import { ExpressionKind, BuiltinSymbols, Expression, SymbolFlags, ExpressionStringifier, SymbolExpression } from "./analyse";
import { asSourceRange, Ast, AstCall, AstFnType, AstIdentifier, AstKind, FileId, parse, SourceRange, sourceRangeBetween, SourceRangeMessage } from "./parser";
import { assert, Either, panic } from "./util";

export const enum HIRKind {
    ROOT,
    EXPR,
    NUMBER,
    LAMBDA,
    CALL,
    FN_TYPE,
    MEMBER_ACCESS,
    SYMBOL,
    SYMBOL_TYPE,
    SYMBOL_ASSIGN,
    SYMBOL_RULE,
    UNKNOWN,
    VARIABLE,
}

export type HIRReg = number & { __marker: HIRReg };

export type HIRData =
    | HIRRoot
    | HIRExpression
    | HIRCall
    | HIRNumber
    | HIRFnType
    | HIRLambda
    | HIRMemberAccess
    | HIRSymbol
    | HIRSymbolType
    | HIRSymbolAssignment
    | HIRSymbolRule
    | HIRUnknown
    | HIRVariable
;

export interface DownValue {
    readonly lhs: HIRReg;
    readonly rhs: HIRReg;
    readonly patterns: Set<HIRReg>;
}

export interface HIRRoot {
    readonly kind: HIRKind.ROOT;
}

export interface HIRExpression {
    readonly kind: HIRKind.EXPR;
    readonly expr: Expression;
    readonly type?: Expression;
}

export interface HIRNumber {
    readonly kind: HIRKind.NUMBER;
    readonly value: number;
}

export interface HIRCall {
    readonly kind: HIRKind.CALL;
    readonly fn: HIRReg;
    readonly arg: HIRReg;
    readonly color: number;
    readonly isPattern: boolean;
}

export interface HIRPartialFnType {
    readonly inputType: HIRReg;
    readonly arg: HIRReg;
    readonly color: number;
    readonly loc?: SourceRange;
}

export interface HIRFnType {
    readonly kind: HIRKind.FN_TYPE;
    readonly inputType: HIRReg;
    readonly arg?: HIRReg;
    readonly outputType: HIRReg;
    readonly color: number;
}

export interface HIRLambda {
    readonly kind: HIRKind.LAMBDA;
    readonly arg?: HIRReg;
    readonly body: HIRReg;
    readonly color: number;
    readonly argType?: HIRReg;
}

export interface HIRMemberAccess {
    readonly kind: HIRKind.MEMBER_ACCESS;
    readonly lhs: HIRReg;
    readonly name: string;
}

export interface HIRRule {
    readonly lhs: HIRReg;
    readonly rhs: HIRReg;
}

export interface HIRSymbol {
    readonly kind: HIRKind.SYMBOL;
    readonly name?: string;
    readonly parent?: HIRReg;
    flags: number;
}

export interface HIRSymbolType {
    readonly kind: HIRKind.SYMBOL_TYPE;
    readonly symbol: HIRReg;
    readonly type: HIRReg;
}

export interface HIRSymbolAssignment {
    readonly kind: HIRKind.SYMBOL_ASSIGN;
    readonly symbol: HIRReg;
    readonly value: HIRReg;
}

export interface HIRSymbolRule {
    readonly kind: HIRKind.SYMBOL_RULE;
    readonly symbol: HIRReg;
    readonly isUpValue: boolean;
    readonly rule: HIRRule;
}

export interface HIRUnknown {
    readonly kind: HIRKind.UNKNOWN;
    readonly type?: HIRReg;
}

export interface HIRVariable {
    readonly kind: HIRKind.VARIABLE;
    readonly name?: string;
    readonly type?: HIRReg;
}

export interface HIRRegData {
    readonly loc?: SourceRange;
    readonly value: HIRData;
}

export class HIRHost {
    readonly regs: HIRRegData[] = [];
    emit(value: HIRData, loc: SourceRange | undefined) {
        const ret = this.regs.length as HIRReg;
        this.regs.push({value, loc});
        return ret;
    }
    dump(registry: ExpressionStringifier) {
        const ret: string[] = [];
        for (let i = 0, a = this.regs; i < a.length; i++) {
            ret.push(`%${i} = ${dumpHIR(registry, a[i].value)}`);
        }
        return ret;
    }
}

export function dumpHIR(registry: ExpressionStringifier, data: HIRData): string {
    switch (data.kind) {
        case HIRKind.CALL: return data.color === 0 ? `%${data.fn}($${data.arg})` : `%${data.fn}[$${data.arg}]`;
        case HIRKind.FN_TYPE: {
            if (data.color === 0) {
                if (data.arg === void 0) {
                    return `%${data.inputType} -> %${data.outputType}`;
                } else {
                    return `(%${data.arg}: %${data.inputType}) -> %${data.outputType}`;
                }
            } else {
                if (data.arg === void 0) {
                    return `[_: %${data.inputType}] -> %${data.outputType}`;
                } else {
                    return `[%${data.arg}: %${data.inputType}] -> %${data.outputType}`;
                }
            }
        }
        case HIRKind.LAMBDA: {
            return (data.arg !== void 0 ? `\\%${data.arg} ` : '\\_ ') + `%${data.body}`;
        }
        case HIRKind.EXPR: return registry.stringify(data.expr);
        case HIRKind.NUMBER: return data.value.toString();
        case HIRKind.MEMBER_ACCESS: return `%${data.lhs}.${data.name}`;
        case HIRKind.UNKNOWN: return 'unknown' + (data.type !== void 0 ? ` %${data.type}` : '');
        case HIRKind.VARIABLE: return 'variable' + (data.type !== void 0 ? ` %${data.type}` : '');
        case HIRKind.ROOT: return 'root';
        case HIRKind.SYMBOL: return `symbol ${data.name ?? '<no name>'}${data.parent === null ? '' : `, parent = %${data.parent}`}`;
        case HIRKind.SYMBOL_TYPE: return `%${data.symbol}: %${data.type}`;
        case HIRKind.SYMBOL_ASSIGN: return `%${data.symbol} === %${data.value}`;
        case HIRKind.SYMBOL_RULE: return `%${data.rule.lhs} === %${data.rule.rhs}`;
        default: panic();
    }
}

function getCallFn(expr: Ast) {
    while (expr.kind === AstKind.CALL) {
        expr = expr.fn;
    }
    return expr;
}

function collectAstFnArgs(expr: AstCall): [Ast, Ast[]] {
    const args: Ast[] = [];
    let expr0: Ast = expr;
    while (expr0.kind === AstKind.CALL) {
        if (expr0.arg !== void 0) {
            args.unshift(expr0.arg);
        }
        expr0 = expr0.fn;
    }
    return [expr0, args];
}

function findRuleTag(expr: AstCall, scope: Map<string, HIRReg>): [HIRReg, boolean] | null {
    const [fn, args] = collectAstFnArgs(expr);
    if (fn.kind === AstKind.IDENTIFIER && scope.has(fn.name)) {
        return [scope.get(fn.name)!, false];
    }
    for (const arg of args) {
        if (arg.kind === AstKind.IDENTIFIER && scope.has(arg.name)) {
            return [scope.get(arg.name)!, true];
        }
        if (arg.kind === AstKind.CALL) {
            const fn2 = getCallFn(arg);
            if (fn2.kind === AstKind.IDENTIFIER && scope.has(fn2.name)) {
                return [scope.get(fn2.name)!, true];
            }
        }
    }
    return null;
}

const CCODE_I = 'i'.charCodeAt(0);

export function irgen(inputAst: Ast[], initialScope: Map<string, SymbolExpression>, builtins: BuiltinSymbols): Either<HIRHost, SourceRangeMessage[]> {
    const scopes: Map<string, HIRReg>[] = [];
    const diagnostics: SourceRangeMessage[] = [];
    const selfStack: HIRReg[] = [];
    const NULL = 0 as HIRReg;
    const hir = new HIRHost();

    {
        const firstScope = new Map<string, HIRReg>();
        initialScope.forEach((v, k) => firstScope.set(k, hir.emit({kind: HIRKind.EXPR, expr: v, type: v.type}, void 0)));
        scopes.push(firstScope);
        const ret = hir.emit({kind: HIRKind.ROOT}, void 0);
        genModuleBody(ret, inputAst);
        if (diagnostics.length > 0) {
            return {isLeft: false, value: diagnostics};
        } else {
            return {isLeft: true, value: hir};
        }
    }

    // function genBlock(expr: AstBlock): RegisterHandle {
    //     const ret = registry.emitValue(BLOCK_EXPRESSION, asSourceRange(expr));
    //     const scope = new Map<string, RegisterHandle>();
    //     scopes.push(scope);
    //     for (const e of expr.body) {
    //         if (e.kind === AstKind.LET) {
    //             const old = scope.get(e.name.name);
    //             if (old !== void 0) {
    //                 diagnostics.push({...asSourceRange(e.name), msg: 'duplicated block variable'});
    //             }
    //             const ret = registry.emit({value: HIR_NULL, loc: asSourceRange(e.name)});
    //             const entry = registry.regs[ret];
    //             if (e.type !== void 0) {
    //                 entry.type = genExpression(e.type) ?? panic();
    //             }
    //             if (e.initializer !== void 0) {
    //                 if (e.isVar) {
    //                     const value = genExpression(e.initializer) ?? panic();
    //                     registry.emitValue({kind: HIRKind.ASSIGN, lhs: ret, rhs: value}, asSourceRange(e));
    //                 } else {
    //                     entry.value = {kind: HIRKind.HANDLE, handle: genExpression(e.initializer)};
    //                 }
    //             }
    //         } else {
    //             genExpression(e);
    //         }
    //     }
    //     scopes.pop();
    //     registry.emitValue(END_EXPRESSION, void 0);
    //     return ret;
    // }

    function genExpression(expr: Ast): HIRReg {
        const loc = asSourceRange(expr);
        switch (expr.kind) {
            case AstKind.IDENTIFIER: {
                const name = expr.name;
                for (let i = 0; i < scopes.length; i++) {
                    const ret = scopes[scopes.length - 1 - i].get(name);
                    if (ret !== void 0) {
                        return ret;
                    }
                }
                if (name === '_') {
                    return emitUnknown(void 0);
                }
                if (name === 'Self') {
                    assert(selfStack.length > 0);
                    return selfStack[selfStack.length - 1];
                }
                // if (/^[ui][0-9]+$/g.test(name)) {
                //     const signed = name.charCodeAt(0) === CCODE_I;
                //     const bits = Number(name.slice(1));
                //     return registry.emitCall(registry.intType, [registry.emitBool(signed), registry.emitNumber(bits, loc)], 0, loc);
                // }
                diagnostics.push({...asSourceRange(expr), msg: 'undefined identifier'});
                return NULL;
            }
            case AstKind.NUMBER: {
                return hir.emit({kind: HIRKind.NUMBER, value: expr.value}, loc);
            }
            case AstKind.STRING: {
                return hir.emit({kind: HIRKind.EXPR, expr: {kind: ExpressionKind.STRING, value: expr.value, loc}}, loc);
            }
            case AstKind.FN_TYPE: return genFnType(expr);
            case AstKind.LAMBDA: {
                let arg: HIRReg | undefined = void 0;
                if (expr.arg.name !== '_') {
                    arg = hir.emit({kind: HIRKind.VARIABLE, name: expr.arg.name}, expr.arg);
                    const newScope = new Map<string, HIRReg>();
                    newScope.set(expr.arg.name, arg);
                    scopes.push(newScope);
                }
                const ret = hir.emit({kind: HIRKind.LAMBDA, arg, body: genExpression(expr.body), color: expr.color}, loc);
                if (arg !== void 0) {
                    scopes.pop();
                }
                return ret;
            }
            // case AstKind.BLOCK: return genBlock(expr);
            case AstKind.CALL: {
                const fn = genExpression(expr.fn);
                let arg: HIRReg | undefined = void 0;
                if (expr.arg !== void 0) {
                    arg = genExpression(expr.arg);
                } else {
                    arg = hir.emit({kind: HIRKind.EXPR, expr: builtins.unit}, void 0);
                }
                return hir.emit({kind: HIRKind.CALL, fn, arg, color: expr.color, isPattern: false}, loc);
            }
            case AstKind.MEMBER_ACCESS: {
                const lhs = genExpression(expr.lhs);
                return hir.emit({kind: HIRKind.MEMBER_ACCESS, lhs, name: expr.member.name}, expr);
            }
            default: panic();
        }
        return NULL;
    }

    function partialFnTypesToFnType(fns: HIRPartialFnType[], outputType: HIRReg) {
        for (let i = 0; i < fns.length; i++) {
            const fn = fns[fns.length - 1 - i];
            outputType = hir.emit({
                kind: HIRKind.FN_TYPE,
                arg: fn.arg,
                color: fn.color,
                // loc: outputType.loc !== void 0 && fn.loc !== void 0 ? sourceRangeBetween(outputType.loc, fn.loc) : void 0,
                inputType: fn.inputType,
                outputType,
            }, void 0);
        }
        return outputType;
    }

    function emitUnknown(type: HIRReg | undefined) {
        return hir.emit({kind: HIRKind.UNKNOWN, type}, void 0);
    }

    function genFnType(expr: AstFnType): HIRReg {
        const args = expr.inputType;
        if (args.isArgList) {
            const color = args.color;
            const fns: HIRPartialFnType[] = [];
            const scope = new Map<string, HIRReg>();
            scopes.push(scope);
            for (const [arg, argType] of args.args) {
                const inputType = argType !== void 0 ? genExpression(argType) : emitUnknown(void 0);
                const argVar = hir.emit({kind: HIRKind.VARIABLE, name: arg.name, type: inputType}, arg);
                scope.set(arg.name, argVar);
                fns.push({color, inputType, arg: argVar, loc: argType !== void 0 ? sourceRangeBetween(arg, argType) : asSourceRange(arg)});
            }
            const outputType = genExpression(expr.outputType);
            scopes.pop();
            return partialFnTypesToFnType(fns, outputType);
        } else {
            return hir.emit({
                kind: HIRKind.FN_TYPE,
                inputType: genExpression(args.type),
                outputType: genExpression(expr.outputType),
                color: 0,
            }, expr);
        }
    }

    function getDeclName(decl: Ast) {
        switch (decl.kind) {
            case AstKind.MODULE_DECL: {
                const lhs = decl.lhs;
                if (lhs.kind === AstKind.IDENTIFIER) {
                    return lhs.name;
                } else return null;
            }
            case AstKind.MODULE: return decl.name.name;
            default: return null;
        }
    }

    function genModuleBody(self: HIRReg, decls: Ast[]) {
        selfStack.push(self);
        const scope = new Map<string, HIRReg>();
        for (const decl of decls) {
            const name = getDeclName(decl);
            if (name !== 'Self' && name !== null && name !== '_' && !scope.has(name)) {
                scope.set(name, hir.emit({kind: HIRKind.SYMBOL, name, parent: self, flags: 0}, decl));
            }
        }
        scopes.push(scope);
        for (const decl of decls) {
            switch (decl.kind) {
                case AstKind.MODULE_DECL: {
                    const {lhs, rhs, type} = decl;
                    switch (lhs.kind) {
                        case AstKind.IDENTIFIER: {
                            let symbol: HIRReg;
                            if (lhs.name === 'Self') {
                                symbol = self;
                            } else if (lhs.name === '_') {
                                symbol = hir.emit({kind: HIRKind.SYMBOL, name: '_', parent: self, flags: 0}, decl);
                            } else {
                                symbol = scope.get(lhs.name) ?? panic();
                            }
                            const entry = hir.regs[symbol].value;
                            assert(entry.kind === HIRKind.SYMBOL);
                            if (type !== void 0) {
                                hir.emit({kind: HIRKind.SYMBOL_TYPE, symbol, type: genExpression(type)}, decl);
                                entry.flags |= SymbolFlags.ALLOW_DEF_TYPE;
                            }
                            if (rhs !== void 0) {
                                hir.emit({kind: HIRKind.SYMBOL_ASSIGN, symbol, value: genExpression(rhs)}, decl);
                                entry.flags |= SymbolFlags.ALLOW_ASSIGNMENT;
                            }
                            break;
                        }
                        case AstKind.CALL: {
                            if (rhs !== void 0) {
                                const tagInfo = findRuleTag(lhs, scope);
                                if (tagInfo !== null) {
                                    const [tag, isUpValue] = tagInfo;
                                    const entry = hir.regs[tag].value;
                                    assert(entry.kind === HIRKind.SYMBOL);
                                    const rule = genRule(lhs, rhs);
                                    hir.emit({kind: HIRKind.SYMBOL_RULE, symbol: tag, rule, isUpValue}, decl);
                                    entry.flags |= isUpValue ? SymbolFlags.ALLOW_UP_VALUE : SymbolFlags.ALLOW_DOWN_VALUE;
                                    break;
                                }
                            }
                            diagnostics.push({...asSourceRange(decl), msg: 'invalid declaration'});
                            break;
                        }
                        default: diagnostics.push({...asSourceRange(decl), msg: 'invalid declaration'}); break;
                    }
                    break;
                }
                case AstKind.MODULE: {
                    const name = decl.name.name;
                    if (name === 'Self') {
                        diagnostics.push({...asSourceRange(decl), msg: 'cannot use Self as module name'});
                    } else {
                        genModuleBody(scope.get(name) ?? panic(), decl.decls);
                    }
                    break;
                }
                default: diagnostics.push({...asSourceRange(decl), msg: 'invalid declaration'}); break;
            }
        }
        scopes.pop();
        selfStack.pop();
    }

    function genRule(lhs: Ast, rhs: Ast): HIRRule {
        const patternsByName = new Map<string, HIRReg>();
        const l = genPatternLhs(lhs, patternsByName);
        scopes.push(patternsByName);
        const r = genExpression(rhs);
        scopes.pop();
        return {lhs: l, rhs: r};
    }

    function genPatternLhs(expr: Ast, patterns: Map<string, HIRReg>): HIRReg {
        switch (expr.kind) {
            case AstKind.CALL: {
                const fn = genPatternLhs(expr.fn, patterns);
                const arg = expr.arg !== void 0 ? genPatternLhs(expr.arg, patterns) : hir.emit({kind: HIRKind.EXPR, expr: builtins.unit}, void 0);
                return hir.emit({kind: HIRKind.CALL, isPattern: true, fn, arg, color: expr.color}, expr);
            }
            case AstKind.PATTERN: {
                const name = expr.name;
                const s = name !== void 0 ? patterns.get(name.name) : void 0;
                if (s !== void 0) {
                    return s;
                }
                const ns = hir.emit({kind: HIRKind.VARIABLE, name: name?.name}, expr);
                if (name !== void 0) {
                    patterns.set(name.name, ns);
                }
                return ns;
            }
            default: return genExpression(expr);
        }
    }
}

export function parseAndIrgen(builtins: BuiltinSymbols, initialScope: Map<string, SymbolExpression>, input: string, file: FileId): Either<HIRHost, SourceRangeMessage[]> {
    const parseResult = parse(input, file);
    if (!parseResult.isLeft) {
        return {isLeft: false, value: parseResult.value};
    }
    return irgen(parseResult.value, initialScope, builtins);
}

export function visitHIR(hir: HIRData, cb: (reg: HIRReg) => void) {
    switch (hir.kind) {
        case HIRKind.CALL:
            cb(hir.fn);
            cb(hir.arg);
            break;
        case HIRKind.EXPR: break;
        case HIRKind.FN_TYPE:
            cb(hir.inputType);
            if (hir.arg !== void 0) {
                cb(hir.arg);
            }
            cb(hir.outputType);
            break;
        case HIRKind.LAMBDA:
            if (hir.arg !== void 0) {
                cb(hir.arg);
            }
            cb(hir.body);
            break;
        case HIRKind.MEMBER_ACCESS:
            cb(hir.lhs);
            break;
        case HIRKind.SYMBOL_ASSIGN:
            cb(hir.symbol);
            cb(hir.value);
            break;
        case HIRKind.SYMBOL_RULE:
            cb(hir.symbol);
            cb(hir.rule.lhs);
            cb(hir.rule.rhs);
            break;
        case HIRKind.SYMBOL_TYPE:
            cb(hir.symbol);
            cb(hir.type);
            break;
        default:;
    }
}

export function generateHIRDependencies(hir: HIRHost) {
    const ret: HIRReg[][] = [];
    for (const data of hir.regs) {
        const deps: HIRReg[] = [];
        visitHIR(data.value, reg => deps.push(reg));
        ret.push(deps);
    }
    return ret;
}
