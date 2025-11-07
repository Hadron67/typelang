import { ExpressionKind, BuiltinSymbols, Expression, SymbolRegistry, inputForm, se, Symbol } from "./analyse";
import { asSourceRange, Ast, AstBlock, AstFnType, AstFnTypeArgList, AstIdentifier, AstKind, AstLet, AstModuelDecl, AstModule, FileId, parse, SourceRange, sourceRangeBetween, SourceRangeMessage } from "./parser";
import { assert, Either, Mutable, panic } from "./util";

export const enum HIRKind {
    EXPR,
    LAMBDA,
    CALL,
    FN_TYPE,
    SYMBOL,
    SYMBOL_TYPE,
    SYMBOL_ASSIGN,
    SYMBOL_DOWNVALUE,
}

export type HIRReg = number & { __marker: HIRReg };

export type HIRData =
    | HIRExpression
    | HIRCall
    | HIRFnType
    | HIRLambda
    | HIRSymbol
    | HIRSymbolType
    | HIRSymbolAssignment
    | HIRSymbolDownValue
;

export interface DownValue {
    readonly lhs: HIRReg;
    readonly rhs: HIRReg;
    readonly patterns: Set<HIRReg>;
}

export interface HIRExpression {
    readonly kind: HIRKind.EXPR;
    readonly expr: Expression;
}

export interface HIRCall {
    readonly kind: HIRKind.CALL;
    readonly fn: HIRReg;
    readonly arg: HIRReg;
    readonly color: number;
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
}

export interface HIRRule {
    readonly lhs: HIRReg;
    readonly rhs: HIRReg;
    readonly patterns: Set<HIRReg>;
}

export const enum SymbolFlags {
    HAS_TYPE = 1,
    HAS_ASSIGNMENT = 2,
    HAS_DOWN_VALUE = 4,
    IS_TEMP = 8,
}

export interface HIRSymbol {
    readonly kind: HIRKind.SYMBOL;
    readonly name?: string;
    readonly parent: HIRReg | null;
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

export interface HIRSymbolDownValue {
    readonly kind: HIRKind.SYMBOL_DOWNVALUE;
    readonly symbol: HIRReg;
    readonly rule: HIRRule;
}

export interface HIRRegData {
    readonly loc?: SourceRange;
    readonly value: HIRData;
    resolvedValue?: Expression;
}

export class HIRHost {
    readonly regs: HIRRegData[] = [];
    emit(value: HIRData, loc: SourceRange | undefined) {
        const ret = this.regs.length as HIRReg;
        this.regs.push({value, loc});
        return ret;
    }
    dump(registry: SymbolRegistry) {
        const ret: string[] = [];
        for (let i = 0, a = this.regs; i < a.length; i++) {
            ret.push(`$${i} = ${dumpHIR(registry, a[i].value)}`);
        }
        return ret;
    }
}

export function dumpHIR(registry: SymbolRegistry, data: HIRData): string {
    switch (data.kind) {
        case HIRKind.CALL: return data.color === 0 ? `$${data.fn}($${data.arg})` : `$${data.fn}[$${data.arg}]`;
        case HIRKind.FN_TYPE: {
            if (data.color === 0) {
                if (data.arg === void 0) {
                    return `$${data.inputType} -> $${data.outputType}`;
                } else {
                    return `($${data.arg}: $${data.inputType}) -> $${data.outputType}`;
                }
            } else {
                if (data.arg === void 0) {
                    return `[_: $${data.inputType}] -> $${data.outputType}`;
                } else {
                    return `[$${data.arg}: $${data.inputType}] -> $${data.outputType}`;
                }
            }
        }
        case HIRKind.LAMBDA: {
            return (data.arg !== void 0 ? `\\$${data.arg} ` : '\\_ ') + `$${data.body}`;
        }
        case HIRKind.EXPR: return inputForm(registry, data.expr);
        case HIRKind.SYMBOL: return `symbol ${data.name ?? '<no name>'}${data.parent === null ? '' : `, parent = $${data.parent}`}`;
        case HIRKind.SYMBOL_TYPE: return `$${data.symbol}: $${data.type}`;
        case HIRKind.SYMBOL_ASSIGN: return `$${data.symbol} === $${data.value}`;
        case HIRKind.SYMBOL_DOWNVALUE: return `$${data.rule.lhs} === $${data.rule.rhs}`;
        default: panic();
    }
}

const CCODE_I = 'i'.charCodeAt(0);

type PatternResolver = (name: AstIdentifier | undefined, isPattern: boolean) => HIRReg | null;

export function irgen(inputAst: Ast[], initialScope: Map<string, Expression>, builtins: BuiltinSymbols): Either<HIRHost, SourceRangeMessage[]> {
    const scopes: Map<string, HIRReg>[] = [];
    const diagnostics: SourceRangeMessage[] = [];
    const selfStack: HIRReg[] = [];
    const NULL = 0 as HIRReg;
    const hir = new HIRHost();

    {
        const firstScope = new Map<string, HIRReg>();
        initialScope.forEach((v, k) => firstScope.set(k, hir.emit({kind: HIRKind.EXPR, expr: v}, void 0)));
        scopes.push(firstScope);
        const ret = hir.emit({kind: HIRKind.SYMBOL, parent: null, flags: 0}, void 0);
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

    function genExpression(expr: Ast, patternResolver: PatternResolver | undefined): HIRReg {
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
                    return hir.emit({kind: HIRKind.SYMBOL, parent: null, flags: SymbolFlags.IS_TEMP | SymbolFlags.HAS_ASSIGNMENT | SymbolFlags.HAS_TYPE}, loc);
                }
                if (name === 'Self') {
                    assert(selfStack.length > 0);
                    return selfStack[selfStack.length - 1];
                }
                if (patternResolver !== void 0) {
                    const p = patternResolver(expr, false);
                    if (p !== null) {
                        return p;
                    }
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
                return hir.emit({kind: HIRKind.EXPR, expr: {kind: ExpressionKind.NUMBER, isLevel: false, value: expr.value, loc}}, loc);
            }
            case AstKind.STRING: {
                return hir.emit({kind: HIRKind.EXPR, expr: {kind: ExpressionKind.STRING, value: expr.value, loc}}, loc);
            }
            case AstKind.PATTERN: {
                if (patternResolver === void 0) {
                    diagnostics.push({...asSourceRange(expr), msg: 'pattern not allow here'});
                    break;
                }
                const ret = patternResolver(expr.name, true);
                if (ret === null) {
                    break;
                }
                return ret;
            }
            case AstKind.FN_TYPE: return genFnType(expr, patternResolver);
            case AstKind.LAMBDA: {
                let arg: HIRReg | undefined = void 0;
                if (expr.arg.name !== '_') {
                    const arg = hir.emit({kind: HIRKind.SYMBOL, parent: null, flags: 0}, expr.arg);
                    const newScope = new Map<string, HIRReg>();
                    newScope.set(expr.arg.name, arg);
                    scopes.push(newScope);
                }
                const ret = hir.emit({kind: HIRKind.LAMBDA, arg, body: genExpression(expr.body, patternResolver)}, loc);
                if (arg !== void 0) {
                    scopes.pop();
                }
                return ret;
            }
            // case AstKind.BLOCK: return genBlock(expr);
            case AstKind.CALL: {
                const fn = genExpression(expr.fn, patternResolver) ?? panic();
                let arg: HIRReg | undefined = void 0;
                if (expr.arg !== void 0) {
                    arg = genExpression(expr.arg, patternResolver) ?? panic();
                } else {
                    arg = hir.emit({kind: HIRKind.EXPR, expr: se(builtins.unit)}, void 0);
                }
                return hir.emit({kind: HIRKind.CALL, fn, arg, color: expr.color}, loc);
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
        const ret = hir.emit({kind: HIRKind.SYMBOL, parent: null, flags: SymbolFlags.IS_TEMP | SymbolFlags.HAS_ASSIGNMENT}, void 0);
        if (type !== void 0) {
            hir.emit({kind: HIRKind.SYMBOL_TYPE, symbol: ret, type}, void 0);
        }
        return ret;
    }

    function genFnType(expr: AstFnType, patternResolver: PatternResolver | undefined): HIRReg {
        const args = expr.inputType;
        if (args.isArgList) {
            const color = args.color;
            const fns: HIRPartialFnType[] = [];
            const scope = new Map<string, HIRReg>();
            scopes.push(scope);
            for (const [arg, argType] of args.args) {
                const inputType = argType !== void 0 ? genExpression(argType, patternResolver) : emitUnknown(void 0);
                const argVar = hir.emit({kind: HIRKind.SYMBOL, flags: SymbolFlags.HAS_TYPE, parent: null}, arg);
                hir.emit({kind: HIRKind.SYMBOL_TYPE, symbol: argVar, type: inputType}, void 0);
                scope.set(arg.name, argVar);
                fns.push({color, inputType, arg: argVar, loc: argType !== void 0 ? sourceRangeBetween(arg, argType) : asSourceRange(arg)});
            }
            const outputType = genExpression(expr.outputType, patternResolver);
            scopes.pop();
            return partialFnTypesToFnType(fns, outputType);
        } else {
            return hir.emit({
                kind: HIRKind.FN_TYPE,
                inputType: genExpression(args.type, patternResolver),
                outputType: genExpression(expr.outputType, patternResolver),
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
            if (name !== 'Self' && name !== null && !scope.has(name)) {
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
                            const symbol = lhs.name === 'Self' ? self : scope.get(lhs.name) ?? panic();
                            const entry = hir.regs[symbol].value;
                            assert(entry.kind === HIRKind.SYMBOL);
                            if (type !== void 0) {
                                hir.emit({kind: HIRKind.SYMBOL_TYPE, symbol, type: genExpression(type, void 0)}, decl);
                                entry.flags |= SymbolFlags.HAS_TYPE;
                            }
                            if (rhs !== void 0) {
                                hir.emit({kind: HIRKind.SYMBOL_ASSIGN, symbol, value: genExpression(rhs, void 0)}, decl);
                                entry.flags |= SymbolFlags.HAS_ASSIGNMENT;
                            }
                            break;
                        }
                        case AstKind.CALL: {
                            const fn = getCallFn(lhs);
                            if (fn.kind === AstKind.IDENTIFIER && rhs !== void 0) {
                                const symbol = scope.get(fn.name) ?? panic();
                                const entry = hir.regs[symbol].value;
                                assert(entry.kind === HIRKind.SYMBOL);
                                const rule = genRule(lhs, rhs);
                                hir.emit({kind: HIRKind.SYMBOL_DOWNVALUE, symbol, rule}, decl);
                                break;
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
        const patterns = new Set<HIRReg>();
        const l = genExpression(lhs, (name, isPattern) => {
            if (isPattern) {
                if (name === void 0 || !patternsByName.has(name.name)) {
                    const p = hir.emit({kind: HIRKind.SYMBOL, parent: null, flags: 0}, name);
                    patterns.add(p);
                    if (name !== void 0) {
                        patternsByName.set(name.name, p);
                    }
                    return p;
                }
            }
            return patternsByName.get(name?.name ?? panic()) ?? null;
        });
        const r = genExpression(rhs, (name, isPattern) => {
            if (!isPattern && name !== void 0) {
                return patternsByName.get(name.name) ?? null;
            }
            return null;
        });
        return {lhs: l, rhs: r, patterns};
    }

    function getCallFn(expr: Ast) {
        while (expr.kind === AstKind.CALL) {
            expr = expr.fn;
        }
        return expr;
    }
}

export function parseAndIrgen(builtins: BuiltinSymbols, initialScope: Map<string, Expression>, input: string, file: FileId): Either<HIRHost, SourceRangeMessage[]> {
    const parseResult = parse(input, file);
    if (!parseResult.isLeft) {
        return {isLeft: false, value: parseResult.value};
    }
    return irgen(parseResult.value, initialScope, builtins);
}
