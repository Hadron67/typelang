import { HIRCall, HIRFnType, HIRHost, HIRKind, HIRReg, HIRRegData, SymbolFlags } from "./irgen";
import { StructVariant, SourceRange, asSourceRange, SourceRangeMessage } from "./parser";
import { assert, IndexedMap, Mutable, panic, popReversed, pushReversed } from "./util";

export const enum ExpressionKind {
    SYMBOL,
    STRING,
    NUMBER,
    UNIVERSE,
    LAMBDA,
    CALL,
    FN_TYPE,
}

export type Symbol = number & { __marker: Symbol };

export type Expression =
    | SymbolExpression
    | StringExpression
    | NumberExpression
    | LambdaExpression
    | FnTypeExpression
    | CallExpression
    | UniverseExpression
;

export interface SymbolExpression {
    readonly kind: ExpressionKind.SYMBOL;
    readonly symbol: Symbol;
    readonly loc?: SourceRange;
}

export interface StringExpression {
    readonly kind: ExpressionKind.STRING;
    readonly value: string;
    readonly loc?: SourceRange;
}

export interface NumberExpression {
    readonly kind: ExpressionKind.NUMBER;
    readonly value: number;
    readonly isLevel: boolean;
    readonly loc?: SourceRange;
}

export interface LambdaExpression {
    readonly kind: ExpressionKind.LAMBDA;
    readonly arg?: SymbolExpression;
    readonly body: Expression;
    readonly type: Expression;
    readonly loc?: SourceRange;
}

export interface FnTypeExpression {
    readonly kind: ExpressionKind.FN_TYPE;
    readonly arg?: SymbolExpression;
    readonly inputType: Expression;
    readonly outputType: Expression;
    readonly color: number;
    readonly typeLevel: Expression;
    readonly loc?: SourceRange;
}

export interface CallExpression {
    readonly kind: ExpressionKind.CALL;
    readonly fn: Expression;
    readonly arg: Expression;
    readonly type: Expression;
    readonly loc?: SourceRange;
}

export interface UniverseExpression {
    readonly kind: ExpressionKind.UNIVERSE;
    readonly level: Expression;
    readonly loc?: SourceRange;
}

export interface SymbolData {
    readonly name?: string;
    readonly loc?: SourceRange;
    readonly parent: Symbol | null;
    readonly evaluator?: (args: Expression[]) => Expression | null;
    readonly flags: number;
    subSymbols?: Map<string, Symbol>;
    type?: Expression;
    value?: Expression;
}

export const enum TypeCheckDiagnosticKind {
    UNEQUAL,
    UNINFERRED,
}

export type TypeCheckDiagnostic = TypeCheckDiagnosticUnequal | TypeCheckDiagnosticUninferred;

export interface TypeCheckDiagnosticUnequal {
    readonly kind: TypeCheckDiagnosticKind.UNEQUAL;
    readonly expr1: Expression;
    readonly expr2: Expression;
}

export interface TypeCheckDiagnosticUninferred {
    readonly kind: TypeCheckDiagnosticKind.UNINFERRED;
    readonly symbol: Symbol;
}

export function renderTypeCheckDiagnostic(d: TypeCheckDiagnostic, reg: SymbolRegistry) {
    switch (d.kind) {
        case TypeCheckDiagnosticKind.UNEQUAL: return [`unequal expressions ${inputForm(reg, d.expr1)} and ${inputForm(reg, d.expr2)}`];
        case TypeCheckDiagnosticKind.UNINFERRED: return [`uninferred symbol ${reg.getSymbolDisplayName(d.symbol)}`];
    }
}

export function se(symbol: Symbol): SymbolExpression {
    return {kind: ExpressionKind.SYMBOL, symbol};
}

export class BuiltinSymbols {
    readonly builtin: Symbol;
    readonly root: Symbol;
    readonly type: Symbol;
    readonly level0: NumberExpression = {kind: ExpressionKind.NUMBER, isLevel: true, value: 0};
    readonly u0: UniverseExpression = {kind: ExpressionKind.UNIVERSE, level: {kind: ExpressionKind.NUMBER, value: 0, isLevel: true}};
    readonly levelType: Symbol;
    readonly levelSucc: Symbol;
    readonly levelMax: Symbol;
    readonly levelMaxType: FnTypeExpression;

    readonly untyped: Symbol;
    readonly numberType: Symbol;
    readonly stringType: Symbol;
    readonly unitType: Symbol;
    readonly unit: Symbol;
    constructor(reg: SymbolRegistry) {
        this.builtin = reg.emitSymbol({name: 'builtin', parent: null, flags: 0});
        this.root = reg.emitSymbol({name: 'root', parent: null, flags: 0});
        this.type = reg.emitSymbol({name: 'Type', parent: this.builtin, flags: 0});

        const makeType = (name: string): Symbol => {
            return reg.emitSymbol({name, type: this.u0, parent: this.builtin, flags: 0});
        }

        this.levelType = makeType('Level');
        this.levelSucc = reg.emitSymbol({
            name: 'succ',
            type: {kind: ExpressionKind.FN_TYPE, inputType: se(this.levelType), outputType: se(this.levelType), typeLevel: this.level0, color: 0},
            parent: this.builtin,
            flags: 0,
            evaluator(args) {
                const a = args[0];
                if (a.kind === ExpressionKind.NUMBER && a.isLevel) {
                    return {kind: ExpressionKind.NUMBER, isLevel: true, value: a.value + 1};
                }
                return null;
            },
        });
        this.levelMaxType = {
            kind: ExpressionKind.FN_TYPE,
            color: 0,
            inputType: se(this.levelType),
            outputType: {
                kind: ExpressionKind.FN_TYPE,
                color: 0,
                inputType: se(this.levelType),
                outputType: se(this.levelType),
                typeLevel: {kind: ExpressionKind.NUMBER, isLevel: true, value: 0},
            },
            typeLevel: {kind: ExpressionKind.NUMBER, isLevel: true, value: 0},
        };
        this.levelMax = reg.emitSymbol({
            name: 'max',
            type: this.levelMaxType,
            parent: this.builtin,
            flags: 0,
            evaluator(args) {
                const [a1, a2] = args;
                if (a1.kind === ExpressionKind.NUMBER && a1.isLevel && a2.kind === ExpressionKind.NUMBER && a2.isLevel) {
                    return {kind: ExpressionKind.NUMBER, isLevel: true, value: Math.max(a1.value, a2.value)};
                }
                return null;
            },
        });

        this.untyped = makeType('untyped');
        this.numberType = makeType('number');
        this.stringType = makeType('string');
        this.unitType = makeType('void');
        this.unit = makeType('void');
    }
    getInitialScope() {
        const ret = new Map<string, Expression>();
        ret.set('Type', se(this.type));
        return ret;
    }
    makeLevelMax(a1: Expression, a2: Expression): Expression {
        return {
            kind: ExpressionKind.CALL,
            fn: {
                kind: ExpressionKind.CALL,
                fn: se(this.levelMax),
                arg: a1,
                type: this.levelMaxType.outputType,
            },
            arg: a2,
            type: se(this.levelType),
        };
    }
}

export class SymbolRegistry {
    private readonly symbolOffset: number;
    private readonly symbols: SymbolData[] = [];
    constructor(private readonly parent: SymbolRegistry | null) {
        this.symbolOffset = parent === null ? 0 : parent.symbolOffset + parent.symbols.length;
    }
    getSymbolEntry(s: Symbol) {
        let p: SymbolRegistry = this;
        while (s < p.symbolOffset) {
            p = p.parent ?? panic();
        }
        assert(s < p.symbols.length + p.symbolOffset);
        return p.symbols[s - p.symbolOffset];
    }
    getSymbolDisplayName(s: Symbol) {
        if (s >= this.symbolOffset + this.symbols.length) {
            return `!${s}`;
        }
        let entry = this.getSymbolEntry(s);
        const parts: string[] = [entry.name ?? `$${s}`];
        while (entry.parent !== null) {
            const p = entry.parent;
            entry = this.getSymbolEntry(entry.parent);
            parts.unshift(entry.name ?? `$${p}`);
        }
        return parts.join('.');
    }
    isLocalSymbol(symbol: Symbol) {
        return symbol >= this.symbolOffset && symbol < this.symbolOffset + this.symbols.length;
    }
    emitSymbol(data: SymbolData) {
        const ret = this.symbolOffset + this.symbols.length as Symbol;
        this.symbols.push(data);
        if (data.parent !== null && data.name !== void 0) {
            const p = this.getSymbolEntry(data.parent);
            if (p.subSymbols === void 0) {
                p.subSymbols = new Map();
            }
            if (!p.subSymbols.has(data.name)) {
                p.subSymbols.set(data.name, ret);
            }
        }
        return ret;
    }
    forEachLocalSymbol(cb: (s: Symbol, entry: SymbolData) => void) {
        for (let i = 0, a = this.symbols; i < a.length; i++) {
            cb(this.symbolOffset + i as Symbol, a[i]);
        }
    }
    emitUnknown(type: Expression): SymbolExpression {
        const ret = this.emitSymbol({type, parent: null, flags: SymbolFlags.IS_TEMP | SymbolFlags.HAS_ASSIGNMENT | SymbolFlags.HAS_TYPE});
        return se(ret);
    }
    emitUnknownType(builtins: BuiltinSymbols) {
        return this.emitUnknown({kind: ExpressionKind.UNIVERSE, level: this.emitUnknown(se(builtins.levelType))});
    }
    mergeFrom(reg: SymbolRegistry) {
        assert(reg.symbolOffset === this.symbols.length);
        assert(reg.parent === this);
        for (const d of reg.symbols) {
            this.symbols.push(d);
        }
        reg.symbols.length = 0;
    }
    dump() {
        const lines: string[] = [];
        this.forEachLocalSymbol((symbol, entry) => {
            if (entry.type !== void 0) {
                lines.push(this.getSymbolDisplayName(symbol) + ': ' + inputForm(this, entry.type));
            }
            if (entry.value !== void 0) {
                lines.push(this.getSymbolDisplayName(symbol) + ' = ' + inputForm(this, entry.value));
            }
        });
        return lines;
    }
}

export function typeOfExpression(expr: Expression, reg: SymbolRegistry, builtins: BuiltinSymbols | undefined): Expression {
    switch (expr.kind) {
        case ExpressionKind.SYMBOL: {
            const entry = reg.getSymbolEntry(expr.symbol);
            if (entry.type === void 0 && 0 !== (entry.flags & SymbolFlags.HAS_TYPE)) {
                entry.type = reg.emitUnknownType(builtins ?? panic());
            }
            return entry.type ?? se((builtins ?? panic()).untyped);
        }
        case ExpressionKind.CALL:
        case ExpressionKind.LAMBDA: return expr.type;
        case ExpressionKind.FN_TYPE: return {kind: ExpressionKind.UNIVERSE, level: expr.typeLevel};
        case ExpressionKind.NUMBER: return se(expr.isLevel ? (builtins ?? panic()).levelType : (builtins ?? panic()).numberType);
        case ExpressionKind.STRING: return se((builtins ?? panic()).stringType);
        case ExpressionKind.UNIVERSE: return {
            kind: ExpressionKind.UNIVERSE,
            level: makeSucc(expr.level, builtins ?? panic()),
        }
        default: panic();
    }
}

function makeSucc(level: Expression, builtins: BuiltinSymbols): Expression {
    if (level.kind === ExpressionKind.NUMBER) {
        assert(level.isLevel);
        return {kind: ExpressionKind.NUMBER, isLevel: true, value: level.value + 1};
    } else {
        return {kind: ExpressionKind.CALL, fn: se(builtins.levelSucc), arg: level, type: se(builtins.levelType)}
    }
}

export function collectFnArgs(expr: Expression): [Expression, Expression[]] {
    const args: Expression[] = [];
    while (expr.kind === ExpressionKind.CALL) {
        args.unshift(expr.arg);
        expr = expr.fn;
    }
    assert(args.length > 0);
    return [expr, args];
}

export function collectFnTypeColors(expr: Expression) {
    const colors: number[] = [];
    while (expr.kind === ExpressionKind.FN_TYPE) {
        colors.push(expr.color);
        expr = expr.outputType;
    }
    return colors;
}

export function inputForm(registry: SymbolRegistry, expr: Expression) {
    const stack: string[] = [];
    const todo: (Expression | ((stack: string[]) => void))[] = [expr];
    while (todo.length > 0) {
        const t = todo.pop()!;
        if (typeof t === 'function') {
            t(stack);
            continue;
        }
        switch (t.kind) {
            case ExpressionKind.SYMBOL: stack.push(registry.getSymbolDisplayName(t.symbol)); break;
            case ExpressionKind.CALL: {
                const [fn, args] = collectFnArgs(t);
                const colors = collectFnTypeColors(typeOfExpression(fn, registry, void 0));
                const needParenth = fn.kind !== ExpressionKind.SYMBOL;
                const length = args.length;
                todo.push(stack => {
                    const args: string[] = [];
                    popReversed(stack, args, length);
                    let fn = stack.pop()!;
                    if (needParenth) {
                        fn = `(${fn})`;
                    }
                    let currentColor = colors.length > 0 ? colors[0] : 0;
                    let argsStr = currentColor === 0 ? '(' : '[';
                    let first = true;
                    for (let i = 0; i < args.length; i++) {
                        const color = i < colors.length ? colors[i] : 0;
                        if (currentColor !== color) {
                            argsStr += (currentColor === 0 ? ')' : ']') + (color === 0 ? '(' : '[');
                            first = true;
                            currentColor = color;
                        }
                        if (!first) {
                            argsStr += ', ';
                        }
                        first = false;
                        argsStr += args[i];
                    }
                    argsStr += currentColor === 0 ? ')' : ']';
                    stack.push(fn + argsStr);
                });
                pushReversed(todo, args);
                todo.push(fn);
                break;
            }
            case ExpressionKind.FN_TYPE: {
                const color = t.color;
                const arg = t.arg !== void 0 ? registry.getSymbolDisplayName(t.arg.symbol) : void 0;
                const needParenth = t.inputType.kind !== ExpressionKind.SYMBOL && t.inputType.kind !== ExpressionKind.CALL;
                todo.push(stack => {
                    const outputType = stack.pop()!;
                    const inputType = stack.pop()!;
                    if (color === 0) {
                        if (arg !== void 0) {
                            stack.push(`(${arg}: ${inputType}) -> ${outputType}`);
                        } else if (needParenth) {
                            stack.push(`(${inputType}) -> ${outputType}`);
                        } else {
                            stack.push(`${inputType} -> ${outputType}`);
                        }
                    } else {
                        if (arg !== void 0) {
                            stack.push(`[${arg}: ${inputType}] -> ${outputType}`);
                        } else {
                            stack.push(`[_: ${inputType}] -> ${outputType}`);
                        }
                    }
                }, t.outputType, t.inputType);
                break;
            }
            case ExpressionKind.LAMBDA: {
                const arg = t.arg !== void 0 ? registry.getSymbolDisplayName(t.arg.symbol) : void 0;
                todo.push(stack => {
                    stack.push((arg !== void 0 ? '\\' + arg : '\\_') + ' ' + stack.pop()!);
                }, t.body);
                break;
            }
            case ExpressionKind.UNIVERSE:
                todo.push(stack => {
                    stack.push(`Type(${stack.pop()!})`);
                }, t.level);
                break;
            case ExpressionKind.NUMBER: stack.push(t.value.toString()); break;
            case ExpressionKind.STRING: stack.push(`"${t.value}"`); break;
            default: panic();
        }
    }
    assert(stack.length === 1);
    return stack[0];
}

export type MapExpressionAction = (Expression | ((stack: Expression[], todo: MapExpressionAction[]) => void))[];
export function mapExpression(expr: Expression, mapper: (expr: Expression) => Expression | null) {
    const todo: (Expression | ((stack: Expression[]) => Expression))[] = [expr];
    const stack: Expression[] = [];
    while (todo.length > 0) {
        const t = todo.pop()!;
        if (typeof t === 'function') {
            const m = mapper(t(stack));
            if (m === null) {
                return null;
            }
            stack.push(m);
            continue;
        }
        switch (t.kind) {
            case ExpressionKind.NUMBER:
            case ExpressionKind.STRING:
            case ExpressionKind.SYMBOL: {
                const m = mapper(t);
                if (m === null) {
                    return null;
                }
                stack.push(m);
                break;
            }
            case ExpressionKind.CALL: {
                const loc = t.loc;
                todo.push(stack => {
                    const type = stack.pop()!;
                    const arg = stack.pop()!;
                    const fn = stack.pop()!;
                    if (fn !== t.fn || arg !== t.arg || type !== t.arg) {
                        return {kind: ExpressionKind.CALL, fn, arg, type, loc};
                    } else {
                        return t;
                    }
                }, t.type, t.arg, t.fn);
                break;
            }
            case ExpressionKind.FN_TYPE: {
                const {loc, color} = t;
                let arg = t.arg;
                if (arg !== void 0) {
                    const n = mapper(arg);
                    if (n === null) return null;
                    assert(n.kind === ExpressionKind.SYMBOL);
                    arg = n;
                }
                todo.push(stack => {
                    const typeLevel = stack.pop()!;
                    const outputType = stack.pop()!;
                    const inputType = stack.pop()!;
                    if (inputType !== t.inputType || outputType !== t.outputType || typeLevel !== t.typeLevel) {
                        return {kind: ExpressionKind.FN_TYPE, inputType, outputType, arg, color, typeLevel, loc};
                    } else {
                        return t;
                    }
                }, t.typeLevel, t.outputType, t.inputType);
                break;
            }
            case ExpressionKind.LAMBDA: {
                let arg = t.arg;
                if (arg !== void 0) {
                    const n = mapper(arg);
                    if (n === null) return null;
                    assert(n.kind === ExpressionKind.SYMBOL);
                    arg = n;
                }
                todo.push(stack => {
                    const type = stack.pop()!;
                    const body = stack.pop()!;
                    if (body !== t.body || type !== t.type) {
                        return {kind: ExpressionKind.LAMBDA, arg, body, type, loc: t.loc};
                    } else {
                        return t;
                    }
                }, t.type, t.body);
                break;
            }
            case ExpressionKind.UNIVERSE: {
                todo.push(stack => {
                    const level = stack.pop()!;
                    if (level !== t.level) {
                        return {kind: ExpressionKind.UNIVERSE, level, loc: t.loc};
                    } else {
                        return t;
                    }
                }, t.level);
                break;
            }
            default: panic();
        }
    }
    assert(stack.length === 1);
    return stack[0];
}

export function replaceOneSymbol(expr: Expression, s: Symbol, replacement: Expression) {
    return mapExpression(expr, expr => {
        if (expr.kind === ExpressionKind.SYMBOL && expr.symbol === s) {
            return replacement;
        }
        return expr;
    }) ?? panic();
}

export function replaceSymbols(expr: Expression, m: Map<Symbol, Expression>) {
    return mapExpression(expr, expr => {
        if (expr.kind === ExpressionKind.SYMBOL) {
            return m.get(expr.symbol) ?? expr;
        }
        return expr;
    }) ?? panic();
}

function checkFnTypeColor(expr: Expression, color: number) {
    while (expr.kind === ExpressionKind.FN_TYPE && expr.color !== color) {
        expr = expr.outputType;
    }
    return expr.kind === ExpressionKind.FN_TYPE;
}

export interface TypeCheckResult {
    readonly tempRegistry: SymbolRegistry;
    readonly diagnostics: TypeCheckDiagnostic[];
}

export function renderTypeCheckResult(tc: TypeCheckResult) {
    const ret: string[] = [];
    for (const d of tc.diagnostics) {
        ret.push(...renderTypeCheckDiagnostic(d, tc.tempRegistry));
    }
    return ret;
}

export function checkTypes(registry: SymbolRegistry, builtins: BuiltinSymbols, hir: HIRHost): TypeCheckResult | null {
    const hirRegs = hir.regs;
    const tempRegistry = new SymbolRegistry(registry);
    const equalConstraints: [Expression, Expression][] = [];
    const diagnostics: TypeCheckDiagnostic[] = [];

    run();
    return diagnostics.length > 0 ? {tempRegistry, diagnostics} : null;

    function typeOfExpression0(expr: Expression) {
        return typeOfExpression(expr, tempRegistry, builtins);
    }

    function pollHIR(data: HIRRegData): boolean {
        const value = data.value;
        if (data.resolvedValue !== void 0) {
            return false;
        }
        switch (value.kind) {
            case HIRKind.EXPR:
                data.resolvedValue = value.expr;
                return true;
            case HIRKind.CALL: {
                const r = pollCall(value);
                if (r !== null) {
                    data.resolvedValue = r;
                    return true;
                } else {
                    return false;
                }
            }
            case HIRKind.LAMBDA: {
                const body = hirRegs[value.body].resolvedValue;
                if (body === void 0) {
                    return false;
                }
                let arg: SymbolExpression | undefined = void 0;
                if (value.arg !== void 0) {
                    const r = hirRegs[value.arg].resolvedValue;
                    if (r === void 0 || r.kind !== ExpressionKind.SYMBOL) {
                        return false;
                    }
                    arg = r;
                }
                const bodyType = typeOfExpression0(body);
                let inputType: Expression;
                if (value.arg !== void 0) {
                    inputType = tempRegistry.getSymbolEntry((arg ?? panic()).symbol).type ?? se(builtins.untyped);
                } else {
                    inputType = tempRegistry.emitUnknownType(builtins);
                }
                const inputLevel = tempRegistry.emitUnknown(se(builtins.levelType));
                const outputLevel = tempRegistry.emitUnknown(se(builtins.levelType));
                equalConstraints.push(
                    [typeOfExpression0(inputType), {kind: ExpressionKind.UNIVERSE, level: inputLevel}],
                    [typeOfExpression0(bodyType), {kind: ExpressionKind.UNIVERSE, level: outputLevel}],
                );
                data.resolvedValue = {
                    kind: ExpressionKind.LAMBDA,
                    arg,
                    body,
                    type: {
                        kind: ExpressionKind.FN_TYPE,
                        color: 0,
                        inputType,
                        outputType: bodyType,
                        arg,
                        typeLevel: builtins.makeLevelMax(inputLevel, outputLevel),
                    },
                };
                return true;
            }
            case HIRKind.SYMBOL: {
                let parent: Symbol | null = null;
                if (value.parent !== null) {
                    const p = hirRegs[value.parent];
                    if (p.resolvedValue === void 0) {
                        return false;
                    }
                    assert(p.resolvedValue.kind === ExpressionKind.SYMBOL);
                    parent = p.resolvedValue.symbol;
                }
                const entry: Mutable<SymbolData> = {parent, name: value.name, loc: data.loc, flags: value.flags};
                data.resolvedValue = {
                    kind: ExpressionKind.SYMBOL,
                    symbol: tempRegistry.emitSymbol(entry),
                };
                return true;
            }
            case HIRKind.SYMBOL_TYPE: {
                const symbol = hirRegs[value.symbol].resolvedValue;
                const type = hirRegs[value.type].resolvedValue;
                if (symbol === void 0 || type === void 0) {
                    return false;
                }
                assert(symbol.kind === ExpressionKind.SYMBOL);
                setSymbolType(symbol.symbol, type);
                data.resolvedValue = se(builtins.unit);
                return true;
            }
            case HIRKind.SYMBOL_ASSIGN: {
                const symbol = hirRegs[value.symbol].resolvedValue;
                const v = hirRegs[value.value].resolvedValue;
                if (symbol === void 0 || v === void 0) {
                    return false;
                }
                assert(symbol.kind === ExpressionKind.SYMBOL);
                setSymbolValue(symbol.symbol, v);
                data.resolvedValue = se(builtins.unit);
                return true;
            }
            case HIRKind.FN_TYPE: {
                const r = pollFnType(value);
                if (r !== null) {
                    data.resolvedValue = r;
                    return true;
                } else {
                    return false;
                }
            }
            case HIRKind.SYMBOL_DOWNVALUE: panic();
        }
    }

    function pollFnType(value: HIRFnType): Expression | null {
        const inputType = hirRegs[value.inputType].resolvedValue;
        const outputType = hirRegs[value.outputType].resolvedValue;
        if (inputType === void 0 || outputType === void 0) return null;
        let arg: SymbolExpression | undefined = void 0;
        if (value.arg !== void 0) {
            const a = hirRegs[value.arg].resolvedValue;
            if (a === void 0 || a.kind !== ExpressionKind.SYMBOL) return null;
            arg = a;
        }
        const inputLevel = tempRegistry.emitUnknown(se(builtins.levelType));
        const outputLevel = tempRegistry.emitUnknown(se(builtins.levelType));
        equalConstraints.push(
            [typeOfExpression0(inputType), {kind: ExpressionKind.UNIVERSE, level: inputLevel}],
            [typeOfExpression0(outputType), {kind: ExpressionKind.UNIVERSE, level: outputLevel}],
        );
        return {
            kind: ExpressionKind.FN_TYPE,
            color: value.color,
            inputType,
            outputType,
            arg,
            typeLevel: builtins.makeLevelMax(inputLevel, outputLevel),
        };
    }

    function pollCall(value: HIRCall): Expression | null {
        const fn = hirRegs[value.fn].resolvedValue;
        const arg = hirRegs[value.arg].resolvedValue;
        if (fn === void 0 || arg === void 0) {
            return null;
        }
        const argType = typeOfExpression0(arg);

        if (fn.kind === ExpressionKind.SYMBOL && fn.symbol === builtins.type) {
            equalConstraints.push([argType, se(builtins.levelType)]);
            return {kind: ExpressionKind.UNIVERSE, level: arg};
        }

        let fnType = typeOfExpression0(fn);
        if (fnType.kind !== ExpressionKind.FN_TYPE) {
            return null;
        }
        if (!checkFnTypeColor(fnType, value.color)) {
            return null;
        }
        let ret = fn;
        while (fnType.kind === ExpressionKind.FN_TYPE && value.color !== fnType.color) {
            const fnArg = fnType.arg;
            const temp = tempRegistry.emitUnknown(fnType.inputType);
            let nextType: Expression = fnType.outputType;
            if (fnArg !== void 0) {
                nextType = replaceOneSymbol(nextType, fnArg.symbol, temp);
            }
            ret = {kind: ExpressionKind.CALL, fn: ret, arg: temp, type: nextType};
            fnType = nextType;
        }
        assert(fnType.kind === ExpressionKind.FN_TYPE);
        equalConstraints.push([fnType.inputType, argType]);
        let retType = fnType.outputType;
        if (fnType.arg !== void 0) {
            retType = replaceOneSymbol(retType, fnType.arg.symbol, arg);
        }
        return {
            kind: ExpressionKind.CALL,
            fn: ret,
            arg,
            type: retType,
        };
    }

    function evaluate(expr: Expression) {
        const e = new Evaluator(tempRegistry, builtins);
        return e.evaluate(expr);
    }

    function setSymbolType(symbol: Symbol, type: Expression) {
        const entry = tempRegistry.getSymbolEntry(symbol);
        if (!tempRegistry.isLocalSymbol(symbol) || 0 === (entry.flags & SymbolFlags.HAS_TYPE)) {
            return false;
        }
        if (entry.type !== void 0) {
            equalConstraints.push([entry.type, type]);
        } else {
            entry.type = type;
        }
        if (entry.value !== void 0) {
            equalConstraints.push([type, typeOfExpression0(entry.value)]);
        }
        return true;
    }

    function setSymbolValue(symbol: Symbol, value: Expression) {
        const type = typeOfExpression0(value);
        const entry = tempRegistry.getSymbolEntry(symbol);
        if (!tempRegistry.isLocalSymbol(symbol) || 0 === (entry.flags & SymbolFlags.HAS_ASSIGNMENT)) {
            return false;
        }
        if (entry.type !== void 0) {
            equalConstraints.push([entry.type, type]);
        } else {
            entry.type = type;
        }
        if (entry.value !== void 0) {
            equalConstraints.push([value, entry.value]);
        } else {
            entry.value = value;
        }
        return true;
    }

    function evaluateEqualConstraint(con: [Expression, Expression]) {
        const [oldExpr1, oldExpr2] = con;
        let expr1 = evaluate(oldExpr1);
        let expr2 = evaluate(oldExpr2);
        const changed = expr1 !== oldExpr1 || expr2 !== oldExpr2;
        if (expr1.kind > expr2.kind) {
            const t = expr1;
            expr1 = expr2;
            expr2 = t;
        }
        if (expr1.kind === ExpressionKind.SYMBOL) {
            if (expr2.kind === ExpressionKind.SYMBOL && expr1.symbol === expr2.symbol) {
                return true;
            }
            if (setSymbolValue(expr1.symbol, expr2)) {
                return true;
            }
            if (expr2.kind === ExpressionKind.SYMBOL && setSymbolValue(expr2.symbol, expr1)) {
                return true;
            }
        }
        if (expr1.kind === ExpressionKind.UNIVERSE && expr2.kind === ExpressionKind.UNIVERSE) {
            equalConstraints.push([expr1.level, expr2.level]);
            return true;
        }
        if (expr1.kind === ExpressionKind.NUMBER && expr2.kind === ExpressionKind.NUMBER && expr1.isLevel && expr2.isLevel && expr1.value === expr2.value) {
            return true;
        }
        if (expr1.kind === ExpressionKind.STRING && expr2.kind === ExpressionKind.STRING && expr1.value === expr2.value) {
            return true;
        }
        equalConstraints.push([expr1, expr2]);
        return changed;
    }

    function iterate() {
        let changed = false;
        for (const data of hir.regs) {
            changed = pollHIR(data) || changed;
        }

        const ec = equalConstraints.slice(0);
        equalConstraints.length = 0;
        for (const con of ec) {
            changed = evaluateEqualConstraint(con) || changed;
        }
        return changed;
    }

    function dump(iteration: number) {
        console.log(`iteration: ${iteration}`);
        console.log('symbols:');
        for (const line of tempRegistry.dump()) {
            console.log(line);
        }
        console.log('hir:');
        for (let i = 0, a = hir.regs; i < a.length; i++) {
            const r = a[i].resolvedValue;
            if (r !== void 0) {
                console.log(`resolved($${i}): ${inputForm(tempRegistry, typeOfExpression0(r))} = ${inputForm(tempRegistry, r)}`);
            }
        }
        console.log('equal constraint:');
        for (const [expr1, expr2] of equalConstraints) {
            console.log(inputForm(tempRegistry, expr1) + ' === ' + inputForm(tempRegistry, expr2));
        }
    }

    function run() {
        let iterations = 0;
        dump(0);
        while (iterate()) {
            iterations++;
            dump(iterations);
        }

        for (const [expr1, expr2] of equalConstraints) {
            diagnostics.push({kind: TypeCheckDiagnosticKind.UNEQUAL, expr1, expr2});
        }
        tempRegistry.forEachLocalSymbol((symbol, entry) => {
            if (0 !== (entry.flags & SymbolFlags.IS_TEMP) && entry.value === void 0) {
                diagnostics.push({kind: TypeCheckDiagnosticKind.UNINFERRED, symbol});
            }
        });
        if (diagnostics.length > 0) {
            return;
        }
        console.log('passed');
        registry.mergeFrom(tempRegistry);
        // tempRegistry.forEachLocalSymbol((symbol, entry) => {
        //     if (0 !== (entry.flags & SymbolFlags.IS_TEMP)) {
        //         assert(entry.value !== void 0);
        //         tempReps.set(symbol, evaluate(entry.value));
        //     } else {
        //         let parent: Symbol | null = null;
        //         if (entry.parent !== null) {
        //             const p = tempReps.get(entry.parent) ?? panic();
        //             assert(p.kind === ExpressionKind.SYMBOL);
        //             parent = p.symbol;
        //         }
        //         const ns = registry.emitSymbol({...entry, parent});
        //         if (minNewSymbol === null) {
        //             minNewSymbol = ns;
        //         }
        //         tempReps.set(symbol, se(ns));
        //     }
        // });
        // if (diagnostics.length === 0 && minNewSymbol !== null) {
        //     registry.forEachLocalSymbol((symbol, entry) => {
        //         if (symbol >= minNewSymbol!) {
        //             if (entry.type !== void 0) {
        //                 entry.type = replaceSymbols(entry.type, tempReps);
        //             }
        //             if (entry.value !== void 0) {
        //                 entry.value = replaceSymbols(entry.value, tempReps);
        //             }
        //             // TODO: down values
        //         }
        //     });
        // }
    }
}

type EvaluatorAction = (self: Evaluator) => void;
export class Evaluator {
    ownValue = true;
    downValue = true;
    expandLambda = true;
    private readonly stack: Expression[] = [];
    private readonly todo: EvaluatorAction[] = [];
    constructor(readonly reg: SymbolRegistry, readonly builtins: BuiltinSymbols) {}
    private doActions(...actions: EvaluatorAction[]) {
        pushReversed(this.todo, actions);
    }
    private _evaluate(expr: Expression): EvaluatorAction {
        return self => {
            switch (expr.kind) {
                case ExpressionKind.SYMBOL: {
                    const entry = this.reg.getSymbolEntry(expr.symbol);
                    if (this.ownValue && entry.value !== void 0) {
                        self.doActions(self._evaluate(entry.value));
                    } else {
                        self.stack.push(expr);
                    }
                    break;
                }
                case ExpressionKind.CALL: {
                    self.doActions(self._evaluate(expr.fn), self._evaluate(expr.arg), self => {
                        const arg = self.stack.pop()!;
                        const fn = self.stack.pop()!;
                        if (fn.kind === ExpressionKind.LAMBDA && this.expandLambda) {
                            if (fn.arg !== void 0) {
                                self.doActions(self._evaluate(replaceOneSymbol(fn.body, fn.arg.symbol, arg)));
                            } else {
                                self.stack.push(fn.body);
                            }
                        } else {
                            if (fn !== expr.fn || arg !== expr.arg) {
                                self.doActions(self._postCall({...expr, fn, arg}));
                            } else {
                                self.doActions(self._postCall(expr));
                            }
                        }
                    });
                    break;
                }
                case ExpressionKind.FN_TYPE: {
                    self.doActions(self._evaluate(expr.inputType), self._evaluate(expr.outputType), self => {
                        const outputType = self.stack.pop()!;
                        const inputType = self.stack.pop()!;
                        if (inputType !== expr.inputType || outputType !== expr.outputType) {
                            self.stack.push({...expr, inputType, outputType});
                        } else {
                            self.stack.push(expr);
                        }
                    });
                    break;
                }
                case ExpressionKind.LAMBDA: {
                    self.doActions(self._evaluate(expr.body), self => {
                        const body = self.stack.pop()!;
                        if (body !== expr.body) {
                            self.stack.push({...expr, body});
                        } else {
                            self.stack.push(expr);
                        }
                    });
                    break;
                }
                case ExpressionKind.UNIVERSE: {
                    self.doActions(self._evaluate(expr.level), self => {
                        const level = self.stack.pop()!;
                        if (level !== expr.level) {
                            self.stack.push({...expr, level});
                        } else {
                            self.stack.push(expr);
                        }
                    });
                    break;
                }
                case ExpressionKind.NUMBER:
                case ExpressionKind.STRING:
                    self.stack.push(expr);
                    break;
                default: panic();
            }
        };
    }
    private _postCall(expr: CallExpression): EvaluatorAction {
        return self => {
            const [fn, args] = collectFnArgs(expr);
            if (fn.kind === ExpressionKind.SYMBOL) {
                const entry = this.reg.getSymbolEntry(fn.symbol);
                if (entry.evaluator !== void 0) {
                    const value = entry.evaluator(args);
                    if (value !== null) {
                        self.stack.push(value);
                        return;
                    }
                }
            }
            self.stack.push(expr);
        };
    }
    wait() {
        while (this.todo.length > 0) {
            this.todo.pop()!(this);
        }
    }
    evaluate(expr: Expression) {
        this.stack.length = 0;
        this.doActions(this._evaluate(expr));
        this.wait();
        assert(this.stack.length === 1);
        return this.stack.pop()!;
    }
}
