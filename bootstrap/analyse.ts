import { generateHIRDependencies, HIRCall, HIRFnType, HIRHost, HIRKind, HIRLambda, HIRReg, HIRRegData, HIRSymbolRule, visitHIR } from "./irgen";
import { StructVariant, SourceRange, asSourceRange, SourceRangeMessage } from "./parser";
import { assert, constArray, IndexedMap, Logger, makeArray, Mutable, panic, popReversed, pushReversed, Timer } from "./util";

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

export const enum SymbolFlags {
    ALLOW_DEF_TYPE = 1,
    ALLOW_ASSIGNMENT = 2,
    ALLOW_DOWN_VALUE = 4,
    ALLOW_UP_VALUE = 8,
    IS_VARIABLE = 16,
    MUST_HAVE_VALUE = 32, // must have an assignment at the end of analyse
    AUTO_SUBSTITUTE = 64, // auto substitute this symbol when it has an assignment during analyse
    AUTO_REMOVE = 128,
    MAY_CONTAINS_LOCAL = 256, // definition of this symbol may contain local variable
}

export const SYMBOL_FLAG_NAMES = ['AllowDefType', 'AllowAssigment', 'AllowDownValue', 'AllowUpValue', 'IsVariable', 'MustHaveValue', 'AutoSubstitute', 'AutoRemove', 'MayContainVariable'];

export function dumpFlags(flags: SymbolFlags) {
    const parts: string[] = [];
    for (const name of SYMBOL_FLAG_NAMES) {
        if (0 !== (flags & 1)) {
            parts.push(name);
        }
        flags >>= 1;
    }
    return parts;
}

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

export interface ExpressionWithReplaces {
    readonly expr: Expression;
    readonly replaces: Map<Symbol, Expression>;
}

export interface SymbolData {
    readonly name?: string;
    readonly loc?: SourceRange;
    readonly parent: Symbol | null;
    readonly evaluator?: (args: Expression[]) => Expression | null;
    readonly flags: number;
    removed?: boolean;
    subSymbols?: Map<string, Symbol>;
    type?: Expression;
    value?: Expression;
    downValues?: [Expression, Expression][];
    upValues?: [Expression, Expression][];
}

export const enum TypeCheckDiagnosticKind {
    UNEQUAL,
    UNINFERRED,
}

export type TypeCheckDiagnostic = TypeCheckDiagnosticUnequal | TypeCheckDiagnosticUninferred;

export interface TypeCheckDiagnosticUnequal {
    readonly kind: TypeCheckDiagnosticKind.UNEQUAL;
    readonly con: EqualConstraint;
}

export interface TypeCheckDiagnosticUninferred {
    readonly kind: TypeCheckDiagnosticKind.UNINFERRED;
    readonly symbol: Symbol;
}

export function renderTypeCheckDiagnostic(d: TypeCheckDiagnostic, reg: SymbolRegistry) {
    switch (d.kind) {
        case TypeCheckDiagnosticKind.UNEQUAL: return [`unequal expressions ${inputForm(reg, d.con.expr1)} and ${inputForm(reg, d.con.expr2)}`];
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
            parent: this.levelType,
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
            parent: this.levelType,
            flags: 0,
            evaluator(args) {
                if (args.length < 2) return null;
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
    private readonly removedSymbols: Symbol[] = [];
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
        if (entry.parent === null && 0 !== (entry.flags & SymbolFlags.MAY_CONTAINS_LOCAL)) {
            return (entry.name ?? '') + `$${s}`;
        }
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
    isVariable(symbol: Symbol) {
        const entry = this.getSymbolEntry(symbol);
        return 0 !== (entry.flags & SymbolFlags.IS_VARIABLE);
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
            const entry = a[i];
            if (!entry.removed) {
                cb(this.symbolOffset + i as Symbol, a[i]);
            }
        }
    }
    emitUnknown(type: Expression, isVariable: boolean): SymbolExpression {
        let f = isVariable ? SymbolFlags.IS_VARIABLE : SymbolFlags.MUST_HAVE_VALUE;
        const ret = this.emitSymbol({type, parent: null, flags: f | SymbolFlags.ALLOW_ASSIGNMENT | SymbolFlags.ALLOW_DEF_TYPE | SymbolFlags.AUTO_SUBSTITUTE | SymbolFlags.AUTO_REMOVE | SymbolFlags.MAY_CONTAINS_LOCAL});
        return se(ret);
    }
    emitUnknownType(builtins: BuiltinSymbols) {
        return this.emitUnknown({kind: ExpressionKind.UNIVERSE, level: this.emitUnknown(se(builtins.levelType), false)}, false);
    }
    mergeFrom(reg: SymbolRegistry) {
        assert(reg.symbolOffset === this.symbols.length);
        assert(reg.parent === this);
        for (const d of reg.symbols) {
            this.symbols.push(d);
        }
        reg.symbols.length = 0;
    }
    substituteTemps(expr: Expression) {
        return mapExpression(expr, (expr, info) => {
            if (expr.kind === ExpressionKind.SYMBOL) {
                const entry = this.getSymbolEntry(expr.symbol);
                if (0 !== (entry.flags & SymbolFlags.AUTO_SUBSTITUTE) && entry.value !== void 0) {
                    info.rerun(entry.value);
                    return;
                }
            }
            info.emit(expr);
        }) ?? panic();
    }
    mapExpressionsOfSymbol(s: Symbol, mapper: (expr: Expression) => Expression) {
        let changed = false;
        const entry = this.getSymbolEntry(s);
        if (entry.type !== void 0) {
            const type = mapper(entry.type);
            changed = changed || type !== entry.type;
            entry.type = type;
        }
        if (entry.value !== void 0) {
            const value = mapper(entry.value);
            changed = changed || value !== entry.value;
            entry.value = value;
        }
        if (entry.downValues !== void 0) {
            for (const dv of entry.downValues) {
                const lhs = mapper(dv[0]);
                const rhs = mapper(dv[1]);
                if (lhs !== dv[0] || rhs !== dv[1]) {
                    changed = true;
                }
                dv[0] = lhs;
                dv[1] = rhs;
            }
        }
        return changed;
    }
    mapAllExpressions(mapper: (expr: Expression) => Expression) {
        let changed = false;
        this.forEachLocalSymbol(symbol => this.mapExpressionsOfSymbol(symbol, mapper));
        return changed;
    }
    substituteAllTemps() {
        return this.mapAllExpressions(expr => this.substituteTemps(expr));
    }
    cleanupTemps() {
        const marked = constArray(false, this.symbols.length);
        const todo: Symbol[] = [];
        const visitOneExpr = (expr: Expression) => {
            mapExpression(expr, (expr, info) => {
                if (expr.kind === ExpressionKind.SYMBOL && this.isLocalSymbol(expr.symbol) && !marked[expr.symbol]) {
                    todo.push(expr.symbol);
                }
                info.emit(expr);
            });
        }
        this.forEachLocalSymbol((symbol, entry) => {
            if (0 === (entry.flags & SymbolFlags.AUTO_REMOVE)) {
                todo.push(symbol);
            }
        });
        while (todo.length > 0) {
            const s = todo.pop()!;
            if (!marked[s]) {
                marked[s] = true;
                this.mapExpressionsOfSymbol(s, expr => {
                    visitOneExpr(expr);
                    return expr;
                });
            }
        }
        this.forEachLocalSymbol((symbol, entry) => {
            if (!marked[symbol]) {
                entry.removed = true;
                this.removedSymbols.push(symbol);
            }
        });
    }
    dump() {
        const lines: string[] = [];
        this.forEachLocalSymbol((symbol, entry) => {
            const name = this.getSymbolDisplayName(symbol);
            const flags = dumpFlags(entry.flags);
            if (flags.length > 0) {
                lines.push(`Flags(${name}) = {${flags.join(', ')}}`);
            }
            if (entry.type !== void 0) {
                lines.push(name + ': ' + inputForm(this, entry.type));
            }
            if (entry.value !== void 0) {
                lines.push(name + ' = ' + inputForm(this, entry.value));
            }
            if (entry.downValues !== void 0) {
                for (const [lhs, rhs] of entry.downValues) {
                    lines.push(inputForm(this, lhs) + ' = ' + inputForm(this, rhs));
                }
            }
            if (entry.upValues !== void 0) {
                for (const [lhs, rhs] of entry.upValues) {
                    lines.push(inputForm(this, lhs) + ' ^= ' + inputForm(this, rhs));
                }
            }
        });
        return lines;
    }
}

export function typeOfExpression(expr: Expression, reg: SymbolRegistry, builtins: BuiltinSymbols | undefined): Expression {
    switch (expr.kind) {
        case ExpressionKind.SYMBOL: {
            const entry = reg.getSymbolEntry(expr.symbol);
            if (entry.type === void 0 && 0 !== (entry.flags & SymbolFlags.ALLOW_DEF_TYPE)) {
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

export function collectFnArgs(expr: CallExpression): [Expression, Expression[]] {
    const args: Expression[] = [];
    let expr0: Expression = expr;
    while (expr0.kind === ExpressionKind.CALL) {
        args.unshift(expr0.arg);
        expr0 = expr0.fn;
    }
    assert(args.length > 0);
    return [expr0, args];
}

export function getFn(expr: CallExpression) {
    let expr0: Expression = expr;
    while (expr0.kind === ExpressionKind.CALL) {
        expr0 = expr0.fn;
    }
    return expr0;
}

export function collectFnTypeColors(expr: Expression) {
    const colors: number[] = [];
    while (expr.kind === ExpressionKind.FN_TYPE) {
        colors.push(expr.color);
        expr = expr.outputType;
    }
    return colors;
}

export function isValidPattern(reg: SymbolRegistry, expr: Expression) {
    const todo: [Expression, boolean][] = [[expr, false]];
    while (todo.length > 0) {
        const [expr, isHead] = todo.pop()!;
        switch (expr.kind) {
            case ExpressionKind.SYMBOL: {
                const entry = reg.getSymbolEntry(expr.symbol);
                const flags = entry.flags;
                if (0 !== (flags & SymbolFlags.IS_VARIABLE)) {
                    break;
                }
                if (entry.value !== void 0 || 0 !== (flags & SymbolFlags.ALLOW_ASSIGNMENT)) {
                    return false;
                }
                if (entry.downValues !== void 0 && entry.downValues.length > 0 || 0 !== (flags & SymbolFlags.ALLOW_DOWN_VALUE)) {
                    return false;
                }
            }
        }
    }
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
                assert(t.type.kind === ExpressionKind.FN_TYPE);
                const inputType = t.type.inputType;
                const color = t.type.color;
                todo.push(stack => {
                    const body = stack.pop()!;
                    const inputType = stack.pop()!;
                    const argStr = color === 0 ? `(${arg ?? '_'}: ${inputType})` : `[${arg ?? '_'}: ${inputType}]`;
                    stack.push('\\' + argStr + ' ' + body);
                }, t.body, inputType);
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

export function containsUninferedTemps(reg: SymbolRegistry, expr: Expression) {
    return null === mapExpression(expr, (expr, info) => {
        if (expr.kind === ExpressionKind.SYMBOL) {
            const entry = reg.getSymbolEntry(expr.symbol);
            const flags = entry.flags;
            const mcl = 0 !== (flags & SymbolFlags.MAY_CONTAINS_LOCAL);
            if (mcl && 0 !== (entry.flags & (SymbolFlags.ALLOW_ASSIGNMENT | SymbolFlags.ALLOW_DOWN_VALUE))) {
                info.terminate();
                return;
            }
        }
        info.emit(expr);
    });
}

export function argsContainsUninferedTemps(reg: SymbolRegistry, expr: CallExpression) {
    let expr0: Expression = expr;
    while (expr0.kind === ExpressionKind.CALL) {
        if (containsUninferedTemps(reg, expr0.arg)) {
            return true;
        }
        expr0 = expr0.fn;
    }
    return false;
}

export interface MapperInfo {
    terminate(): void;
    rerun(expr: Expression): void;
    emit(expr: Expression): void;
}

export function mapExpression(expr: Expression, mapper: (expr: Expression, info: MapperInfo) => void) {
    const todo: (Expression | ((stack: Expression[]) => Expression))[] = [expr];
    const stack: Expression[] = [];
    let terminated = false;
    const info: MapperInfo = {
        terminate() {
            terminated = true;
        },
        rerun(expr) {
            todo.push(expr);
        },
        emit(expr) {
            stack.push(expr);
        },
    };
    while (todo.length > 0) {
        const t = todo.pop()!;
        if (typeof t === 'function') {
            mapper(t(stack), info);
            if (terminated) {
                return null;
            }
            continue;
        }
        switch (t.kind) {
            case ExpressionKind.NUMBER:
            case ExpressionKind.STRING:
            case ExpressionKind.SYMBOL: {
                mapper(t, info);
                if (terminated) {
                    return null;
                }
                break;
            }
            case ExpressionKind.CALL: {
                const loc = t.loc;
                todo.push(stack => {
                    const type = stack.pop()!;
                    const arg = stack.pop()!;
                    const fn = stack.pop()!;
                    if (fn !== t.fn || arg !== t.arg || type !== t.type) {
                        return {kind: ExpressionKind.CALL, fn, arg, type, loc};
                    } else {
                        return t;
                    }
                }, t.type, t.arg, t.fn);
                break;
            }
            case ExpressionKind.FN_TYPE: {
                const {loc, color} = t;
                todo.push(stack => {
                    const typeLevel = stack.pop()!;
                    const outputType = stack.pop()!;
                    const inputType = stack.pop()!;
                    let arg: SymbolExpression | undefined = void 0;
                    if (t.arg !== void 0) {
                        const a = stack.pop()!;
                        assert(a.kind === ExpressionKind.SYMBOL);
                        arg = a;
                    }
                    if (inputType !== t.inputType || outputType !== t.outputType || typeLevel !== t.typeLevel) {
                        return {kind: ExpressionKind.FN_TYPE, inputType, outputType, arg, color, typeLevel, loc};
                    } else {
                        return t;
                    }
                }, t.typeLevel, t.outputType, t.inputType);
                if (t.arg !== void 0) {
                    todo.push(t.arg);
                }
                break;
            }
            case ExpressionKind.LAMBDA: {
                todo.push(stack => {
                    const type = stack.pop()!;
                    const body = stack.pop()!;
                    let arg: SymbolExpression | undefined = void 0;
                    if (t.arg !== void 0) {
                        const a = stack.pop()!;
                        assert(a.kind === ExpressionKind.SYMBOL);
                        arg = a;
                    }
                    if (body !== t.body || type !== t.type) {
                        return {kind: ExpressionKind.LAMBDA, arg, body, type, loc: t.loc};
                    } else {
                        return t;
                    }
                }, t.type, t.body);
                if (t.arg !== void 0) {
                    todo.push(t.arg);
                }
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
    return mapExpression(expr, (expr, info) => {
        if (expr.kind === ExpressionKind.SYMBOL && expr.symbol === s) {
            info.emit(replacement);
        } else {
            info.emit(expr);
        }
    }) ?? panic();
}

export function replaceSymbols(expr: Expression, m: Map<Symbol, Expression>) {
    return mapExpression(expr, (expr, info) => {
        if (expr.kind === ExpressionKind.SYMBOL) {
            info.emit(m.get(expr.symbol) ?? expr);
        } else {
            info.emit(expr);
        }
    }) ?? panic();
}

export function freeQ(expr: Expression, symbol: Symbol) {
    return null !== mapExpression(expr, (expr, info) => {
        if (expr.kind === ExpressionKind.SYMBOL && expr.symbol === symbol) {
            info.terminate();
            return;
        }
        info.emit(expr);
    });
}

export function sameQ(expr1: Expression, expr2: Expression) {
    const todo = [expr1, expr2];
    while (todo.length > 0) {
        const expr2 = todo.pop()!;
        const expr1 = todo.pop()!;
        switch (expr1.kind) {
            case ExpressionKind.SYMBOL:
                if (expr2.kind !== ExpressionKind.SYMBOL || expr2.symbol !== expr1.symbol) {
                    return false;
                }
                break;
            case ExpressionKind.NUMBER:
                if (expr2.kind !== ExpressionKind.NUMBER || expr2.isLevel !== expr1.isLevel || expr2.value !== expr1.value) {
                    return false;
                }
                break;
            case ExpressionKind.STRING:
                if (expr2.kind !== ExpressionKind.STRING || expr2.value !== expr1.value) {
                    return false;
                }
                break;
            case ExpressionKind.CALL:
                if (expr2.kind !== ExpressionKind.CALL) {
                    return false;
                }
                todo.push(expr1.arg, expr2.arg, expr1.fn, expr2.fn);
                break;
            case ExpressionKind.FN_TYPE: {
                if (expr2.kind !== ExpressionKind.FN_TYPE) {
                    return false;
                }
                let output2 = expr2.outputType;
                if (expr1.arg !== void 0 && expr2.arg !== void 0 && expr1.arg.symbol !== expr2.arg.symbol) {
                    output2 = replaceOneSymbol(output2, expr2.arg.symbol, expr1.arg);
                }
                todo.push(expr1.outputType, output2, expr1.inputType, expr2.inputType);
                break;
            }
            case ExpressionKind.LAMBDA: {
                if (expr2.kind !== ExpressionKind.LAMBDA) {
                    return false;
                }
                let body2 = expr2.body;
                if (expr1.arg !== void 0 && expr2.arg !== void 0 && expr1.arg.symbol !== expr2.arg.symbol) {
                    body2 = replaceOneSymbol(body2, expr2.arg.symbol, expr1.arg);
                }
                todo.push(expr1.body, body2);
                break;
            }
            case ExpressionKind.UNIVERSE: {
                if (expr2.kind !== ExpressionKind.UNIVERSE) {
                    return false;
                }
                todo.push(expr1.level, expr2.level);
                break;
            }
        }
    }
    return true;
}

export function matchPattern(reg: SymbolRegistry, pattern: Expression, expr: Expression) {
    const reps = new Map<Symbol, Expression>();
    const todo = [pattern, expr];
    while (todo.length > 0) {
        const expr = todo.pop()!;
        const pattern = todo.pop()!;
        switch (pattern.kind) {
            case ExpressionKind.STRING:
            case ExpressionKind.NUMBER:
            case ExpressionKind.LAMBDA:
            case ExpressionKind.UNIVERSE:
            case ExpressionKind.FN_TYPE:
                if (!sameQ(pattern, expr)) {
                    return null;
                }
                break;
            case ExpressionKind.SYMBOL: {
                if (reg.isVariable(pattern.symbol)) {
                    const old = reps.get(pattern.symbol);
                    if (old !== void 0) {
                        if (!sameQ(old, expr)) {
                            return null;
                        }
                    } else {
                        reps.set(pattern.symbol, expr);
                    }
                } else {
                    if (expr.kind !== ExpressionKind.SYMBOL || expr.symbol !== pattern.symbol) {
                        return null;
                    }
                }
                break;
            }
            case ExpressionKind.CALL:
                if (expr.kind !== ExpressionKind.CALL || countArgs(pattern) !== countArgs(expr)) {
                    return null;
                }
                todo.push(pattern.arg, expr.arg, pattern.fn, expr.fn);
                break;
            default: panic();
        }
    }
    return reps;
}

export function countArgs(expr: Expression) {
    let ret = 0;
    while (expr.kind === ExpressionKind.CALL) {
        ret++;
        expr = expr.fn;
    }
    return ret;
}

function checkFnTypeColor(expr: Expression, color: number) {
    while (expr.kind === ExpressionKind.FN_TYPE && expr.color !== color) {
        expr = expr.outputType;
    }
    return expr.kind === ExpressionKind.FN_TYPE;
}

function collectSymbols(expr: Expression, set: Set<Symbol>) {
    mapExpression(expr, (expr, info) => {
        if (expr.kind === ExpressionKind.SYMBOL) {
            set.add(expr.symbol);
        }
        info.emit(expr);
    });
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

interface HIRResolvedData {
    completeDone: boolean;
    noEqualConstraints: boolean;
    type?: Expression;
    value?: Expression;
}

interface EqualConstraint {
    readonly source: HIRReg;
    readonly expr1: Expression;
    readonly expr2: Expression;
}

export function checkTypes(registry: SymbolRegistry, builtins: BuiltinSymbols, hir: HIRHost, logger: Logger): TypeCheckResult | null {
    const hirRegs = hir.regs;
    const hirResolvedData: HIRResolvedData[] = makeArray(() => ({completeDone: false, noEqualConstraints: true}), hirRegs.length);
    const tempRegistry = new SymbolRegistry(registry);
    const equalConstraints: EqualConstraint[] = [];
    const diagnostics: TypeCheckDiagnostic[] = [];
    const doneSymbols = new Set<Symbol>();
    const hirDependencies = generateHIRDependencies(hir);

    run();
    return diagnostics.length > 0 ? {tempRegistry, diagnostics} : null;

    function typeOfExpression0(expr: Expression) {
        return typeOfExpression(expr, tempRegistry, builtins);
    }

    function pollHIR(hirReg: HIRReg): boolean {
        const data = hirRegs[hirReg];
        const resolved = hirResolvedData[hirReg];
        const value = data.value;
        if (resolved.completeDone) {
            assert(resolved.value !== void 0);
            return false;
        }
        switch (value.kind) {
            case HIRKind.EXPR:
                resolved.value = value.expr;
                resolved.completeDone = true;
                return true;
            case HIRKind.NUMBER: {
                const type = resolved.type;
                if (type !== void 0) {
                    if (type.kind === ExpressionKind.SYMBOL && type.symbol === builtins.levelType) {
                        resolved.value = {
                            kind: ExpressionKind.NUMBER,
                            isLevel: true,
                            value: value.value,
                        };
                        resolved.completeDone = true;
                        return true;
                    } else if (type.kind === ExpressionKind.SYMBOL && type.symbol === builtins.numberType) {
                        resolved.value = {
                            kind: ExpressionKind.NUMBER,
                            isLevel: false,
                            value: value.value,
                        };
                        resolved.completeDone = true;
                        return true;
                    }
                }
                return false;
            }
            case HIRKind.CALL: return pollCall(hirReg, value, resolved);
            case HIRKind.LAMBDA: return pollLambda(hirReg, value, resolved);
            case HIRKind.FN_TYPE: return pollFnType(hirReg, value, resolved);
            case HIRKind.SYMBOL: {
                let parent: Symbol | null = null;
                if (value.parent !== null) {
                    const p = hirResolvedData[value.parent];
                    if (p.value === void 0) {
                        return false;
                    }
                    assert(p.value.kind === ExpressionKind.SYMBOL);
                    parent = p.value.symbol;
                }
                const entry: Mutable<SymbolData> = {parent, name: value.name, loc: data.loc, flags: value.flags};
                resolved.value = {
                    kind: ExpressionKind.SYMBOL,
                    symbol: tempRegistry.emitSymbol(entry),
                };
                resolved.completeDone = true;
                return true;
            }
            case HIRKind.SYMBOL_TYPE: {
                const symbol = hirResolvedData[value.symbol].value;
                const type = hirResolvedData[value.type].value;
                if (symbol === void 0 || type === void 0) {
                    return false;
                }
                assert(symbol.kind === ExpressionKind.SYMBOL);
                setSymbolType(symbol.symbol, type, hirReg);
                resolved.value = se(builtins.unit);
                resolved.completeDone = true; // safe to set here since this HIR kind should never be referenced
                return true;
            }
            case HIRKind.SYMBOL_ASSIGN: {
                const symbol = hirResolvedData[value.symbol].value;
                const v = hirResolvedData[value.value].value;
                if (symbol === void 0 || v === void 0) {
                    return false;
                }
                assert(symbol.kind === ExpressionKind.SYMBOL);
                setSymbolValue(symbol.symbol, v, hirReg);
                resolved.value = se(builtins.unit);
                resolved.completeDone = true; // ditto
                return true;
            }
            case HIRKind.SYMBOL_RULE: return pollDownValue(hirReg, value, resolved);
            case HIRKind.MEMBER_ACCESS: {
                let ret = false;
                if (resolved.value === void 0) {
                    const lhs = hirResolvedData[value.lhs].value;
                    if (lhs !== void 0) {
                        if (lhs.kind === ExpressionKind.SYMBOL) {
                            const entry = tempRegistry.getSymbolEntry(lhs.symbol);
                            if (entry.subSymbols !== void 0 && entry.subSymbols.has(value.name)) {
                                resolved.value = se(entry.subSymbols.get(value.name)!);
                                ret = true;
                            }
                        }
                    }
                }
                if (!resolved.completeDone) {
                    if (hirResolvedData[value.lhs].completeDone) {
                        resolved.completeDone = true;
                        return true;
                    }
                }
                return ret;
            }
        }
    }

    function pollFnType(source: HIRReg, value: HIRFnType, resolved: HIRResolvedData): boolean {
        if (resolved.value === void 0) {
            const inputType = hirResolvedData[value.inputType].value;
            if (inputType === void 0 || !hirResolvedData[value.outputType].completeDone) return false;
            let outputType = hirResolvedData[value.outputType].value ?? panic();
            let arg: SymbolExpression | undefined = void 0;
            if (value.arg !== void 0) {
                const a = hirResolvedData[value.arg].value;
                if (a === void 0 || a.kind !== ExpressionKind.SYMBOL) return false;
                arg = a;
            }
            const inputLevel = tempRegistry.emitUnknown(se(builtins.levelType), false);
            const outputLevel = tempRegistry.emitUnknown(se(builtins.levelType), false);
            addEqualConstraint(typeOfExpression0(inputType), {kind: ExpressionKind.UNIVERSE, level: inputLevel}, source);
            addEqualConstraint(typeOfExpression0(outputType), {kind: ExpressionKind.UNIVERSE, level: outputLevel}, source);
            resolved.value = {
                kind: ExpressionKind.FN_TYPE,
                color: value.color,
                inputType,
                outputType,
                arg,
                typeLevel: builtins.makeLevelMax(inputLevel, outputLevel),
            };
            return true;
        }
        if (!resolved.completeDone) {
            if (hirResolvedData[value.inputType].completeDone && hirResolvedData[value.outputType].completeDone && resolved.noEqualConstraints) {
                resolved.completeDone = true;
                return true;
            }
            return false;
        }
        panic();
    }

    function pollCallIn(source: HIRReg, hirArg: HIRReg, color: number, isPattern: boolean, fn: Expression, arg: Expression): Expression | null {
        let fnType = typeOfExpression0(fn);

        if (arg === void 0) {
            const argEntry = hirResolvedData[hirArg];
            if (argEntry.type === void 0) {
                if (fn.kind === ExpressionKind.SYMBOL && fn.symbol === builtins.type) {
                    argEntry.type = se(builtins.levelType);
                } else if (fnType.kind === ExpressionKind.FN_TYPE) {
                    argEntry.type = fnType.inputType;
                }
            }
            return null;
        }
        const argType = typeOfExpression0(arg);

        if (fn.kind === ExpressionKind.SYMBOL && fn.symbol === builtins.type) {
            addEqualConstraint(argType, se(builtins.levelType), source);
            return {kind: ExpressionKind.UNIVERSE, level: arg};
        }

        if (fnType.kind !== ExpressionKind.FN_TYPE) {
            return null;
        }
        if (!checkFnTypeColor(fnType, color)) {
            return null;
        }
        let ret = fn;
        while (fnType.kind === ExpressionKind.FN_TYPE && color !== fnType.color) {
            const fnArg = fnType.arg;
            const temp = tempRegistry.emitUnknown(fnType.inputType, isPattern);
            let nextType: Expression = fnType.outputType;
            if (fnArg !== void 0) {
                nextType = replaceOneSymbol(nextType, fnArg.symbol, temp);
            }
            ret = {kind: ExpressionKind.CALL, fn: ret, arg: temp, type: nextType};
            fnType = nextType;
        }
        assert(fnType.kind === ExpressionKind.FN_TYPE);
        addEqualConstraint(fnType.inputType, argType, source);
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

    function pollCall(source: HIRReg, value: HIRCall, resolved: HIRResolvedData): boolean {
        if (resolved.value === void 0) {
            const fn = hirResolvedData[value.fn].value;
            const arg = hirResolvedData[value.arg].value;
            if (fn === void 0) {
                return false;
            }
            let fnType = typeOfExpression0(fn);

            if (arg === void 0) {
                const argEntry = hirResolvedData[value.arg];
                if (argEntry.type === void 0) {
                    if (fn.kind === ExpressionKind.SYMBOL && fn.symbol === builtins.type) {
                        argEntry.type = se(builtins.levelType);
                    } else if (fnType.kind === ExpressionKind.FN_TYPE) {
                        argEntry.type = fnType.inputType;
                    }
                }
                return false;
            }
            const argType = typeOfExpression0(arg);

            if (fn.kind === ExpressionKind.SYMBOL && fn.symbol === builtins.type) {
                addEqualConstraint(argType, se(builtins.levelType), source);
                resolved.value = {kind: ExpressionKind.UNIVERSE, level: arg};
                return true;
            }

            if (fnType.kind !== ExpressionKind.FN_TYPE) {
                return false;
            }
            if (!checkFnTypeColor(fnType, value.color)) {
                return false;
            }
            let ret = fn;
            while (fnType.kind === ExpressionKind.FN_TYPE && value.color !== fnType.color) {
                const fnArg = fnType.arg;
                const temp = tempRegistry.emitUnknown(fnType.inputType, value.isPattern);
                let nextType: Expression = fnType.outputType;
                if (fnArg !== void 0) {
                    nextType = replaceOneSymbol(nextType, fnArg.symbol, temp);
                }
                ret = {kind: ExpressionKind.CALL, fn: ret, arg: temp, type: nextType};
                fnType = nextType;
            }
            assert(fnType.kind === ExpressionKind.FN_TYPE);
            addEqualConstraint(fnType.inputType, argType, source);
            let retType = fnType.outputType;
            if (fnType.arg !== void 0) {
                retType = replaceOneSymbol(retType, fnType.arg.symbol, arg);
            }
            resolved.value = {
                kind: ExpressionKind.CALL,
                fn: ret,
                arg,
                type: retType,
            };
            return true;
        }
        if (!resolved.completeDone) {
            if (resolved.noEqualConstraints && hirResolvedData[value.fn].completeDone && hirResolvedData[value.arg].completeDone) {
                resolved.completeDone = true;
                return true;
            }
            return false;
        }
        panic();
    }

    function pollLambda(source: HIRReg, value: HIRLambda, resolved: HIRResolvedData): boolean {
        let ret = false;
        if (resolved.value === void 0) {
            if (!hirResolvedData[value.body].completeDone) {
                return false;
            }
            const body = hirResolvedData[value.body].value ?? panic();
            let arg: SymbolExpression | undefined = void 0;
            if (value.arg !== void 0) {
                const r = hirResolvedData[value.arg].value;
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
            const inputLevel = tempRegistry.emitUnknown(se(builtins.levelType), false);
            const outputLevel = tempRegistry.emitUnknown(se(builtins.levelType), false);
            addEqualConstraint(typeOfExpression0(inputType), {kind: ExpressionKind.UNIVERSE, level: inputLevel}, source);
            addEqualConstraint(typeOfExpression0(bodyType), {kind: ExpressionKind.UNIVERSE, level: outputLevel}, source);
            resolved.value = {
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
            ret = true;
        }
        if (!resolved.completeDone) {
            if (resolved.noEqualConstraints) {
                resolved.completeDone = true;
                return true;
            }
            return ret;
        }
        panic();
    }

    function evaluate(expr: Expression) {
        const e = new Evaluator(tempRegistry, builtins);
        return e.evaluate(expr);
    }

    function setSymbolType(symbol: Symbol, type: Expression, source: HIRReg) {
        const entry = tempRegistry.getSymbolEntry(symbol);
        if (!tempRegistry.isLocalSymbol(symbol) || 0 === (entry.flags & SymbolFlags.ALLOW_DEF_TYPE)) {
            return false;
        }
        if (entry.type !== void 0) {
            addEqualConstraint(entry.type, type, source);
        } else {
            entry.type = type;
            logger.info(() => `setting type ${tempRegistry.getSymbolDisplayName(symbol)}: ${inputForm(tempRegistry, type)}`);
        }
        if (entry.value !== void 0) {
            addEqualConstraint(type, typeOfExpression0(entry.value), source);
        }
        return true;
    }

    function addEqualConstraint(expr1: Expression, expr2: Expression, source: HIRReg) {
        logger.info(() => `add equal constraint ${inputForm(tempRegistry, expr1)} === ${inputForm(tempRegistry, expr2)}， with ${inputForm(tempRegistry, typeOfExpression0(expr1))}`);
        equalConstraints.push({expr1, expr2, source});
    }

    function setSymbolValue(symbol: Symbol, value: Expression, source: HIRReg) {
        const type = typeOfExpression0(value);
        const entry = tempRegistry.getSymbolEntry(symbol);
        if (!tempRegistry.isLocalSymbol(symbol) || 0 === (entry.flags & SymbolFlags.ALLOW_ASSIGNMENT)) {
            return false;
        }
        if (entry.value !== void 0) {
            addEqualConstraint(value, entry.value, source);
        } else {
            if (freeQ(value, symbol)) {
                entry.value = value;
                logger.info(() => `setting value ${tempRegistry.getSymbolDisplayName(symbol)} = ${inputForm(tempRegistry, value)}`);
            } else {
                return false;
            }
        }
        if (entry.type !== void 0) {
            addEqualConstraint(entry.type, type, source);
        } else {
            entry.type = type;
        }
        if (entry.downValues !== void 0) {
            for (const [lhs, rhs] of entry.downValues) {
                addEqualConstraint(lhs, rhs, source);
            }
            delete entry.downValues;
        }
        return true;
    }

    function pollDownValue(source: HIRReg, value: HIRSymbolRule, resolved: HIRResolvedData): boolean {
        const {lhs, rhs} = value.rule;
        if (resolved.value === void 0) {
            const lhsType = hirResolvedData[lhs].type;
            if (lhsType !== void 0 && hirResolvedData[rhs].type === void 0) {
                hirResolvedData[rhs].type = lhsType;
            }
            if (!hirResolvedData[lhs].completeDone || !hirResolvedData[rhs].completeDone) {
                return false;
            }
            const lhsExpr = hirResolvedData[lhs].value ?? panic();
            const rhsExpr = hirResolvedData[rhs].value ?? panic();
            assert(lhsExpr.kind === ExpressionKind.CALL);
            const [fn, args] = collectFnArgs(lhsExpr);
            assert(fn.kind === ExpressionKind.SYMBOL);
            const entry = tempRegistry.getSymbolEntry(fn.symbol);
            if (!tempRegistry.isLocalSymbol(fn.symbol) || 0 === (entry.flags & SymbolFlags.ALLOW_DOWN_VALUE)) {
                return false;
            }
            let target: [Expression, Expression][];
            if (!value.isUpValue) {
                if (entry.downValues === void 0) {
                    entry.downValues = [];
                }
                target = entry.downValues;
            } else {
                if (entry.upValues === void 0) {
                    entry.upValues = [];
                }
                target = entry.upValues;
            }
            addEqualConstraint(typeOfExpression0(lhsExpr), typeOfExpression0(rhsExpr), source);
            target.push([lhsExpr, rhsExpr]);
            resolved.value = se(builtins.unit);
            return true;
        }
        if (!resolved.completeDone) {
            if (resolved.noEqualConstraints) {
                resolved.completeDone = true;
                return true;
            }
            return false;
        }
        panic();
    }

    function symbolAssignOrder(s1: Symbol, s2: Symbol) {
        const entry1 = tempRegistry.getSymbolEntry(s1);
        const entry2 = tempRegistry.getSymbolEntry(s2);
        const settable1 = 0 !== (entry1.flags & SymbolFlags.ALLOW_ASSIGNMENT);
        const settable2 = 0 !== (entry2.flags & SymbolFlags.ALLOW_ASSIGNMENT);
        if (!settable1 && settable2) {
            return false;
        }
        if (!settable2) {
            return true;
        }
        const mhv1 = 0 !== (entry1.flags & SymbolFlags.MUST_HAVE_VALUE);
        const mhv2 = 0 !== (entry2.flags & SymbolFlags.MUST_HAVE_VALUE);
        return mhv1 || !mhv2;
    }

    function callExprOrder(expr1: CallExpression, expr2: CallExpression) {
        const fn1 = expr1.fn;
        const fn2 = expr2.fn;
        const arg1 = expr1.arg;
        const arg2 = expr2.arg;
        if (fn1.kind === ExpressionKind.SYMBOL && fn2.kind === ExpressionKind.SYMBOL) {
            if (!tempRegistry.isVariable(fn1.symbol) && tempRegistry.isVariable(fn2.symbol)) {
                return false;
            }
        }
    }

    function makeLambda(body: Expression, arg: SymbolExpression, type: Expression): Expression {
        if (body.kind === ExpressionKind.CALL && body.arg.kind === ExpressionKind.SYMBOL && body.arg.symbol === arg.symbol && freeQ(body.fn, arg.symbol)) {
            return body.fn;
        } else {
            return {
                kind: ExpressionKind.LAMBDA,
                arg,
                body,
                type,
            };
        }
    }

    function evaluateEqualConstraint(con: EqualConstraint, fixedPoint: boolean) {
        logger.info(() => `evaluating ${inputForm(tempRegistry, con.expr1)} === ${inputForm(tempRegistry, con.expr2)}, source %${con.source}`);
        const oldExpr1 = con.expr1;
        const oldExpr2 = con.expr2;
        let expr1 = evaluate(oldExpr1);
        let expr2 = evaluate(oldExpr2);
        if (oldExpr1 !== expr1 || oldExpr2 !== expr2) {
            logger.info(() => `evaluated expr: ${inputForm(tempRegistry, expr1)} === ${inputForm(tempRegistry, expr2)}`);
        }
        const changed = expr1 !== oldExpr1 || expr2 !== oldExpr2;
        if (expr1.kind !== ExpressionKind.SYMBOL && expr2.kind === ExpressionKind.SYMBOL) {
            const t = expr1;
            expr1 = expr2;
            expr2 = t;
        }
        if (expr1.kind === ExpressionKind.SYMBOL) {
            if (expr2.kind === ExpressionKind.SYMBOL) {
                if (expr1.symbol === expr2.symbol) {
                    return true;
                }
                if (!symbolAssignOrder(expr1.symbol, expr2.symbol)) {
                    let t = expr1;
                    expr1 = expr2;
                    expr2 = t;
                }
            }
            if (setSymbolValue(expr1.symbol, expr2, con.source)) {
                return true;
            }
        }
        if (expr1.kind === ExpressionKind.UNIVERSE && expr2.kind === ExpressionKind.UNIVERSE) {
            addEqualConstraint(expr1.level, expr2.level, con.source);
            return true;
        }
        if (expr1.kind === ExpressionKind.NUMBER && expr2.kind === ExpressionKind.NUMBER && expr1.isLevel && expr2.isLevel && expr1.value === expr2.value) {
            return true;
        }
        if (expr1.kind === ExpressionKind.STRING && expr2.kind === ExpressionKind.STRING && expr1.value === expr2.value) {
            return true;
        }

        if (expr1.kind !== ExpressionKind.CALL && expr2.kind === ExpressionKind.CALL) {
            const t = expr1;
            expr1 = expr2;
            expr2 = t;
        }
        if (expr1.kind === ExpressionKind.CALL) {
            if (expr2.kind === ExpressionKind.CALL) {
                if (fixedPoint) {
                    addEqualConstraint(expr1.fn, expr2.fn, con.source);
                    addEqualConstraint(expr1.arg, expr2.arg, con.source);
                    return true;
                }
                const [fn1, args1] = collectFnArgs(expr1);
                const [fn2, args2] = collectFnArgs(expr2);
                if (fn1.kind === ExpressionKind.SYMBOL && fn2.kind === ExpressionKind.SYMBOL) {
                    if (args1.length === args2.length && fn1.symbol === fn2.symbol) {
                        const entry = tempRegistry.getSymbolEntry(fn1.symbol);
                        if (0 === (entry.flags & (SymbolFlags.ALLOW_DOWN_VALUE | SymbolFlags.ALLOW_ASSIGNMENT))) {
                            for (let i = 0; i < args1.length; i++) {
                                addEqualConstraint(args1[i], args2[i], con.source);
                            }
                            addEqualConstraint(expr1.type, expr2.type, con.source);
                            return true;
                        }
                    }
                    if (!symbolAssignOrder(fn1.symbol, fn2.symbol)) {
                        const t = expr1;
                        expr1 = expr2;
                        expr2 = t;
                    }
                    const arg1 = args1[0];
                    const arg2 = args2[0];
                    if (arg1.kind === ExpressionKind.SYMBOL && arg2.kind === ExpressionKind.SYMBOL && !tempRegistry.isVariable(arg1.symbol) && tempRegistry.isVariable(arg2.symbol)) {
                        const t = expr1;
                        expr1 = expr2;
                        expr2 = t;
                    }
                }
            }
            if (expr1.arg.kind === ExpressionKind.SYMBOL && tempRegistry.isVariable(expr1.arg.symbol) && freeQ(expr1.fn, expr1.arg.symbol)) {
                if (fixedPoint || !argsContainsUninferedTemps(tempRegistry, expr1) && !containsUninferedTemps(tempRegistry, expr2)) {
                    addEqualConstraint(expr1.fn, makeLambda(expr2, expr1.arg, typeOfExpression0(expr1.fn)), con.source);
                    addEqualConstraint(expr1.type, typeOfExpression0(expr2), con.source);
                    return true;
                }
            }
        }
        if (expr1.kind === ExpressionKind.FN_TYPE && expr2.kind === ExpressionKind.FN_TYPE) {
            let output2 = expr2.outputType;
            if (expr1.arg !== void 0 && expr2.arg !== void 0 && expr1.arg.symbol !== expr2.arg.symbol) {
                output2 = replaceOneSymbol(output2, expr2.arg.symbol, expr1.arg);
            }
            addEqualConstraint(expr1.inputType, expr2.inputType, con.source);
            addEqualConstraint(expr1.outputType, output2, con.source);
            return true;
        }
        if (sameQ(expr1, expr2)) {
            return true;
        }
        if (changed) {
            logger.info(() => 'changed');
            addEqualConstraint(expr1, expr2, con.source);
        } else {
            logger.info(() => 'unchanged');
            equalConstraints.push(con);
        }
        return changed;
    }

    function pollAllHIR() {
        let done = false;
        let changed = false;
        while (!done) {
            done = true;
            for (let i = 0; i < hirRegs.length; i++) {
                const resolved = hirResolvedData[i];
                const hasValue = resolved.value !== void 0;
                const completeDone = resolved.completeDone;
                if (pollHIR(i as HIRReg)) {
                    if (!hasValue && resolved.value !== void 0) {
                        logger.info(() => `resolved(%${i}): ${inputForm(tempRegistry, typeOfExpression0(resolved.value!))} = ${inputForm(tempRegistry, resolved.value!)}`);
                    }
                    if (!completeDone && resolved.completeDone) {
                        logger.info(() => `completeDone(%${i})`);
                    }
                    done = false;
                    changed = true;
                }
            }
        }
        return changed;
    }

    function dumpEqualConstraints(title: string) {
        logger.info(() => {
            const ret: string[] = [title + ': equal constraints:'];
            for (const con of equalConstraints) {
                ret.push(`    ${inputForm(tempRegistry, con.expr1)} === ${inputForm(tempRegistry, con.expr2)}, source: ${con.source}`);
            }
            ret.push('end');
            return ret;
        });
    }

    function evaluateEqualConstraints(fixedPoint: boolean) {
        dumpEqualConstraints('before');
        let done = false;
        let changed = false;
        while (!done) {
            done = true;
            const ec = equalConstraints.slice(0);
            equalConstraints.length = 0;
            for (const con of ec) {
                if (evaluateEqualConstraint(con, fixedPoint)) {
                    if (fixedPoint) {
                        fixedPoint = false;
                    }
                    done = false;
                    changed = true;
                }
            }
        }
        dumpEqualConstraints('after');
        return changed;
    }

    function updateNoEqualConstraintsMarker() {
        for (const data of hirResolvedData) {
            data.noEqualConstraints = true;
        }
        for (const con of equalConstraints) {
            hirResolvedData[con.source].noEqualConstraints = false;
        }
    }

    function substituesTempsInHIR() {
        for (const data of hirResolvedData) {
            if (data.type !== void 0) {
                data.type = tempRegistry.substituteTemps(data.type);
            }
            if (data.value !== void 0) {
                data.value = tempRegistry.substituteTemps(data.value);
            }
        }
    }

    function iterate(fixedPoint: boolean) {
        let changed = false;
        let now = new Date();
        const timer = new Timer();
        if (!fixedPoint) {
            changed = pollAllHIR() || changed;
        }
        logger.info(() => `poll HIR took ${timer.elapsed()}ms`);
        changed = evaluateEqualConstraints(fixedPoint) || changed;
        logger.info(() => `equal contraints took ${timer.elapsed()}ms`);
        if (changed) {
            updateNoEqualConstraintsMarker();
            substituesTempsInHIR();
            tempRegistry.substituteAllTemps();
            logger.info(() => `refresh took ${timer.elapsed()}ms`);
        }
        return changed;
    }

    function run() {
        let iterations = 0;
        let fixedIterations = 0;
        while (true) {
            logger.info(() => `iteration ${iterations}`);
            while (iterate(false)) {
                iterations++;
            }
            logger.info(() => `fixed iteration ${iterations}`);
            if (!iterate(true)) {
                fixedIterations++;
                const s = new Date();
                break;
            }
        }

        for (const con of equalConstraints) {
            diagnostics.push({kind: TypeCheckDiagnosticKind.UNEQUAL, con});
        }
        tempRegistry.forEachLocalSymbol((symbol, entry) => {
            if (0 !== (entry.flags & SymbolFlags.MUST_HAVE_VALUE) && entry.value === void 0 && (entry.downValues === void 0 || entry.downValues.length === 0)) {
                diagnostics.push({kind: TypeCheckDiagnosticKind.UNINFERRED, symbol});
            }
        });
        if (diagnostics.length > 0) {
            logger.info(() => tempRegistry.dump());
            return;
        }
        logger.info(() => `done in ${iterations} iterations and ${fixedIterations} fixed iterations`);
        registry.mergeFrom(tempRegistry);
        registry.substituteAllTemps();
        registry.cleanupTemps();
    }
}

function collectRules(reg: SymbolRegistry, expr: CallExpression) {
    const [fn, args] = collectFnArgs(expr);
    const rules: [Expression, Expression][] = [];
    for (const arg of args) {
        if (arg.kind === ExpressionKind.SYMBOL) {
            const entry = reg.getSymbolEntry(arg.symbol);
            if (entry.upValues) {
                rules.push(...entry.upValues);
            }
        } else if (arg.kind === ExpressionKind.CALL) {
            const fn2 = getFn(arg);
            if (fn2.kind === ExpressionKind.SYMBOL) {
                const entry = reg.getSymbolEntry(fn2.symbol);
                if (entry.upValues) {
                    rules.push(...entry.upValues);
                }
            }
        }
    }
    if (fn.kind === ExpressionKind.SYMBOL) {
        const entry = reg.getSymbolEntry(fn.symbol);
        if (entry.downValues) {
            rules.push(...entry.downValues);
        }
    }
    return rules;
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
                for (const [lhs, rhs] of collectRules(this.reg, expr)) {
                    const reps = matchPattern(this.reg, lhs, expr);
                    if (reps !== null) {
                        self.doActions(self._evaluate(replaceSymbols(rhs, reps)));
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
