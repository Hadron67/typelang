import { HIRCall, HIRFnType, HIRHost, HIRKind, HIRReg, HIRSymbolFlags } from "./irgen";
import { StructVariant, SourceRange, asSourceRange } from "./parser";
import { assert, IndexedMap, Mutable, panic, popReversed, pushReversed } from "./util";

export const enum ExpressionKind {
    SYMBOL,
    STRING,
    NUMBER,
    UNIVERSE,
    LAMBDA,
    CALL,
    FN_TYPE,
    PENDING,
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
    | PendingValueExpression
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
    readonly arg?: Symbol;
    readonly body: Expression;
    readonly type: Expression;
    readonly loc?: SourceRange;
}

export interface FnTypeExpression {
    readonly kind: ExpressionKind.FN_TYPE;
    readonly arg?: Symbol;
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

export interface UnknownVariableData {
    type: Expression;
    value?: Expression;
}

export interface PendingValueExpression {
    readonly kind: ExpressionKind.PENDING;
}

export interface SymbolData {
    readonly name?: string;
    readonly loc?: SourceRange;
    readonly parent: Symbol | null;
    subSymbols?: Map<string, Symbol>;
    type?: Expression;
    value?: Expression;
}

export function se(symbol: Symbol): SymbolExpression {
    return {kind: ExpressionKind.SYMBOL, symbol};
}

export class BuiltinSymbols {
    readonly builtin: Symbol;
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
        this.builtin = reg.emitSymbol({name: 'builtin', parent: null});
        this.type = reg.emitSymbol({name: 'Type', parent: this.builtin});

        const makeType = (name: string): Symbol => {
            return reg.emitSymbol({name, type: this.u0, parent: this.builtin});
        }

        this.levelType = makeType('Level');
        this.levelSucc = reg.emitSymbol({
            name: 'succ',
            type: {kind: ExpressionKind.FN_TYPE, inputType: se(this.levelType), outputType: se(this.levelType), typeLevel: this.level0, color: 0},
            parent: this.builtin,
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
        this.levelMax = reg.emitSymbol({name: 'max', type: this.levelMaxType, parent: this.builtin});

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
        let entry = this.symbols[s];
        const parts: string[] = [entry.name ?? `$${s}`];
        while (entry.parent !== null) {
            entry = this.getSymbolEntry(entry.parent);
            parts.unshift(entry.name ?? `$${s}`);
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
}

export function typeOfExpression(expr: Expression, reg: SymbolRegistry, builtins: BuiltinSymbols): Expression {
    switch (expr.kind) {
        case ExpressionKind.SYMBOL: return reg.getSymbolEntry(expr.symbol).type ?? se(builtins.untyped);
        case ExpressionKind.CALL:
        case ExpressionKind.LAMBDA: return expr.type;
        case ExpressionKind.FN_TYPE: return {kind: ExpressionKind.UNIVERSE, level: expr.typeLevel};
        case ExpressionKind.NUMBER: return se(expr.isLevel ? builtins.levelType : builtins.numberType);
        case ExpressionKind.STRING: return se(builtins.stringType);
        case ExpressionKind.UNIVERSE: return {
            kind: ExpressionKind.UNIVERSE,
            level: makeSucc(expr.level, builtins),
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
    }
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
                const [fn, args] = collectFnArgs(expr);
                const colors = collectFnTypeColors(fn);
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
                        const color = i >= colors.length ? colors[i] : 0;
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
                const arg = t.arg !== void 0 ? registry.getSymbolDisplayName(t.arg) : void 0;
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
                const arg = t.arg !== void 0 ? registry.getSymbolDisplayName(t.arg) : void 0;
                todo.push(stack => {
                    stack.push((arg !== void 0 ? '\\' + arg : '\\_') + ' ' + stack.pop()!);
                }, t.body);
                break;
            }
            case ExpressionKind.NUMBER: stack.push(t.value.toString()); break;
            case ExpressionKind.STRING: stack.push(`"${t.value}"`); break;
            default: panic();
        }
    }
    assert(stack.length === 1);
    return stack[0];
}

export function mapExpression(expr: Expression, mapper: (expr: Expression) => Expression | null) {
    const todo: (Expression | ((stack: Expression[]) => Expression))[] = [];
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
                todo.push(stack => {
                    const typeLevel = stack.pop()!;
                    const outputType = stack.pop()!;
                    const inputType = stack.pop()!;
                    if (inputType !== t.inputType || outputType !== t.outputType || typeLevel !== t.typeLevel) {
                        return {kind: ExpressionKind.FN_TYPE, inputType, outputType, arg: t.arg, color, typeLevel, loc};
                    } else {
                        return t;
                    }
                }, t.typeLevel, t.outputType, t.inputType);
                break;
            }
            case ExpressionKind.LAMBDA: {
                todo.push(stack => {
                    const type = stack.pop()!;
                    const body = stack.pop()!;
                    if (body !== t.body || type !== t.type) {
                        return {kind: ExpressionKind.LAMBDA, arg: t.arg, body, type, loc: t.loc};
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

function checkFnTypeColor(expr: Expression, color: number) {
    while (expr.kind === ExpressionKind.FN_TYPE && expr.color !== color) {
        expr = expr.outputType;
    }
    return expr.kind === ExpressionKind.FN_TYPE;
}

export function checkTypes(registry: SymbolRegistry, builtins: BuiltinSymbols, hir: HIRHost) {
    const hirRegs = hir.regs;
    const tempRegistry = new SymbolRegistry(registry);
    const equalConstraints: [Expression, Expression][] = [];

    function typeOfExpression0(expr: Expression) {
        return typeOfExpression(expr, tempRegistry, builtins);
    }

    function emitUnknown(type: Expression): SymbolExpression {
        const ret = tempRegistry.emitSymbol({type, parent: null, value: {kind: ExpressionKind.PENDING}});
        return se(ret);
    }

    function emitUnknownType() {
        return emitUnknown(emitUnknown(se(builtins.levelType)));
    }

    function pollHIR(r: HIRReg) {
        const data = hirRegs[r];
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
                    inputType = emitUnknownType();
                }
                const inputLevel = emitUnknown(se(builtins.levelType));
                const outputLevel = emitUnknown(se(builtins.levelType));
                equalConstraints.push(
                    [typeOfExpression0(inputType), {kind: ExpressionKind.UNIVERSE, level: inputLevel}],
                    [typeOfExpression0(bodyType), {kind: ExpressionKind.UNIVERSE, level: outputLevel}],
                );
                data.resolvedValue = {
                    kind: ExpressionKind.LAMBDA,
                    arg: arg?.symbol,
                    body,
                    type: {
                        kind: ExpressionKind.FN_TYPE,
                        color: 0,
                        inputType,
                        outputType: bodyType,
                        arg: arg?.symbol,
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
                const entry: Mutable<SymbolData> = {parent, name: value.name, loc: data.loc};
                if (0 !== (value.flags & HIRSymbolFlags.HAS_TYPE)) {
                    entry.type = {kind: ExpressionKind.PENDING};
                }
                if (0 !== (value.flags & HIRSymbolFlags.HAS_ASSIGNMENT)) {
                    entry.value = {kind: ExpressionKind.PENDING};
                }
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
                const entry = tempRegistry.getSymbolEntry(symbol.symbol);
                if (entry.type !== void 0 && entry.type.kind !== ExpressionKind.PENDING) {
                    equalConstraints.push([entry.type, type]);
                }
                if (entry.value !== void 0 && entry.value.kind !== ExpressionKind.PENDING) {
                    equalConstraints.push([type, typeOfExpression0(entry.value)]);
                }
                entry.type = type;
                break;
            }
            case HIRKind.SYMBOL_ASSIGN: {
                const symbol = hirRegs[value.symbol].resolvedValue;
                const v = hirRegs[value.value].resolvedValue;
                if (symbol === void 0 || v === void 0) {
                    return false;
                }
                assert(symbol.kind === ExpressionKind.SYMBOL);
                const entry = tempRegistry.getSymbolEntry(symbol.symbol);
                if (entry.type !== void 0 && entry.type.kind !== ExpressionKind.PENDING) {
                    equalConstraints.push([entry.type, typeOfExpression0(v)]);
                }
                if (entry.value !== void 0 && entry.value.kind !== ExpressionKind.PENDING) {
                    equalConstraints.push([v, entry.value]);
                }
                entry.value = v;
                break;
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
        }
    }

    function pollFnType(value: HIRFnType): Expression | null {
        const inputType = hirRegs[value.inputType].resolvedValue;
        const outputType = hirRegs[value.outputType].resolvedValue;
        if (inputType === void 0 || outputType === void 0) return null;
        let arg: Symbol | undefined = void 0;
        if (value.arg !== void 0) {
            const a = hirRegs[value.arg].resolvedValue;
            if (a === void 0 || a.kind !== ExpressionKind.SYMBOL) return null;
            arg = a.symbol;
        }
        const inputLevel = emitUnknown(se(builtins.levelType));
        const outputLevel = emitUnknown(se(builtins.levelType));
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
            const temp = emitUnknown(fnType.inputType);
            let nextType: Expression = fnType.outputType;
            if (fnArg !== void 0) {
                nextType = replaceOneSymbol(nextType, fnArg, temp);
            }
            ret = {kind: ExpressionKind.CALL, fn: ret, arg: temp, type: nextType};
            fnType = nextType;
        }
        assert(fnType.kind === ExpressionKind.FN_TYPE);
        equalConstraints.push([fnType.inputType, argType]);
        let retType = fnType.outputType;
        if (fnType.arg !== void 0) {
            retType = replaceOneSymbol(retType, fnType.arg, arg);
        }
        return {
            kind: ExpressionKind.CALL,
            fn: ret,
            arg,
            type: retType,
        };
    }

    function evaluateEqualConstraint(con: [Expression, Expression]) {
        let [expr1, expr2] = con;
        if (expr1.kind > expr2.kind) {
            const t = expr1;
            expr1 = expr2;
            expr2 = t;
        }
        
    }
}

type EvaluatorAction = (self: Evaluator) => void;
export class Evaluator {
    private readonly stack: Expression[] = [];
    private readonly todo: EvaluatorAction[] = [];
    constructor(readonly reg: SymbolRegistry) {}
    private doActions(...actions: EvaluatorAction[]) {
        pushReversed(this.todo, actions);
    }
    private _evaluate(expr: Expression): EvaluatorAction {
        return self => {
            switch (expr.kind) {
                case ExpressionKind.CALL: {
                    self.doActions(self._evaluate(expr.fn), self._evaluate(expr.arg), self => {
                        const arg = self.stack.pop()!;
                        const fn = self.stack.pop()!;
                        if (fn.kind === ExpressionKind.LAMBDA) {
                            if (fn.arg !== void 0) {
                                self.doActions(self._evaluate(replaceOneSymbol(fn.body, fn.arg, arg)));
                            } else {
                                self.stack.push(fn.body);
                            }
                        } else {

                        }
                    });
                }
            }
        };
    }
}