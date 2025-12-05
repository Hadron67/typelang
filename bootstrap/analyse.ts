import { generateHIRDependencies, HIRCall, HIRFnType, HIRHost, HIRKind, HIRLambda, HIRMemberAccess, HIRReg, HIRRegData, HIRSymbol, HIRSymbolRule } from "./irgen";
import { asSourceRange, SourceRange } from "./parser";
import { assert, constArray, Either, Logger, makeArray, Mutable, panic, popReversed, PtrNumbering, pushReversed, Timer } from "./util";

export const enum ExpressionKind {
    SYMBOL,
    VARIABLE,
    STRING,
    NUMBER,
    LAMBDA,
    CALL,
    FN_TYPE,
    UNKNOWN,
}

export type Symbol = number & { __marker: Symbol };
export type VariableId = number & { __marker: VariableId };

export const enum SymbolFlags {
    ALLOW_DEF_TYPE = 1,
    ALLOW_ASSIGNMENT = 2,
    ALLOW_DOWN_VALUE = 4,
    ALLOW_UP_VALUE = 8,
    AUTO_REMOVE = 16,
    HOLD = 32,
}

export const SYMBOL_FLAG_NAMES = ['AllowDefType', 'AllowAssigment', 'AllowDownValue', 'AllowUpValue', 'AutoRemove', 'Hold'];

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
    | UnknownExpression
    | VariableExpression
    | StringExpression
    | NumberExpression
    | LambdaExpression
    | FnTypeExpression
    | CallExpression
;

export interface SymbolExpression {
    readonly kind: ExpressionKind.SYMBOL;
    readonly loc?: SourceRange;
    readonly parent?: SymbolExpression;
    readonly name?: string;
    readonly evaluator?: (args: Expression[]) => Expression | undefined;
    readonly flags: number;
    type?: Expression;
    value?: Expression;
    subSymbols?: Map<string, SymbolExpression>;
    downValues?: [Expression, Expression][];
    upValues?: [Expression, Expression][];
}

export interface VariableExpression {
    readonly kind: ExpressionKind.VARIABLE;
    readonly defaultType: Expression;
    readonly name?: string;
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
    readonly arg?: VariableExpression;
    readonly argType: Expression;
    readonly body: Expression;
    readonly color: number;
    readonly loc?: SourceRange;
}

export interface FnTypeExpression {
    readonly kind: ExpressionKind.FN_TYPE;
    readonly arg?: VariableExpression;
    readonly inputType: Expression;
    readonly outputType: Expression;
    readonly color: number;
    readonly loc?: SourceRange;
}

export interface CallExpression {
    readonly kind: ExpressionKind.CALL;
    readonly fn: Expression;
    readonly arg: Expression;
    readonly color: number;
    readonly loc?: SourceRange;
}

export interface UnknownExpression {
    readonly kind: ExpressionKind.UNKNOWN;
    readonly type?: Expression;
    readonly isPattern: boolean;
    readonly excludedVariables: Set<VariableExpression>;
    value?: Expression;
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
    UNRESOLVED_CONSTRAINT,
    UNINFERRED,
}

export type TypeCheckDiagnostic = TypeCheckDiagnosticUnequal | TypeCheckDiagnosticUninferred;

export interface TypeCheckDiagnosticUnequal {
    readonly kind: TypeCheckDiagnosticKind.UNRESOLVED_CONSTRAINT;
    readonly con: Constraint;
}

export interface TypeCheckDiagnosticUninferred {
    readonly kind: TypeCheckDiagnosticKind.UNINFERRED;
    readonly expr: UnknownExpression;
}

export function renderTypeCheckDiagnostic(d: TypeCheckDiagnostic, reg: ExpressionStringifier) {
    switch (d.kind) {
        case TypeCheckDiagnosticKind.UNRESOLVED_CONSTRAINT: return [`unresolved constraint ${dumpConstraint(d.con, reg)}`];
        case TypeCheckDiagnosticKind.UNINFERRED: return [`uninferred symbol ${reg.stringify(d.expr)}`];
    }
}

export function setParent(expr: SymbolExpression) {
    const p = expr.parent;
    if (p !== void 0 && expr.name !== void 0) {
        if (p.subSymbols === void 0) {
            p.subSymbols = new Map();
        }
        p.subSymbols.set(expr.name, expr);
    }
}

function isLevel(expr: Expression): expr is NumberExpression {
    return expr.kind === ExpressionKind.NUMBER && expr.isLevel;
}

function evaluateLevelMax(a1: Expression, a2: Expression): Expression | undefined {
    if (!isLevel(a1) && isLevel(a2)) {
        const t = a1;
        a1 = a2;
        a2 = t;
    }
    if (isLevel(a1)) {
        if (isLevel(a2)) {
            return {kind: ExpressionKind.NUMBER, isLevel: true, value: Math.max(a1.value, a2.value)};
        } else if (a1.value === 0) {
            return a2;
        }
    }
}

export class BuiltinSymbols {
    readonly builtin: SymbolExpression;
    readonly root: SymbolExpression;
    readonly type: SymbolExpression;
    readonly level0: NumberExpression = {kind: ExpressionKind.NUMBER, isLevel: true, value: 0};
    readonly levelType: SymbolExpression;
    readonly levelSucc: SymbolExpression;
    readonly levelMax: SymbolExpression;

    readonly untyped: SymbolExpression;
    readonly numberType: SymbolExpression;
    readonly stringType: SymbolExpression;
    readonly unitType: SymbolExpression;
    readonly unit: SymbolExpression;
    constructor() {
        const subSymbol = (parent: SymbolExpression, name: string, type: Expression | undefined): SymbolExpression => {
            if (parent.subSymbols === void 0) {
                parent.subSymbols = new Map();
            }
            const ret: SymbolExpression = {kind: ExpressionKind.SYMBOL, name, parent, type, flags: 0};
            parent.subSymbols.set(name, ret);
            return ret;
        };
        this.builtin = {kind: ExpressionKind.SYMBOL, name: 'builtin', flags: 0};
        this.levelType = subSymbol(this.builtin, "Level", void 0);
        this.levelSucc = {
            kind: ExpressionKind.SYMBOL,
            name: 'succ',
            type: {kind: ExpressionKind.FN_TYPE, inputType: this.levelType, outputType: this.levelType, color: 0},
            flags: 0,
            parent: this.levelType,
            evaluator(args) {
                const a = args[0];
                if (a.kind === ExpressionKind.NUMBER && a.isLevel) {
                    return {kind: ExpressionKind.NUMBER, isLevel: true, value: a.value + 1};
                }
            },
        };
        setParent(this.levelSucc);
        this.levelMax = {
            kind: ExpressionKind.SYMBOL,
            name: 'max',
            type: {
                kind: ExpressionKind.FN_TYPE,
                color: 0,
                inputType: this.levelType,
                outputType: {
                    kind: ExpressionKind.FN_TYPE,
                    color: 0,
                    inputType: this.levelType,
                    outputType: this.levelType,
                },
            },
            flags: 0,
            parent: this.levelType,
            evaluator(args) {
                if (args.length < 2) return void 0;
                const [a1, a2] = args;
                return evaluateLevelMax(a1, a2);
            },
        };
        setParent(this.levelMax);

        this.root = {kind: ExpressionKind.SYMBOL, name: 'root', flags: 0};
        this.type = subSymbol(this.builtin, "Type", void 0);
        {
            const i: VariableExpression = {
                kind: ExpressionKind.VARIABLE,
                name: 'i',
                defaultType: this.levelType,
            };
            // (i: Level) -> Type(succ(i))
            this.type.type = {
                kind: ExpressionKind.FN_TYPE,
                inputType: this.levelType,
                arg: i,
                outputType: {
                    kind: ExpressionKind.CALL,
                    fn: this.type,
                    arg: {
                        kind: ExpressionKind.CALL,
                        fn: this.levelSucc,
                        arg: i,
                        color: 0,
                    },
                    color: 0,
                },
                color: 0,
            };
        }

        const u0: CallExpression = {kind: ExpressionKind.CALL, fn: this.type, arg: this.level0, color: 0};
        const makeType = (name: string): SymbolExpression => {
            return subSymbol(this.builtin, name, u0);
        }
        this.levelType.type = u0;

        this.untyped = makeType('untyped');
        this.numberType = makeType('number');
        this.stringType = makeType('string');
        this.unitType = makeType('void');
        this.unit = makeType('void');
    }
    getInitialScope() {
        const ret = new Map<string, SymbolExpression>();
        ret.set('Type', this.type);
        ret.set('builtin', this.builtin);
        return ret;
    }
    makeLevelMax(a1: Expression, a2: Expression): Expression {
        return evaluateLevelMax(a1, a2) ?? {
            kind: ExpressionKind.CALL,
            fn: {
                kind: ExpressionKind.CALL,
                fn: this.levelMax,
                color: 0,
                arg: a1,
            },
            arg: a2,
            color: 0,
        };
    }
    makeLevelSucc(level: Expression): Expression {
        if (level.kind === ExpressionKind.NUMBER && level.isLevel) {
            return {kind: ExpressionKind.NUMBER, isLevel: true, value: level.value + 1};
        } else {
            return {kind: ExpressionKind.CALL, color: 0, fn: this.levelSucc, arg: level}
        }
    }
    makeUniverse(level: Expression): CallExpression {
        return {kind: ExpressionKind.CALL, fn: this.type, arg: level, color: 0};
    }
    makeUnknownUniverse() {
        return this.makeUniverse(makeUnknown(this.levelType, false));
    }
}

function makeUnknown(type: Expression, isPattern: boolean): UnknownExpression {
    return {
        kind: ExpressionKind.UNKNOWN,
        isPattern,
        excludedVariables: new Set(),
        type,
    };
}

function makeUnknownType(builtins: BuiltinSymbols): UnknownExpression {
    return makeUnknown(builtins.makeUniverse(makeUnknown(builtins.levelType, false)), false);
}

export function getCachedType(cache: WeakMap<Expression, Expression>, expr: Expression) {
    const type = cache.get(expr);
    if (type !== void 0) {
        const type2 = unwrapUnknown(type);
        if (type !== type2) {
            cache.set(expr, type2);
        }
        return type2;
    }
    return void 0;
}

type TypeSolverAction = (self: TypeSolver) => void;
export class TypeSolver {
    private readonly stack: Expression[] = [];
    private readonly todo: TypeSolverAction[] = [];
    private readonly variableTypes = new Map<VariableExpression, Expression>();
    constructor(private readonly cache: WeakMap<Expression, Expression>, private readonly builtins: BuiltinSymbols, private readonly csolver: ConstraintSolver) {}
    setType(expr: Expression, type: Expression) {
        this.cache.set(expr, type);
    }
    private doActions(...actions: TypeSolverAction[]) {
        pushReversed(this.todo, actions);
    }
    private _getType(expr: Expression): TypeSolverAction {
        return self => {
            const builtins = self.builtins;
            const cached = getCachedType(this.cache, expr);
            if (cached !== void 0) {
                self.stack.push(cached);
                return;
            }
            switch (expr.kind) {
                case ExpressionKind.STRING: self.stack.push(builtins.stringType); break;
                case ExpressionKind.NUMBER: self.stack.push(expr.isLevel ? builtins.levelType : builtins.numberType); break;
                case ExpressionKind.UNKNOWN:
                    if (expr.value !== void 0) {
                        self.doActions(self._getType(expr.value));
                    } else if (expr.type !== void 0) {
                        self.stack.push(expr.type);
                    } else {
                        const type: UnknownExpression = {kind: ExpressionKind.UNKNOWN, isPattern: false, excludedVariables: new Set()};
                        expr.excludedVariables.forEach(v => type.excludedVariables.add(v));
                        self.csolver.add({kind: ConstraintKind.TYPEOF, target: type, expr});
                        self.stack.push(type);
                    }
                    break;
                case ExpressionKind.VARIABLE: self.stack.push(self.variableTypes.get(expr) ?? expr.defaultType); break;
                case ExpressionKind.SYMBOL: {
                    self.stack.push(expr.type ?? builtins.untyped);
                    break;
                }
                case ExpressionKind.FN_TYPE: {
                    self.doActions(self._getType(expr.inputType), self._getType(expr.outputType), self => {
                        const outputTypeType = self.stack.pop()!;
                        const inputTypeType = self.stack.pop()!;
                        const ret: UnknownExpression = {kind: ExpressionKind.UNKNOWN, isPattern: false, excludedVariables: new Set()};
                        self.csolver.add({kind: ConstraintKind.FN_TYPE_TYPE, target: ret, type1: inputTypeType, type2: outputTypeType});
                        self.cache.set(expr, ret);
                        self.stack.push(ret);
                    });
                    break;
                }
                case ExpressionKind.CALL: {
                    self.doActions(self._getType(expr.fn), self => {
                        const fnType = unwrapUnknown(self.stack.pop()!);
                        assert(fnType.kind === ExpressionKind.FN_TYPE);
                        let type = fnType.outputType;
                        if (fnType.arg !== void 0) {
                            type = replaceScopeVariable(type, fnType.arg, expr.arg, self.csolver) ?? panic();
                        }
                        self.cache.set(expr, type);
                        self.stack.push(type);
                    });
                    break;
                }
                case ExpressionKind.LAMBDA: {
                    self.doActions(self._getType(expr.body), self => {
                        const bodyType = self.stack.pop()!;
                        const type: FnTypeExpression = {kind: ExpressionKind.FN_TYPE, inputType: expr.argType, arg: expr.arg, outputType: bodyType, color: expr.color};
                        self.cache.set(expr, type);
                        self.stack.push(type);
                    });
                    break;
                }
            }
        };
    }
    run(expr: Expression) {
        this.stack.length = 0;
        this.todo.length = 0;
        this.doActions(this._getType(expr));
        while (this.todo.length > 0) {
            this.todo.pop()!(this);
        }
        assert(this.stack.length === 1);
        return this.stack.pop()!;
    }
}

export function collectFnArgs(expr: CallExpression): [Expression, Expression[], number[]] {
    const args: Expression[] = [];
    const colors: number[] = [];
    let expr0: Expression = unwrapUnknown(expr);
    while (expr0.kind === ExpressionKind.CALL) {
        args.unshift(expr0.arg);
        colors.unshift(expr0.color);
        expr0 = unwrapUnknown(expr0.fn);
    }
    assert(args.length > 0);
    return [expr0, args, colors];
}

export function getFn(expr: CallExpression) {
    let expr0: Expression = unwrapUnknown(expr);
    while (expr0.kind === ExpressionKind.CALL) {
        expr0 = unwrapUnknown(expr0.fn);
    }
    return expr0;
}

export function collectFnTypeColors(expr: Expression) {
    const colors: number[] = [];
    expr = unwrapUnknown(expr);
    while (expr.kind === ExpressionKind.FN_TYPE) {
        colors.push(expr.color);
        expr = expr.outputType;
    }
    return colors;
}

export function unwrapUnknown(expr: Expression) {
    while (expr.kind === ExpressionKind.UNKNOWN && expr.value !== void 0) {
        expr = expr.value;
    }
    return expr;
}

export function unwrapUnknownNullable(expr: Expression | undefined) {
    return expr === void 0 ? void 0 : unwrapUnknown(expr);
}

export class ExpressionStringifier {
    private readonly unknownNumbers = new PtrNumbering<UnknownExpression>();
    private readonly symbolNumbers = new PtrNumbering<SymbolExpression>();
    private readonly varialbeNumbers = new PtrNumbering<VariableExpression>();
    stringifySymbol(s: SymbolExpression) {
        const parts: string[] = [];
        while (s.parent !== void 0) {
            parts.unshift(s.name ?? `$${this.symbolNumbers.get(s)}`);
            s = s.parent;
        }
        parts.unshift(s.name ?? `$${this.symbolNumbers.get(s)}`);
        return parts.join('.');
    }
    stringifyVariable(expr: VariableExpression) {
        return (expr.name ?? '') + '$' + this.varialbeNumbers.get(expr);
    }
    stringify(expr: Expression) {
        const stack: string[] = [];
        const todo: (Expression | ((stack: string[]) => void))[] = [expr];
        while (todo.length > 0) {
            let t = todo.pop()!;
            if (typeof t === 'function') {
                t(stack);
                continue;
            }
            t = unwrapUnknown(t);
            switch (t.kind) {
                case ExpressionKind.SYMBOL: stack.push(this.stringifySymbol(t)); break;
                case ExpressionKind.UNKNOWN: {
                    if (t.value !== void 0) {
                        todo.push(t.value);
                    } else {
                        stack.push((t.isPattern ? '?#' : '?') + this.unknownNumbers.get(t));
                    }
                    break;
                }
                case ExpressionKind.VARIABLE: {
                    stack.push((t.name ?? '') + `$${this.varialbeNumbers.get(t)}`);
                    break;
                }
                case ExpressionKind.CALL: {
                    const [fn, args, colors] = collectFnArgs(t);
                    const needParenth = fn.kind !== ExpressionKind.SYMBOL && fn.kind !== ExpressionKind.UNKNOWN;
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
                    const arg = t.arg !== void 0 ? this.stringifyVariable(t.arg) : void 0;
                    const needParenth = t.inputType.kind !== ExpressionKind.SYMBOL && t.inputType.kind !== ExpressionKind.UNKNOWN && t.inputType.kind !== ExpressionKind.VARIABLE && t.inputType.kind !== ExpressionKind.CALL;
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
                    const arg = t.arg !== void 0 ? this.stringifyVariable(t.arg) : void 0;
                    let hasType = false;
                    todo.push(stack => {
                        const body = stack.pop()!;
                        const inputType = stack.pop()!;
                        let argStr = arg ?? '_';
                        if (inputType !== void 0) {
                            argStr = `(${argStr}: ${inputType})`;
                        }
                        stack.push('\\' + argStr + ' ' + body);
                    }, t.body, t.argType);
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
    dumpSymbol(root: SymbolExpression) {
        const todo = [root];
        const ret: string[] = [];
        while (todo.length > 0) {
            const s = todo.pop()!;
            const name = this.stringifySymbol(s);
            if (s.type !== void 0) {
                let line = `${name}: ${this.stringify(s.type)}`;
                if (s.value !== void 0) {
                    line += ` = ${this.stringify(s.value)}`;
                }
                ret.push(line);
            }
            if (s.downValues !== void 0) {
                for (const [lhs, rhs] of s.downValues) {
                    ret.push(`${this.stringify(lhs)} = ${this.stringify(rhs)}`);
                }
            }
            if (s.upValues !== void 0) {
                for (const [lhs, rhs] of s.upValues) {
                    ret.push(`${this.stringify(lhs)} = ${this.stringify(rhs)}`);
                }
            }

            if (s.subSymbols !== void 0) {
                const subSymbols: SymbolExpression[] = [];
                s.subSymbols.forEach(v => subSymbols.push(v));
                pushReversed(todo, subSymbols);
            }
        }
        return ret;
    }
}

function checkFnTypeColor(expr: Expression, color: number) {
    expr = unwrapUnknown(expr);
    while (expr.kind === ExpressionKind.FN_TYPE && expr.color !== color) {
        expr = unwrapUnknown(expr.outputType);
    }
    return expr.kind === ExpressionKind.FN_TYPE;
}

// main purpose of this function is removing unknown expressions
export function copyExpression(expr: Expression) {
    return mapExpression(expr, {
        map(expr, info) {
            info.emit(expr);
        },
        leaveScope() {},
        enterScope() {},
    }) ?? panic();
}

export interface ExpressionVisitor {
    map(v: Expression, info: ExpressionMap): void;
    enterScope(v: VariableExpression, info: ExpressionMap): void;
    leaveScope(v: VariableExpression, info: ExpressionMap): void;
}

type ExpressionMapAction = (self: ExpressionMap) => void;

export class ExpressionMap {
    readonly todo: ExpressionMapAction[] = [];
    terminated = false;
    private readonly stack: Expression[] = [];
    constructor(private readonly mapper: ExpressionVisitor) {}
    doActions(...actions: ExpressionMapAction[]) {
        pushReversed(this.todo, actions);
    }
    map(expr: Expression): ExpressionMapAction {
        return self => {
            const mapper = self.mapper;
            switch (expr.kind) {
                case ExpressionKind.NUMBER:
                case ExpressionKind.STRING:
                case ExpressionKind.SYMBOL:
                case ExpressionKind.VARIABLE: {
                    if (mapper.map) {
                        mapper.map(expr, self);
                    } else {
                        self.stack.push(expr);
                    }
                    break;
                }
                case ExpressionKind.UNKNOWN: {
                    if (expr.value !== void 0) {
                        self.doActions(self.map(expr.value));
                    } else {
                        mapper.map(expr, self);
                    }
                    break;
                }
                case ExpressionKind.CALL: {
                    self.doActions(self.map(expr.fn), self.map(expr.arg), self => {
                        const arg = self.stack.pop()!;
                        const fn = self.stack.pop()!;
                        self.stack.push(fn !== expr.fn || arg !== expr.arg ? {...expr, fn, arg} : expr);
                    });
                    break;
                }
                case ExpressionKind.FN_TYPE: {
                    self.doActions(self.map(expr.inputType), self => {
                        if (expr.arg !== void 0) {
                            self.mapper.enterScope(expr.arg, self);
                        }
                    }, self.map(expr.outputType), self => {
                        const outputType = self.stack.pop()!;
                        const inputType = self.stack.pop()!;
                        if (expr.arg !== void 0) {
                            self.mapper.leaveScope(expr.arg, self);
                        }
                        self.stack.push(inputType !== expr.inputType || outputType !== expr.outputType ? {...expr, inputType, outputType} : expr);
                    });
                    break;
                }
                case ExpressionKind.LAMBDA: {
                    self.doActions(self.map(expr.argType), self => {
                        if (expr.arg !== void 0) {
                            self.mapper.enterScope(expr.arg, self);
                        }
                    }, self.map(expr.body), self => {
                        const body = self.stack.pop()!;
                        const argType = self.stack.pop()!;
                        if (expr.arg !== void 0) {
                            self.mapper.leaveScope(expr.arg, self);
                        }
                        self.stack.push(body !== expr.body || argType !== expr.argType ? {...expr, argType, body} : body);
                    });
                    break;
                }
                default: panic();
            }
        };
    }
    terminate() {
        this.terminated = true;
    }
    emit(expr: Expression) {
        this.stack.push(expr);
    }
    pop() {
        assert(this.stack.length > 0);
        return this.stack.pop()!;
    }
    run(expr: Expression) {
        this.terminated = false;
        this.doActions(this.map(expr));
        while (!this.terminated && this.todo.length > 0) {
            this.todo.pop()!(this);
        }
        if (!this.terminated) {
            assert(this.stack.length === 1);
            return this.stack.pop()!;
        } else return null;
    }
}

export function mapExpression(expr: Expression, mapper: ExpressionVisitor) {
    return new ExpressionMap(mapper).run(expr);
}

export function visitExpression(expr: Expression, visitor: (expr: Expression) => boolean) {
    const todo = [expr];
    while (todo.length > 0) {
        const expr = todo.pop()!;
        if (visitor(expr)) {
            return true;
        }
        switch (expr.kind) {
            case ExpressionKind.SYMBOL:
            case ExpressionKind.VARIABLE:
            case ExpressionKind.UNKNOWN:
            case ExpressionKind.NUMBER:
            case ExpressionKind.STRING:
                break;
            case ExpressionKind.CALL:
                todo.push(expr.arg, expr.fn);
                break;
            case ExpressionKind.FN_TYPE:
                todo.push(expr.outputType, expr.inputType);
                break;
            case ExpressionKind.LAMBDA:
                todo.push(expr.body);
                break;
            default: panic();
        }
    }
    return false;
}

function markExcludedVariable(expr: Expression, v: VariableExpression) {
    visitExpression(expr, expr => {
        if (expr.kind === ExpressionKind.UNKNOWN) {
            expr.excludedVariables.add(v);
        }
        return false;
    });
}

export function replaceScopeVariable(expr: Expression, v: VariableExpression, replacement: Expression, solver: ConstraintSolver | undefined) {
    return mapExpression(expr, {
        enterScope(v, info) {
            markExcludedVariable(replacement, v);
        },
        leaveScope() {},
        map(expr, info) {
            switch (expr.kind) {
                case ExpressionKind.VARIABLE:
                    if (expr === v) {
                        info.emit(replacement);
                        return;
                    }
                    break;
                case ExpressionKind.UNKNOWN:
                    if (!expr.excludedVariables.has(v)) {
                        if (solver !== void 0) {
                            if (expr.type !== void 0) {
                                info.doActions(info.map(expr.type), self => {
                                    self.emit(solver.makeReplaceUnknown(expr, self.pop(), v, replacement));
                                });
                            } else {
                                info.emit(solver.makeReplaceUnknown(expr, void 0, v, replacement));
                            }
                        } else {
                            const v2: UnknownExpression = {kind: ExpressionKind.UNKNOWN, type: expr.type, isPattern: false, excludedVariables: new Set()};
                            expr.excludedVariables.forEach(v => v2.excludedVariables.add(v));
                            info.emit(v2);
                        }
                        return;
                    }
                    break;
            }
            info.emit(expr);
        },
    }) ?? panic();
}

export function replaceScopeVariables(expr: Expression, reps: Map<VariableExpression, Expression>) {
    return mapExpression(expr, {
        enterScope(v) {
            reps.forEach(rep => markExcludedVariable(rep, v));
        },
        leaveScope() {},
        map(expr, info) {
            switch (expr.kind) {
                case ExpressionKind.VARIABLE: {
                    const rep = reps.get(expr);
                    if (rep !== void 0) {
                        info.emit(rep);
                    }
                    break;
                }
                case ExpressionKind.UNKNOWN: {
                    let contains = false;
                    reps.forEach((v, k) => {
                        if (expr.excludedVariables.has(k)) {
                            contains = true;
                        }
                    });
                    if (contains) {
                        info.terminate();
                        return;
                    }
                    break;
                }
            }
            info.emit(expr);
        },
    });
}

export function freeQ(expr: Expression, predicate: (expr: Expression) => boolean) {
    return null !== mapExpression(expr, {
        enterScope() {},
        leaveScope() {},
        map(expr, info) {
            if (predicate(expr)) {
                info.terminate();
                return;
            }
            info.emit(expr);
        },
    });
}

export function variableFreeQ(expr: Expression, variable: VariableExpression) {
    return freeQ(expr, expr => {
        switch (expr.kind) {
            case ExpressionKind.VARIABLE:
                if (expr === variable) {
                    return true;
                }
                break;
            case ExpressionKind.UNKNOWN:
                if (!expr.excludedVariables.has(variable)) {
                    return true;
                }
                break;
        }
        return false;
    });
}

export function canUseEtaReduction(expr: CallExpression) {
    const arg = expr.arg;
    if (arg.kind !== ExpressionKind.VARIABLE) {
        return false;
    }
    let expr0 = expr.fn;
    while (expr0.kind === ExpressionKind.CALL) {
        if (!variableFreeQ(expr0.arg, arg)) {
            return false;
        }
    }
    return true;
}

export function sameQ(expr1: Expression, expr2: Expression) {
    const todo = [expr1, expr2];
    while (todo.length > 0) {
        const expr2 = unwrapUnknown(todo.pop()!);
        const expr1 = unwrapUnknown(todo.pop()!);
        switch (expr1.kind) {
            case ExpressionKind.SYMBOL:
            case ExpressionKind.VARIABLE:
                if (expr1 !== expr2) {
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
                if (expr1.arg !== void 0 && expr2.arg !== void 0 && expr1.arg !== expr2.arg) {
                    output2 = replaceScopeVariable(output2, expr2.arg, expr1.arg, void 0) ?? panic();
                }
                todo.push(expr1.outputType, output2, expr1.inputType, expr2.inputType);
                break;
            }
            case ExpressionKind.LAMBDA: {
                if (expr2.kind !== ExpressionKind.LAMBDA) {
                    return false;
                }
                let body2 = expr2.body;
                if (expr1.arg !== void 0 && expr2.arg !== void 0 && expr1.arg !== expr2.arg) {
                    body2 = replaceScopeVariable(body2, expr2.arg, expr1.arg, void 0) ?? panic();
                }
                todo.push(expr1.body, body2);
                break;
            }
            case ExpressionKind.UNKNOWN: {
                if (expr1 !== expr2) {
                    return false;
                }
                break;
            }
            default: panic();
        }
    }
    return true;
}

export function matchPattern(pattern: Expression, expr: Expression) {
    const reps = new Map<VariableExpression, Expression>();
    const todo = [pattern, expr];
    while (todo.length > 0) {
        const expr = todo.pop()!;
        const pattern = todo.pop()!;
        switch (pattern.kind) {
            case ExpressionKind.STRING:
            case ExpressionKind.NUMBER:
            case ExpressionKind.LAMBDA:
            case ExpressionKind.FN_TYPE:
                if (!sameQ(pattern, expr)) {
                    return null;
                }
                break;
            case ExpressionKind.VARIABLE: {
                const old = reps.get(pattern);
                if (old !== void 0) {
                    if (!sameQ(old, expr)) {
                        return null;
                    }
                } else {
                    reps.set(pattern, expr);
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

interface HIRResolvedData {
    errored: boolean;
    type?: Expression;
    value?: Expression;
}

export const enum ConstraintKind {
    EQUAL,
    EQUAL_WITH_REPLACE,
    FN_TYPE_TYPE,
    TYPEOF,
}

export type Constraint =
    | EqualConstraint
    | EqualWithReplaceConstraint
    | FnTypeTypeConstraint
    | TypeofConstraint
;

export interface EqualConstraint {
    readonly kind: ConstraintKind.EQUAL;
    readonly expr1: Expression;
    readonly expr2: Expression;
}

export interface FnTypeTypeConstraint {
    readonly kind: ConstraintKind.FN_TYPE_TYPE;
    readonly target: UnknownExpression;
    readonly type1: Expression;
    readonly type2: Expression;
}

export interface EqualWithReplaceConstraint {
    readonly kind: ConstraintKind.EQUAL_WITH_REPLACE;
    readonly target: UnknownExpression;
    readonly expr: UnknownExpression;
    readonly variable: VariableExpression;
    readonly replacement: Expression;
}

export interface TypeofConstraint {
    readonly kind: ConstraintKind.TYPEOF;
    readonly target: UnknownExpression;
    readonly expr: UnknownExpression;
}

export class ConstraintSolver {
    private readonly constraints: Constraint[] = [];
    private readonly erroredConstraints: Constraint[] = [];
    private readonly constraintUnknowns = new Set<UnknownExpression>();
    constructor(
        readonly logger: Logger,
        readonly stringifier: ExpressionStringifier,
        readonly builtins: BuiltinSymbols,
        readonly typeCache: WeakMap<Expression, Expression>,
    ) {}
    add(con: Constraint) {
        this.logger.info(() => `add constraint ${dumpConstraint(con, this.stringifier)}`);
        this.scanConstraintUnknonws(con);
        this.constraints.push(con);
    }
    private scanUnknowns(expr: Expression) {
        visitExpression(expr, expr => {
            if (expr.kind === ExpressionKind.UNKNOWN) {
                this.constraintUnknowns.add(expr);
            }
            return false;
        });
    }
    private scanConstraintUnknonws(con: Constraint) {
        switch (con.kind) {
            case ConstraintKind.EQUAL:
                this.scanUnknowns(con.expr1);
                this.scanUnknowns(con.expr2);
                break;
            case ConstraintKind.EQUAL_WITH_REPLACE:
                this.constraintUnknowns.add(con.target);
                this.scanUnknowns(con.replacement);
                break;
            case ConstraintKind.FN_TYPE_TYPE:
                this.constraintUnknowns.add(con.target);
                this.scanUnknowns(con.type1);
                this.scanUnknowns(con.type2);
                break;
            case ConstraintKind.TYPEOF:
                this.constraintUnknowns.add(con.target);
                this.scanUnknowns(con.expr);
                break;
            default: panic();
        }
    }
    containsConstraintUnknown(expr: Expression) {
        return visitExpression(expr, expr => this.constraintUnknowns.has(expr as any));
    }
    addEqualConstraint(expr1: Expression, expr2: Expression) {
        this.add({kind: ConstraintKind.EQUAL, expr1, expr2});
    }
    getType(expr: Expression) {
        const c = this.typeCache.get(expr);
        if (c !== void 0) {
            return c;
        }
        const t = new TypeSolver(this.typeCache, this.builtins, this);
        return t.run(expr) ?? panic();
    }
    setType(expr: Expression, type: Expression) {
        this.typeCache.set(expr, type);
    }
    makeReplaceUnknown(expr: UnknownExpression, type: Expression | undefined, v: VariableExpression, replacement: Expression) {
        const ret: UnknownExpression = {kind: ExpressionKind.UNKNOWN, type, excludedVariables: new Set(), isPattern: false};
        expr.excludedVariables.forEach(v => ret.excludedVariables.add(v));
        this.add({kind: ConstraintKind.EQUAL_WITH_REPLACE, target: ret, expr, variable: v, replacement});
        return ret;
    }
    private evaluateEqualConstraint(expr1: Expression, expr2: Expression) {
        const {logger, stringifier} = this;
        if (expr1.kind !== ExpressionKind.UNKNOWN && expr2.kind === ExpressionKind.UNKNOWN) {
            const t = expr1;
            expr1 = expr2;
            expr2 = t;
        }
        if (expr1.kind === ExpressionKind.UNKNOWN) {
            assert(expr1.value === void 0);
            if (expr2.kind === ExpressionKind.UNKNOWN) {
                assert(expr2.value === void 0);
                if (expr1 === expr2) {
                    return true;
                }
                if (expr1.isPattern && !expr2.isPattern) {
                    const t = expr1;
                    expr1 = expr2;
                    expr2 = t;
                }
            }
            if (!freeQ(expr2, expr => expr === expr1)) {
                logger.info(() => `rejecting unknown assign ${stringifier.stringify(expr1)} = ${stringifier.stringify(expr2)}`);
                return false;
            }
            if (expr1.type !== void 0) {
                this.addEqualConstraint(expr1.type, this.getType(expr2));
            }
            logger.info(() => `setting unknown ${stringifier.stringify(expr1)} = ${stringifier.stringify(expr2)}`);
            expr1.value = expr2;
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
                const [fn1, args1] = collectFnArgs(expr1);
                const [fn2, args2] = collectFnArgs(expr2);
                if (fn1.kind === ExpressionKind.SYMBOL && fn2.kind === ExpressionKind.SYMBOL) {
                    if (args1.length === args2.length && fn1 === fn2) {
                        if (0 === (fn1.flags & (SymbolFlags.ALLOW_DOWN_VALUE | SymbolFlags.ALLOW_ASSIGNMENT))) {
                            for (let i = 0; i < args1.length; i++) {
                                this.addEqualConstraint(args1[i], args2[i]);
                            }
                            if (fn1 !== this.builtins.type) {
                                this.addEqualConstraint(this.getType(expr1), this.getType(expr2));
                            }
                            return true;
                        }
                    }
                }
            }
            let eta1 = canUseEtaReduction(expr1);
            if (!eta1 && expr2.kind === ExpressionKind.CALL && canUseEtaReduction(expr2)) {
                eta1 = true;
                const t = expr1;
                expr1 = expr2;
                expr2 = t;
            }
            // TODO
            // if (eta1) {
            //     this.addEqualConstraint(expr1.fn, makeLambda(expr2, expr1.arg, expr1.fn.));
            // }
            // if (expr1.arg.kind === ExpressionKind.SYMBOL && tempRegistry.isVariable(expr1.arg.symbol) && symbolFreeQ(expr1.fn, expr1.arg.symbol)) {
            //     if (fixedPoint || !argsContainsUninferedTemps(tempRegistry, expr1) && !containsUninferedTemps(tempRegistry, expr2)) {
            //         addEqualConstraint(expr1.fn, makeLambda(expr2, expr1.arg, typeOfExpression0(expr1.fn)), source);
            //         addEqualConstraint(expr1.type, typeOfExpression0(expr2), source);
            //         return true;
            //     }
            // }
        }
        if (expr1.kind === ExpressionKind.FN_TYPE && expr2.kind === ExpressionKind.FN_TYPE) {
            this.addEqualConstraint(expr1.inputType, expr2.inputType);
            let arg: VariableExpression | undefined = void 0;
            if (expr1.arg !== void 0) {
                arg = {kind: ExpressionKind.VARIABLE, defaultType: expr1.inputType};
            } else if (expr2.arg !== void 0) {
                arg = {kind: ExpressionKind.VARIABLE, defaultType: expr2.inputType};
            }
            let output1 = expr1.outputType;
            let output2 = expr2.outputType;
            if (expr1.arg !== void 0) {
                output1 = replaceScopeVariable(output1, expr1.arg, arg ?? panic(), this);
            }
            if (expr2.arg !== void 0) {
                output2 = replaceScopeVariable(output2, expr2.arg, arg ?? panic(), this);
            }
            this.addEqualConstraint(expr1.outputType, output2);
            return true;
        }
        if (expr1.kind === ExpressionKind.LAMBDA && expr2.kind === ExpressionKind.LAMBDA) {
            this.addEqualConstraint(expr1.argType, expr2.argType);
            let body1 = expr1.body;
            let body2 = expr2.body;
            let arg: VariableExpression | undefined = void 0;
            if (expr1.arg !== void 0) {
                arg = {kind: ExpressionKind.VARIABLE, defaultType: expr1.argType};
            } else if (expr2.arg !== void 0) {
                arg = {kind: ExpressionKind.VARIABLE, defaultType: expr2.argType};
            }
            if (expr1.arg !== void 0) {
                body1 = replaceScopeVariable(body1, expr1.arg, arg ?? panic(), this);
            }
            if (expr2.arg !== void 0) {
                body2 = replaceScopeVariable(body2, expr2.arg, arg ?? panic(), this);
            }
            this.addEqualConstraint(body1, body2);
            return true;
        }
        return false;
    }
    private setUnknown(target: UnknownExpression, value: Expression) {
        if (!freeQ(value, expr => expr === target)) {
            this.logger.info(() => `rejecting unknown assign ${this.stringifier.stringify(target)} = ${this.stringifier.stringify(value)}`);
            return false;
        }
        if (target.type !== void 0) {
            this.addEqualConstraint(target.type, this.getType(value));
        }
        if (target.value === void 0) {
            this.logger.info(() => `setting unknown ${this.stringifier.stringify(target)} = ${this.stringifier.stringify(value)}`);
            target.value = value;
        } else {
            this.addEqualConstraint(target.value, value);
        }
        return true;
    }
    private evaluateFnTypeType(expr1: Expression, expr2: Expression): Expression | undefined {
        if (expr1.kind === ExpressionKind.CALL && expr2.kind === ExpressionKind.CALL) {
            if (expr1.fn === this.builtins.type && expr2.fn === this.builtins.type) {
                return {kind: ExpressionKind.CALL, fn: this.builtins.type, arg: this.builtins.makeLevelMax(expr1.arg, expr2.arg), color: 0};
            }
        }
        return void 0;
    }
    private evaluateConstraint(con: Constraint) {
        const {logger, stringifier} = this;
        const evaluator = new Evaluator(this.builtins, this);
        switch (con.kind) {
            case ConstraintKind.EQUAL: {
                const oldExpr1 = con.expr1;
                const oldExpr2 = con.expr2;
                let expr1 = evaluator.evaluate(oldExpr1);
                let expr2 = evaluator.evaluate(oldExpr2);
                if (oldExpr1 !== expr1 || oldExpr2 !== expr2) {
                    logger.info(() => `evaluated expr: ${stringifier.stringify(expr1)} === ${stringifier.stringify(expr2)}`);
                }
                const changed = expr1 !== oldExpr1 || expr2 !== oldExpr2;
                if (this.evaluateEqualConstraint(expr1, expr2)) {
                    return true;
                }
                if (sameQ(expr1, expr2)) {
                    return true;
                }
                if (changed) {
                    logger.info(() => 'changed');
                    this.addEqualConstraint(expr1, expr2);
                } else {
                    logger.info(() => 'unchanged');
                    this.add(con);
                }
                return changed;
            }
            case ConstraintKind.TYPEOF: {
                if (con.expr.value !== void 0 && this.setUnknown(con.target, this.getType(con.expr))) {
                    return true;
                }
                this.add(con);
                return false;
            }
            case ConstraintKind.FN_TYPE_TYPE: {
                const type1 = evaluator.evaluate(con.type1);
                const type2 = evaluator.evaluate(con.type2);
                const changed = type1 !== con.type1 || type2 !== con.type2;
                const type = this.evaluateFnTypeType(type1, type2);
                if (type !== void 0) {
                    if (!this.setUnknown(con.target, type)) {
                        this.erroredConstraints.push(con);
                    }
                    return true;
                }
                if (changed) {
                    con = {...con, type1, type2};
                }
                this.add(con);
                return changed;
            }
            case ConstraintKind.EQUAL_WITH_REPLACE: {
                if (con.expr.value !== void 0) {
                    const rep = replaceScopeVariable(con.expr.value, con.variable, con.replacement, this);
                    if (!this.setUnknown(con.target, rep)) {
                        this.erroredConstraints.push(con);
                    }
                    return true;
                }
                this.add(con);
                return false;
            }
            default: panic();
        }
    }
    evaluate() {
        let ret = false;
        let done = false;
        while (!done) {
            done = true;
            const cons = this.constraints.slice(0);
            this.constraints.length = 0;
            this.constraintUnknowns.clear();
            for (const con of cons) {
                if (this.evaluateConstraint(con)) {
                    done = false;
                    ret = true;
                }
            }
        }
        return ret;
    }
    isUnknownConstraint(expr: UnknownExpression) {
        return this.constraintUnknowns.has(expr);
    }
    dump() {
        const ret: string[] = [];
        for (const con of this.constraints) {
            ret.push(dumpConstraint(con, this.stringifier));
        }
        return ret;
    }
    collectDiagnostics() {
        const ret: TypeCheckDiagnostic[] = [];
        for (const con of this.constraints) {
            ret.push({kind: TypeCheckDiagnosticKind.UNRESOLVED_CONSTRAINT, con});
        }
        for (const con of this.erroredConstraints) {
            ret.push({kind: TypeCheckDiagnosticKind.UNRESOLVED_CONSTRAINT, con});
        }
        return ret;
    }
}

export function dumpConstraint(con: Constraint, reg: ExpressionStringifier) {
    switch (con.kind) {
        case ConstraintKind.EQUAL: return `${reg.stringify(con.expr1)} === ${reg.stringify(con.expr2)}`;
        case ConstraintKind.EQUAL_WITH_REPLACE: return `${reg.stringify(con.target)} === ${reg.stringify(con.expr)} /. ${reg.stringify(con.variable)} -> ${reg.stringify(con.replacement)}`;
        case ConstraintKind.FN_TYPE_TYPE: return `${reg.stringify(con.target)} === #fn-type-type(${reg.stringify(con.type1)}, ${reg.stringify(con.type2)})`;
        case ConstraintKind.TYPEOF: return `${reg.stringify(con.target)} === #typeof(${reg.stringify(con.expr)})`;
        default: panic();
    }
}

const enum PollResult {
    UNCHANGED,
    CHANGED,
    DONE,
}

function convertRule(lhs: Expression, rhs: Expression): [Expression, Expression] {
    lhs = mapExpression(lhs, {
        enterScope(){},
        leaveScope(){},
        map(expr, info) {
            if (expr.kind === ExpressionKind.UNKNOWN && expr.isPattern) {
                assert(expr.value === void 0);
                assert(expr.type !== void 0);
                const s: VariableExpression = {kind: ExpressionKind.VARIABLE, defaultType: expr.type};
                expr.value = s;
                info.emit(s);
                return;
            }
            info.emit(expr);
        }
    }) ?? panic();
    return [lhs, copyExpression(rhs)];
}

type HIRPollAction = (self: HIRSolver) => PollResult;

export class HIRSolver {
    private readonly resolved: HIRResolvedData[];
    private readonly actions: [number, HIRPollAction][];
    constructor(
        private readonly root: SymbolExpression,
        private readonly regs: HIRRegData[],
        private readonly csolver: ConstraintSolver,
    ) {
        this.resolved = makeArray(() => ({completeDone: false, noEqualConstraints: true, errored: false}), regs.length);
        this.actions = makeArray(i => [i, this.pollAction(i)], regs.length);
    }
    private pollCallAction(value: HIRCall, loc: SourceRange | undefined, resolved: HIRResolvedData): HIRPollAction {
        let tmpInsertedFn: Expression | undefined = void 0;
        return self => {
            let ret = PollResult.UNCHANGED;
            if (tmpInsertedFn === void 0) {
                let fn = unwrapUnknownNullable(self.resolved[value.fn].value);
                if (fn === void 0) {
                    return ret;
                }
                let fnType = unwrapUnknown(self.csolver.getType(fn));
                if (!checkFnTypeColor(fnType, value.color)) {
                    return ret;
                }
                while (fnType.kind === ExpressionKind.FN_TYPE && fnType.color !== value.color) {
                    const tmp = makeUnknown(fnType.inputType, value.isPattern);
                    fn = {kind: ExpressionKind.CALL, fn, arg: tmp, color: fnType.color};
                    fnType = self.csolver.getType(fn);
                }
                tmpInsertedFn = fn;
                ret = PollResult.CHANGED;
            }
            const fnType = self.csolver.getType(tmpInsertedFn);
            assert(fnType.kind === ExpressionKind.FN_TYPE);
            const arg = self.resolved[value.arg];
            if (arg.value === void 0) {
                if (arg.type === void 0) {
                    arg.type = fnType.inputType;
                }
                return ret;
            }
            this.csolver.addEqualConstraint(this.csolver.getType(arg.value), fnType.inputType);
            resolved.value = {kind: ExpressionKind.CALL, fn: tmpInsertedFn, arg: arg.value, color: value.color, loc};
            return PollResult.DONE;
        };
    }
    private pollFnTypeAction(value: HIRFnType, loc: SourceRange | undefined, resolved: HIRResolvedData): HIRPollAction {
        return self => {
            const inputType = self.resolved[value.inputType].value;
            const outputType = self.resolved[value.outputType].value;
            if (inputType === void 0 || outputType === void 0) {
                return PollResult.UNCHANGED;
            }
            let arg: VariableExpression | undefined = void 0;
            if (value.arg !== void 0) {
                const arg0 = self.resolved[value.arg].value;
                if (arg0 === void 0) {
                    return PollResult.UNCHANGED;
                }
                assert(arg0.kind === ExpressionKind.VARIABLE);
                arg = arg0;
            }
            resolved.value = {
                kind: ExpressionKind.FN_TYPE,
                inputType,
                outputType,
                arg,
                color: value.color,
                loc,
            };
            return PollResult.DONE;
        };
    }
    private pollMemberAccessAction(value: HIRMemberAccess, loc: SourceRange | undefined, resolved: HIRResolvedData): HIRPollAction {
        return self => {
            const lhs = unwrapUnknownNullable(self.resolved[value.lhs].value);
            if (lhs === void 0) {
                return PollResult.UNCHANGED;
            }
            if (lhs.kind === ExpressionKind.SYMBOL) {
                if (lhs.subSymbols !== void 0 && lhs.subSymbols.has(value.name)) {
                    const s = lhs.subSymbols.get(value.name) ?? panic();
                    if (s.value === void 0 || s.type === void 0) {
                        return PollResult.UNCHANGED;
                    }
                    resolved.value = s.value;
                    return PollResult.DONE;
                }
            }
            panic("TODO");
        };
    }
    private pollLambdaAction(value: HIRLambda, loc: SourceRange | undefined, resolved: HIRResolvedData): HIRPollAction {
        return self => {
            const type = unwrapUnknownNullable(resolved.type);
            if (type === void 0 || type.kind !== ExpressionKind.FN_TYPE) {
                return PollResult.UNCHANGED;
            }
            panic();
        };
    }
    private pollSymbolRuleAction(value: HIRSymbolRule, loc: SourceRange | undefined, resolved: HIRResolvedData): HIRPollAction {
        let hasTypeConstraint = false;
        return self => {
            let ret = PollResult.UNCHANGED;
            const symbol = self.resolved[value.symbol].value;
            const lhs = self.resolved[value.rule.lhs];
            const rhs = self.resolved[value.rule.rhs];
            if (lhs.value === void 0 || symbol === void 0) {
                return ret;
            }
            assert(symbol.kind === ExpressionKind.SYMBOL);
            if (rhs.value === void 0) {
                if (rhs.type === void 0) {
                    rhs.type = self.csolver.getType(lhs.value);
                    ret = PollResult.CHANGED;
                }
                return ret;
            }
            if (!hasTypeConstraint) {
                hasTypeConstraint = true;
                self.csolver.addEqualConstraint(self.csolver.getType(lhs.value), self.csolver.getType(rhs.value));
                return PollResult.CHANGED;
            }
            if (self.csolver.containsConstraintUnknown(lhs.value) || self.csolver.containsConstraintUnknown(rhs.value)) {
                return ret;
            }
            const rule = convertRule(lhs.value, rhs.value);
            if (value.isUpValue) {
                if (symbol.upValues === void 0) {
                    symbol.upValues = [];
                }
                symbol.upValues.push(rule);
            } else {
                if (symbol.downValues === void 0) {
                    symbol.downValues = [];
                }
                symbol.downValues.push(rule);
            }
            resolved.value = self.csolver.builtins.unit;
            return PollResult.DONE;
        };
    }
    private pollAction(index: number): HIRPollAction {
        const {value, loc} = this.regs[index];
        const resolved = this.resolved[index];
        switch (value.kind) {
            case HIRKind.CALL: return this.pollCallAction(value, loc, resolved);
            case HIRKind.FN_TYPE: return this.pollFnTypeAction(value, loc, resolved);
            case HIRKind.EXPR: return self => {
                resolved.value = value.expr;
                return PollResult.DONE;
            };
            case HIRKind.NUMBER: return self => {
                if (resolved.type === self.csolver.builtins.numberType) {
                    resolved.value = {kind: ExpressionKind.NUMBER, isLevel: false, value: value.value, loc};
                    return PollResult.DONE;
                }
                if (resolved.type === self.csolver.builtins.levelType) {
                    resolved.value = {kind: ExpressionKind.NUMBER, isLevel: true, value: value.value, loc};
                    return PollResult.DONE;
                }
                return PollResult.UNCHANGED;
            };
            case HIRKind.ROOT: return self => {
                resolved.value = self.root;
                return PollResult.DONE;
            };
            case HIRKind.VARIABLE: return self => {
                let type: Expression;
                if (value.type !== void 0) {
                    const type0 = self.resolved[value.type].value;
                    if (type0 === void 0) {
                        return PollResult.UNCHANGED;
                    }
                    this.csolver.addEqualConstraint(this.csolver.getType(type0), this.csolver.builtins.makeUnknownUniverse());
                    type = type0;
                } else {
                    type = makeUnknownType(self.csolver.builtins);
                }
                resolved.value = {
                    kind: ExpressionKind.VARIABLE,
                    loc,
                    name: value.name,
                    defaultType: type,
                };
                return PollResult.DONE;
            };
            case HIRKind.UNKNOWN: return self => {
                let type: Expression;
                if (value.type !== void 0) {
                    const type0 = self.resolved[value.type].value;
                    if (type0 === void 0) {
                        return PollResult.UNCHANGED;
                    }
                    self.csolver.addEqualConstraint(this.csolver.getType(type0), self.csolver.builtins.makeUniverse(makeUnknown(self.csolver.builtins.levelType, false)));
                    type = type0;
                } else {
                    type = makeUnknownType(self.csolver.builtins);
                }
                resolved.value = makeUnknown(type, false);
                return PollResult.DONE;
            };
            case HIRKind.SYMBOL: return self => {
                let parent: SymbolExpression;
                if (value.parent !== void 0) {
                    const p = self.resolved[value.parent];
                    if (p.value === void 0) {
                        return PollResult.UNCHANGED;
                    }
                    assert(p.value.kind === ExpressionKind.SYMBOL);
                    parent = p.value;
                } else {
                    parent = self.root;
                }
                const type = 0 !== (value.flags & SymbolFlags.ALLOW_DEF_TYPE) ? makeUnknownType(self.csolver.builtins) : self.csolver.builtins.untyped;
                resolved.value = {
                    kind: ExpressionKind.SYMBOL,
                    parent,
                    name: value.name,
                    loc,
                    flags: value.flags,
                    type,
                };
                setParent(resolved.value);
                return PollResult.DONE;
            };
            case HIRKind.SYMBOL_ASSIGN: return self => {
                const symbol = self.resolved[value.symbol].value;
                const v = self.resolved[value.value].value;
                if (symbol === void 0 || v === void 0) {
                    return PollResult.UNCHANGED;
                }
                assert(symbol.kind === ExpressionKind.SYMBOL);
                if (0 === (symbol.flags & SymbolFlags.ALLOW_ASSIGNMENT)) {
                    return PollResult.UNCHANGED;
                }
                assert(symbol.value === void 0);
                symbol.value = v;
                if (symbol.type === void 0) {
                    symbol.type = self.csolver.getType(v);
                } else {
                    self.csolver.addEqualConstraint(symbol.type, self.csolver.getType(v));
                }
                resolved.value = self.csolver.builtins.unit;
                return PollResult.DONE;
            };
            case HIRKind.SYMBOL_TYPE: return self => {
                const symbol = self.resolved[value.symbol].value;
                const type = self.resolved[value.type].value;
                if (symbol === void 0 || type === void 0) {
                    return PollResult.UNCHANGED;
                }
                assert(symbol.kind === ExpressionKind.SYMBOL);
                if (0 === (symbol.flags & SymbolFlags.ALLOW_DEF_TYPE)) {
                    return PollResult.UNCHANGED;
                }
                self.csolver.addEqualConstraint(self.csolver.getType(type), self.csolver.builtins.makeUnknownUniverse());
                if (symbol.type === void 0) {
                    symbol.type = type;
                } else {
                    self.csolver.addEqualConstraint(symbol.type, type);
                }
                resolved.value = self.csolver.builtins.unit;
                return PollResult.DONE;
            };
            case HIRKind.SYMBOL_RULE: return this.pollSymbolRuleAction(value, loc, resolved);
            case HIRKind.MEMBER_ACCESS: return this.pollMemberAccessAction(value, loc, resolved);
            case HIRKind.LAMBDA: return this.pollLambdaAction(value, loc, resolved);
        }
    }
    private iterate() {
        let changed = false;
        const actions = this.actions.slice(0);
        this.actions.length = 0;
        for (const a of actions) {
            const [index, action] = a;
            switch (action(this)) {
                case PollResult.UNCHANGED:
                    this.actions.push(a);
                    break;
                case PollResult.CHANGED:
                    changed = true;
                    this.actions.push(a);
                    break;
                case PollResult.DONE: {
                    changed = true;
                    const value = this.resolved[index].value ?? panic();
                    this.csolver.logger.info(() => `resolved(%${index}): ${this.csolver.stringifier.stringify(this.csolver.getType(value))} = ${this.csolver.stringifier.stringify(value)}`);
                    break;
                }
            }
        }
        changed = this.csolver.evaluate() || changed;
        return changed;
    }
    run() {
        while (this.iterate()) {}
    }
    collectDiagnostics() {
        const ret = this.csolver.collectDiagnostics();
        return ret;
    }
}

// export function checkTypes(root: SymbolExpression, stringifier: ExpressionStringifier, builtins: BuiltinSymbols, hir: HIRHost, logger: Logger): TypeCheckDiagnostic[] {
//     const hirRegs = hir.regs;
//     const hirResolvedData: HIRResolvedData[] = makeArray(() => ({completeDone: false, noEqualConstraints: true, errored: false}), hirRegs.length);
//     const hirDependencies = generateHIRDependencies(hir);
//     const constraints: Constraint[] = [];
//     const diagnostics: TypeCheckDiagnostic[] = [];
//     const typeCache = new WeakMap<Expression, Expression>();

//     run();
//     return diagnostics;

//     function makeUnknownType(source: HIRReg) {
//         return makeUnknown(builtins.makeUniverse(makeUnknown(builtins.levelType)));
//     }

//     function getType(expr: Expression) {
//         new TypeSolver(typeCache, builtins);
//     }

//     function pollHIR(hirReg: HIRReg): boolean {
//         const data = hirRegs[hirReg];
//         const resolved = hirResolvedData[hirReg];
//         const value = data.value;
//         if (resolved.errored || resolved.value !== void 0) {
//             return false;
//         }
//         switch (value.kind) {
//             case HIRKind.EXPR:
//                 resolved.value = value.expr;
//                 return true;
//             case HIRKind.NUMBER: {
//                 const type = resolved.type;
//                 if (type !== void 0) {
//                     if (type === builtins.levelType) {
//                         resolved.value = {
//                             kind: ExpressionKind.NUMBER,
//                             isLevel: true,
//                             value: value.value,
//                         };
//                         return true;
//                     } else if (type === builtins.numberType) {
//                         resolved.value = {
//                             kind: ExpressionKind.NUMBER,
//                             isLevel: false,
//                             value: value.value,
//                         };
//                         return true;
//                     }
//                 }
//                 return false;
//             }
//             case HIRKind.CALL: return pollCall(hirReg, value, resolved);
//             case HIRKind.LAMBDA: return pollLambda(hirReg, value, resolved);
//             case HIRKind.FN_TYPE: return pollFnType(hirReg, value, resolved);
//             case HIRKind.ROOT: {
//                 resolved.value = root;
//                 return true;
//             }
//             case HIRKind.SYMBOL: {
//                 let parent: SymbolExpression;
//                 if (value.parent !== void 0) {
//                     const p = hirResolvedData[value.parent];
//                     if (p.value === void 0) {
//                         return false;
//                     }
//                     assert(p.value.kind === ExpressionKind.SYMBOL);
//                     parent = p.value;
//                 } else {
//                     parent = root;
//                 }
//                 const type = 0 !== (value.flags & SymbolFlags.ALLOW_DEF_TYPE) ? makeUnknownType(hirReg) : builtins.untyped;
//                 resolved.value = {
//                     kind: ExpressionKind.SYMBOL,
//                     parent,
//                     name: value.name,
//                     loc: data.loc,
//                     flags: value.flags,
//                     type,
//                 };
//                 setParent(resolved.value);
//                 return true;
//             }
//             case HIRKind.VARIABLE: {
//                 let type: Expression;
//                 if (value.type !== void 0) {
//                     const type0 = hirResolvedData[value.type].value;
//                     if (type0 === void 0) {
//                         return false;
//                     }
//                     addConstraint({kind: ConstraintKind.IS_TYPE, expr: type0, source: hirReg});
//                     type = type0;
//                 } else {
//                     type = makeUnknownType(hirReg);
//                 }
//                 resolved.value = {
//                     kind: ExpressionKind.VARIABLE,
//                     loc: data.loc,
//                     name: value.name,
//                     type,
//                 };
//                 return true;
//             }
//             case HIRKind.SYMBOL_TYPE: {
//                 const symbol = hirResolvedData[value.symbol].value;
//                 const type = hirResolvedData[value.type].value;
//                 if (symbol === void 0 || type === void 0) {
//                     return false;
//                 }
//                 assert(symbol.kind === ExpressionKind.SYMBOL);
//                 if (0 === (symbol.flags & SymbolFlags.ALLOW_DEF_TYPE)) {
//                     return false;
//                 }
//                 if (symbol.type === void 0) {
//                     symbol.type = type;
//                 } else {
//                     addEqualConstraint(symbol.type, type, hirReg);
//                 }

//                 resolved.value = builtins.unit;
//                 resolved.type = builtins.unitType;
//                 return true;
//             }
//             case HIRKind.SYMBOL_ASSIGN: {
//                 const symbol = hirResolvedData[value.symbol].value;
//                 const v = hirResolvedData[value.value].value;
//                 const type = hirResolvedData[value.value].type;
//                 if (symbol === void 0 || v === void 0 || type === void 0) {
//                     return false;
//                 }
//                 assert(symbol.kind === ExpressionKind.SYMBOL);
//                 if (0 === (symbol.flags & SymbolFlags.ALLOW_ASSIGNMENT)) {
//                     return false;
//                 }
//                 assert(symbol.value === void 0);
//                 symbol.value = v;
//                 if (symbol.type === void 0) {
//                     symbol.type = type;
//                 } else {
//                     addEqualConstraint(symbol.type, type, hirReg);
//                 }
//                 resolved.value = builtins.unit;
//                 resolved.type = builtins.unitType;
//                 return true;
//             }
//             case HIRKind.SYMBOL_RULE: return pollDownValue(hirReg, value, resolved);
//             case HIRKind.UNKNOWN: {
//                 let type: Expression;
//                 if (value.type !== void 0) {
//                     const type0 = hirResolvedData[value.type].value;
//                     if (type0 === void 0) {
//                         return false;
//                     }
//                     addConstraint({kind: ConstraintKind.IS_TYPE, expr: type0, source: hirReg});
//                     type = type0;
//                 } else {
//                     type = makeUnknownType(hirReg);
//                 }
//                 resolved.value = makeUnknown(type);
//                 return true;
//             }
//             case HIRKind.MEMBER_ACCESS: return pollMemberAccess(hirReg, value, resolved);
//         }
//     }

//     function pollFnType(source: HIRReg, value: HIRFnType, resolved: HIRResolvedData): boolean {
//         const inputType = hirResolvedData[value.inputType].value;
//         const outputType = hirResolvedData[value.outputType].value;
//         if (inputType === void 0 || outputType === void 0) return false;
//         let arg: VariableExpression | undefined = void 0;
//         if (value.arg !== void 0) {
//             const a = hirResolvedData[value.arg].value;
//             if (a === void 0 || a.kind !== ExpressionKind.VARIABLE) return false;
//             arg = a;
//         }
//         resolved.value = {
//             kind: ExpressionKind.FN_TYPE,
//             color: value.color,
//             inputType,
//             outputType,
//             arg,
//         };
//         return true;
//     }

//     function pollCallIn(source: HIRReg, fn: Expression, fnType: Expression | undefined, argReg: HIRReg, color: number, isPattern: boolean): Expression | null {
//         const arg = hirResolvedData[argReg].value;
//         if (arg === void 0) {
//             const argEntry = hirResolvedData[argReg];
//             if (argEntry.type === void 0) {
//                 if (fn.kind === ExpressionKind.SYMBOL && fn === builtins.type) {
//                     argEntry.type = builtins.levelType;
//                 } else if (fnType !== void 0 && fnType.kind === ExpressionKind.FN_TYPE) {
//                     argEntry.type = fnType.inputType;
//                 }
//             }
//             return null;
//         }
//         const argType = getType(arg, builtins);
//         if (argType === void 0) {
//             return null;
//         }

//         if (fnType === void 0 || fnType.kind !== ExpressionKind.FN_TYPE) {
//             return null;
//         }
//         if (!checkFnTypeColor(fnType, color, true)) {
//             return null;
//         }
//         let ret = fn;
//         while (fnType.kind === ExpressionKind.FN_TYPE && color !== fnType.color) {
//             const temp: UnknownExpression = {kind: ExpressionKind.UNKNOWN, isPattern, excludedVariables: new Set()};
//             let nextType: Expression = fnType.outputType;
//             if (fnType.arg !== void 0) {
//                 nextType = replaceScopeVariable(nextType, fnType.arg, temp, false) ?? panic();
//             }
//             ret = {kind: ExpressionKind.CALL, fn: ret, arg: temp, type: nextType, color: fnType.color};
//             fnType = unwrapUnknown(nextType);
//         }
//         assert(fnType.kind === ExpressionKind.FN_TYPE);
//         addEqualConstraint(fnType.inputType, argType, source);
//         let retType = fnType.outputType;
//         if (fnType.arg !== void 0) {
//             retType = replaceScopeVariable(retType, fnType.arg, arg, false) ?? panic();
//         }
//         return {
//             kind: ExpressionKind.CALL,
//             fn: ret,
//             arg,
//             type: retType,
//             color,
//         };
//     }

//     function pollCall(source: HIRReg, value: HIRCall, resolved: HIRResolvedData): boolean {
//         assert(resolved.value === void 0);
//         let fn = hirResolvedData[value.fn].value;
//         if (fn === void 0) {
//             return false;
//         }
//         fn = unwrapUnknown(fn);
//         let fnType = getType(fn, builtins);
//         if (fnType !== void 0) {
//             fnType = unwrapUnknown(fnType);
//         }

//         const v = pollCallIn(source, fn, fnType, value.arg, value.color, value.isPattern);
//         if (v !== null) {
//             resolved.value = v;
//             return true;
//         } else {
//             return false;
//         }
//     }

//     function pollMemberAccess(source: HIRReg, value: HIRMemberAccess, resolved: HIRResolvedData) {
//         let lhs = hirResolvedData[value.lhs].value;
//         let lhsType = hirResolvedData[value.lhs].type;
//         if (lhs === void 0 || lhsType === void 0) {
//             return false;
//         }
//         lhs = unwrapUnknown(lhs);
//         lhsType = unwrapUnknown(lhsType);
//         if (lhs.kind === ExpressionKind.SYMBOL) {
//             if (lhs.subSymbols !== void 0 && lhs.subSymbols.has(value.name)) {
//                 const s = lhs.subSymbols.get(value.name) ?? panic();
//                 if (s.value === void 0 || s.type === void 0) {
//                     return false;
//                 }
//                 resolved.value = s.value;
//                 resolved.type = s.type;
//                 return true;
//             }
//         }
//         panic("TODO");
//     }

//     function pollLambda(source: HIRReg, value: HIRLambda, resolved: HIRResolvedData): boolean {
//         let body = hirResolvedData[value.body].value;
//         if (resolved.type === void 0 || body === void 0) {
//             return false;
//         }
//         let arg: SymbolExpression | undefined = void 0;
//         if (value.arg !== void 0) {
//             const r = hirResolvedData[value.arg].value;
//             if (r === void 0 || r.kind !== ExpressionKind.SYMBOL) {
//                 return false;
//             }
//             arg = r;
//         }
//         let type = unwrapUnknown(resolved.type);
//         if (type.kind !== ExpressionKind.FN_TYPE || !checkFnTypeColor(type, 0, false)) {
//             return false;
//         }

//         panic("TODO");
//     }

//     function addConstraint(con: Constraint) {
//         logger.info(() => `add constraint ${dumpConstraint(con, stringifier)}, source %${con.source}`);
//         constraints.push(con);
//     }

//     function addEqualConstraint(expr1: MetaExpression, expr2: MetaExpression, source: HIRReg) {
//         addConstraint({kind: ConstraintKind.EQUAL, expr1, expr2, source});
//     }

//     function convertRule(lhs: Expression, rhs: Expression) {
//         lhs = mapExpression(lhs, {
//             enterScope(){},
//             leaveScope(){},
//             map(expr, info){
//                 if (expr.kind === ExpressionKind.UNKNOWN && expr.isPattern) {
//                     assert(expr.value === void 0);
//                     assert(expr.type !== void 0);
//                     const s: VariableExpression = {kind: ExpressionKind.VARIABLE, type: expr.type};
//                     expr.value = s;
//                     info.emit(s);
//                     return;
//                 }
//             }
//         }) ?? panic();
//         return [lhs, copyExpression(rhs)];
//     }

//     function pollDownValue(source: HIRReg, value: HIRSymbolRule, resolved: HIRResolvedData): boolean {
//         if (resolved.value === void 0) {
//             const lhs = hirResolvedData[value.rule.lhs].value;
//             if (lhs === void 0) {
//                 return false;
//             }
//             const lhsType = getType(lhs, builtins);
//             const rhs = hirResolvedData[value.rule.rhs].value;
//             if (lhsType !== void 0) {
//                 hirResolvedData[value.rule.rhs].type = lhsType;
//             }
//             if (rhs === void 0) {
//                 return false;
//             }
//             const rhsType = getType(rhs, builtins);
//             if (lhsType !== void 0 && rhsType !== void 0) {
//                 addEqualConstraint(lhsType, rhsType, source);
//             }
//             resolved.value = builtins.unit;
//             return true;
//         }
//         // if (!resolved.completeDone) {
//         //     if (resolved.noEqualConstraints) {
//         //         const [lhsExpr, rhsExpr] = convertRule(hirResolvedData[lhs].value ?? panic(), hirResolvedData[rhs].value ?? panic());
//         //         assert(lhsExpr.kind === ExpressionKind.CALL);
//         //         const fn = getFn(lhsExpr);
//         //         assert(fn.kind === ExpressionKind.SYMBOL);
//         //         const entry = tempRegistry.getSymbolEntry(fn.symbol);
//         //         if (!tempRegistry.isLocalSymbol(fn.symbol) || 0 === (entry.flags & SymbolFlags.ALLOW_DOWN_VALUE)) {
//         //             return false;
//         //         }
//         //         let target: [Expression, Expression][];
//         //         if (!value.isUpValue) {
//         //             if (entry.downValues === void 0) {
//         //                 entry.downValues = [];
//         //             }
//         //             target = entry.downValues;
//         //         } else {
//         //             if (entry.upValues === void 0) {
//         //                 entry.upValues = [];
//         //             }
//         //             target = entry.upValues;
//         //         }
//         //         target.push([lhsExpr, rhsExpr]);
//         //         resolved.completeDone = true;
//         //         return true;
//         //     }
//         //     return false;
//         // }
//         panic();
//     }

//     function makeLambda(body: Expression, arg: VariableExpression, type: FnTypeExpression): Expression {
//         if (body.kind === ExpressionKind.CALL && body.arg.kind === ExpressionKind.VARIABLE && body.arg === arg && variableFreeQ(body.fn, arg)) {
//             return body.fn;
//         } else {
//             const newArg: VariableExpression | undefined = variableFreeQ(body, arg) ? void 0 : {
//                 kind: ExpressionKind.VARIABLE,
//                 type: type.inputType,
//             };
//             return {
//                 kind: ExpressionKind.LAMBDA,
//                 arg: newArg,
//                 body: newArg !== void 0 ? (replaceScopeVariable(body, arg, newArg, false) ?? panic()) : body,
//                 type,
//             };
//         }
//     }

//     function evaluateEqualConstraint(expr1: Expression, expr2: Expression, source: HIRReg, fixedPoint: boolean) {
//         if (expr1.kind !== ExpressionKind.UNKNOWN && expr2.kind === ExpressionKind.UNKNOWN) {
//             const t = expr1;
//             expr1 = expr2;
//             expr2 = t;
//         }
//         if (expr1.kind === ExpressionKind.UNKNOWN) {
//             assert(expr1.value === void 0);
//             if (expr2.kind === ExpressionKind.UNKNOWN) {
//                 assert(expr2.value === void 0);
//                 if (expr1 === expr2) {
//                     return true;
//                 }
//                 if (expr1.isPattern && !expr2.isPattern) {
//                     const t = expr1;
//                     expr1 = expr2;
//                     expr2 = t;
//                 }
//             }
//             if (!freeQ(expr2, expr => expr === expr1)) {
//                 logger.info(() => `rejecting unknown assign ${stringifier.stringify(expr1)} = ${stringifier.stringify(expr2)}`);
//                 return false;
//             }
//             // addEqualConstraint(expr1.type, typeOfExpression0(expr2), source);
//             logger.info(() => `setting unknown ${stringifier.stringify(expr1)} = ${stringifier.stringify(expr2)}`);
//             expr1.value = expr2;
//             return true;
//         }
//         if (expr1.kind === ExpressionKind.UNIVERSE && expr2.kind === ExpressionKind.UNIVERSE) {
//             addEqualConstraint(expr1.level, expr2.level, source);
//             return true;
//         }
//         if (expr1.kind === ExpressionKind.NUMBER && expr2.kind === ExpressionKind.NUMBER && expr1.isLevel && expr2.isLevel && expr1.value === expr2.value) {
//             return true;
//         }
//         if (expr1.kind === ExpressionKind.STRING && expr2.kind === ExpressionKind.STRING && expr1.value === expr2.value) {
//             return true;
//         }
//         if (expr1.kind !== ExpressionKind.CALL && expr2.kind === ExpressionKind.CALL) {
//             const t = expr1;
//             expr1 = expr2;
//             expr2 = t;
//         }
//         if (expr1.kind === ExpressionKind.CALL) {
//             if (expr2.kind === ExpressionKind.CALL) {
//                 if (fixedPoint) {
//                     addEqualConstraint(expr1.fn, expr2.fn, source);
//                     addEqualConstraint(expr1.arg, expr2.arg, source);
//                     return true;
//                 }
//                 const [fn1, args1] = collectFnArgs(expr1);
//                 const [fn2, args2] = collectFnArgs(expr2);
//                 if (fn1.kind === ExpressionKind.SYMBOL && fn2.kind === ExpressionKind.SYMBOL) {
//                     if (args1.length === args2.length && fn1 === fn2) {
//                         if (0 === (fn1.flags & (SymbolFlags.ALLOW_DOWN_VALUE | SymbolFlags.ALLOW_ASSIGNMENT))) {
//                             for (let i = 0; i < args1.length; i++) {
//                                 addEqualConstraint(args1[i], args2[i], source);
//                             }
//                             addEqualConstraint(expr1.type, expr2.type, source);
//                             return true;
//                         }
//                     }
//                 }
//             }
//             let eta1 = canUseEtaReduction(expr1);
//             if (!eta1 && expr2.kind === ExpressionKind.CALL && canUseEtaReduction(expr2)) {
//                 eta1 = true;
//                 const t = expr1;
//                 expr1 = expr2;
//                 expr2 = t;
//             }
//             // TODO
//             // if (eta1) {
//             //     addEqualConstraint(expr1.fn, makeLambda(expr2, expr1.arg, expr1.fn.));
//             // }
//             // if (expr1.arg.kind === ExpressionKind.SYMBOL && tempRegistry.isVariable(expr1.arg.symbol) && symbolFreeQ(expr1.fn, expr1.arg.symbol)) {
//             //     if (fixedPoint || !argsContainsUninferedTemps(tempRegistry, expr1) && !containsUninferedTemps(tempRegistry, expr2)) {
//             //         addEqualConstraint(expr1.fn, makeLambda(expr2, expr1.arg, typeOfExpression0(expr1.fn)), source);
//             //         addEqualConstraint(expr1.type, typeOfExpression0(expr2), source);
//             //         return true;
//             //     }
//             // }
//         }
//         if (expr1.kind === ExpressionKind.FN_TYPE && expr2.kind === ExpressionKind.FN_TYPE) {
//             addEqualConstraint(expr1.inputType, expr2.inputType, source);
//             let output2: MetaExpression = expr2.outputType;
//             if (expr1.arg !== void 0 && expr2.arg !== void 0 && expr1.arg !== expr2.arg) {
//                 output2 = {
//                     kind: ExpressionKind.REPLACE_VARIABLE,
//                     expr: expr2.outputType,
//                     variable: expr2.arg,
//                     replacement: expr1.arg,
//                 };
//             }
//             addEqualConstraint(expr1.outputType, output2, source);
//             return true;
//         }
//         if (expr1.kind === ExpressionKind.LAMBDA && expr2.kind === ExpressionKind.LAMBDA) {
//             addEqualConstraint(expr1.type, expr2.type, source);
//             let body2: MetaExpression = expr2.body;
//             if (expr1.arg !== void 0 && expr2.arg !== void 0 && expr1.arg !== expr2.arg) {
//                 body2 = {
//                     kind: ExpressionKind.REPLACE_VARIABLE,
//                     expr: expr2.body,
//                     variable: expr2.arg,
//                     replacement: expr1.arg,
//                 };
//             }
//             addEqualConstraint(expr1.body, body2, source);
//             return true;
//         }
//         return false;
//     }

//     function evaluateConstraint(con: Constraint, isFixedPoint: boolean) {
//         logger.info(() => `evaluating ${dumpConstraint(con, stringifier)}, source %${con.source}`);
//         const evaluator = new Evaluator(builtins);
//         switch (con.kind) {
//             case ConstraintKind.EQUAL: {
//                 const oldExpr1 = con.expr1;
//                 const oldExpr2 = con.expr2;
//                 let expr1 = evaluator.evaluateMeta(oldExpr1);
//                 let expr2 = evaluator.evaluateMeta(oldExpr2);
//                 if (oldExpr1 !== expr1 || oldExpr2 !== expr2) {
//                     logger.info(() => `evaluated expr: ${stringifier.stringifyMeta(expr1)} === ${stringifier.stringifyMeta(expr2)}`);
//                 }
//                 const changed = expr1 !== oldExpr1 || expr2 !== oldExpr2;
//                 if (isExpression(expr1) && isExpression(expr2)) {
//                     if (evaluateEqualConstraint(expr1, expr2, con.source, isFixedPoint)) {
//                         return true;
//                     }
//                     if (sameQ(expr1, expr2)) {
//                         return true;
//                     }
//                 }
//                 if (changed) {
//                     logger.info(() => 'changed');
//                     addEqualConstraint(expr1, expr2, con.source);
//                 } else {
//                     logger.info(() => 'unchanged');
//                     constraints.push(con);
//                 }
//                 return changed;
//             }
//         }

//     }

//     function pollAllHIR() {
//         let done = false;
//         let changed = false;
//         while (!done) {
//             done = true;
//             for (let i = 0; i < hirRegs.length; i++) {
//                 const resolved = hirResolvedData[i];
//                 const hasValue = resolved.value !== void 0;
//                 if (pollHIR(i as HIRReg)) {
//                     if (!hasValue && resolved.value !== void 0) {
//                         const type = getType(resolved.value, builtins);
//                         const typeStr = type !== void 0 ? ': ' + stringifier.stringify(type) : '';
//                         logger.info(() => `resolved(%${i})${typeStr} = ${stringifier.stringify(resolved.value!)}`);
//                     }
//                     done = false;
//                     changed = true;
//                 }
//             }
//         }
//         return changed;
//     }

//     function dumpConstraints(title: string) {
//         logger.info(() => {
//             const ret: string[] = [title + ': equal constraints:'];
//             for (const con of constraints) {
//                 ret.push(`    ${dumpConstraint(con, stringifier)}, source %${con.source}`);
//             }
//             ret.push('end');
//             return ret;
//         });
//     }

//     function evaluateConstraints(fixedPoint: boolean) {
//         dumpConstraints('before');
//         let done = false;
//         let changed = false;
//         while (!done) {
//             done = true;
//             const cons = constraints.slice(0);
//             constraints.length = 0;
//             for (const con of cons) {
//                 if (evaluateConstraint(con, fixedPoint)) {
//                     if (fixedPoint) {
//                         fixedPoint = false;
//                     }
//                     done = false;
//                     changed = true;
//                 }
//             }
//         }
//         dumpConstraints('after');
//         return changed;
//     }

//     function updateNoEqualConstraintsMarker() {

//     }

//     function iterate(fixedPoint: boolean) {
//         let changed = false;
//         let now = new Date();
//         const timer = new Timer();
//         if (!fixedPoint) {
//             changed = pollAllHIR() || changed;
//         }
//         logger.info(() => `poll HIR took ${timer.elapsed()}ms`);
//         changed = evaluateConstraints(fixedPoint) || changed;
//         logger.info(() => `contraints took ${timer.elapsed()}ms`);
//         if (changed) {
//             updateNoEqualConstraintsMarker();
//             logger.info(() => `refresh took ${timer.elapsed()}ms`);
//         }
//         return changed;
//     }

//     function run() {
//         let iterations = 0;
//         let fixedIterations = 0;
//         const timer = new Timer();
//         while (true) {
//             logger.info(() => `iteration ${iterations}`);
//             while (iterate(false)) {
//                 iterations++;
//             }
//             logger.info(() => `fixed iteration ${fixedIterations}`);
//             if (!iterate(true)) {
//                 fixedIterations++;
//                 break;
//             }
//         }

//         for (const con of constraints) {
//             diagnostics.push({kind: TypeCheckDiagnosticKind.UNRESOLVED_CONSTRAINT, con});
//         }
//         if (diagnostics.length > 0) {
//             logger.info(() => stringifier.dumpSymbol(root));
//             return;
//         }
//         logger.info(() => `done in ${timer.elapsed()}ms, ${iterations} iterations and ${fixedIterations} fixed iterations`);
//     }
// }

function collectRules(expr: CallExpression) {
    const [fn, args] = collectFnArgs(expr);
    const rules: [Expression, Expression][] = [];
    for (const arg of args) {
        if (arg.kind === ExpressionKind.SYMBOL) {
            if (arg.upValues) {
                rules.push(...arg.upValues);
            }
        } else if (arg.kind === ExpressionKind.CALL) {
            const fn2 = getFn(arg);
            if (fn2.kind === ExpressionKind.SYMBOL) {
                if (fn2.upValues) {
                    rules.push(...fn2.upValues);
                }
            }
        }
    }
    if (fn.kind === ExpressionKind.SYMBOL) {
        if (fn.downValues) {
            rules.push(...fn.downValues);
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
    constructor(readonly builtins: BuiltinSymbols, readonly csolver: ConstraintSolver) {}
    private doActions(...actions: EvaluatorAction[]) {
        pushReversed(this.todo, actions);
    }
    private _evaluate(expr: Expression): EvaluatorAction {
        return self => {
            switch (expr.kind) {
                case ExpressionKind.VARIABLE: self.stack.push(expr); break;
                case ExpressionKind.SYMBOL: {
                    if (self.ownValue && expr.value !== void 0) {
                        self.doActions(self._evaluate(expr.value));
                    } else {
                        self.stack.push(expr);
                    }
                    break;
                }
                case ExpressionKind.CALL: {
                    self.doActions(self._evaluate(expr.fn), self._evaluate(expr.arg), self => {
                        const arg = self.stack.pop()!;
                        const fn = self.stack.pop()!;
                        if (fn.kind === ExpressionKind.LAMBDA) {
                            if (fn.arg !== void 0) {
                                self.doActions(self._evaluate(replaceScopeVariable(fn.body, fn.arg, arg, self.csolver) ?? panic()));
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
                case ExpressionKind.UNKNOWN: {
                    if (expr.value !== void 0) {
                        self.doActions(self._evaluate(expr.value));
                    } else {
                        self.stack.push(expr);
                    }
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
                if (fn.evaluator !== void 0) {
                    const value = fn.evaluator(args);
                    if (value !== void 0) {
                        self.stack.push(value);
                        return;
                    }
                }
                for (const [lhs, rhs] of collectRules(expr)) {
                    const reps = matchPattern(lhs, expr);
                    if (reps !== null) {
                        panic("TODO");
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
