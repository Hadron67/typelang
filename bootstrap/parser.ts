import { assert, Either } from "./util";

const CCODE_A = 'A'.charCodeAt(0);
const CCODE_Z = 'Z'.charCodeAt(0);
const CCODE_LOWER_A = 'a'.charCodeAt(0);
const CCODE_LOWER_Z = 'z'.charCodeAt(0);

const CCODE_0 = '0'.charCodeAt(0);
const CCODE_9 = '9'.charCodeAt(0);
const CCODE_OPEN_PARENTH = '('.charCodeAt(0);
const CCODE_CLOSE_PARENTH = ')'.charCodeAt(0);
const CCODE_OPEN_BRACKET = '['.charCodeAt(0);
const CCODE_CLOSE_BRACKET = ']'.charCodeAt(0);
const CCODE_OPEN_BRACE = '{'.charCodeAt(0);
const CCODE_CLOSE_BRACE = '}'.charCodeAt(0);
const CCODE_DASH = '-'.charCodeAt(0);
const CCODE_GT = '>'.charCodeAt(0);
const CCODE_LT = '<'.charCodeAt(0);
const CCODE_BAR = '|'.charCodeAt(0);
const CCODE_PLUS = '+'.charCodeAt(0);
const CCODE_BSLASH = '\\'.charCodeAt(0);
const CCODE_DOT = '.'.charCodeAt(0);
const CCODE_EQUAL = '='.charCodeAt(0);
const CCODE_COLON = ':'.charCodeAt(0);
const CCODE_COMMA = ','.charCodeAt(0);
const CCODE_EAR = '?'.charCodeAt(0);
const CCODE_N = 'n'.charCodeAt(0);
const CCODE_L = 'l'.charCodeAt(0);
const CCODE_SEMI_COLON = ';'.charCodeAt(0);
const CCODE_UNDERSCORE = '_'.charCodeAt(0);

const CCODE_SPACE = ' '.charCodeAt(0);
const CCODE_CR = '\r'.charCodeAt(0);
const CCODE_LF = '\n'.charCodeAt(0);
const CCODE_TAB = '\t'.charCodeAt(0);

export const enum TokenKind {
    EOF,
    NUMBER,
    STRING,
    IDENTIFIER,
    COLON,
    DOT,
    OPEN_PARENTH,
    CLOSE_PARENTH,
    OPEN_BRACKET,
    CLOSE_BRACKET,
    OPEN_BRACE,
    CLOSE_BRACE,
    COMMA,
    IMPORT,
    ARROW,
    BSLASH,
    DOUBLE_BSLASH,
    ASSIGN,
    OPERATOR,
    ASSIGN_OPERATOR,
    PROD,
    EAR,
    EQUIV,
    SEMI_COLON,
    WHILE,
    STRUCT,
    ENUM,
    BREAK,
    CONTINUE,
    RETURN,
    DEFER,
    VAR,
    LET,
    PUB,
    PRIV,
    INLINE,
    INDUCTIVE,
    MODULE,
    DOWN_VALUE,
    VARIABLE,
}

export interface Token extends SourceRange {
    readonly kind: TokenKind;
    readonly value: unknown;
}

const KEYWORKDS: {[name: string]: TokenKind} = {
    'if': TokenKind.IMPORT,
    'else': TokenKind.MODULE,
    'while': TokenKind.WHILE,
    'struct': TokenKind.STRUCT,
    'enum': TokenKind.ENUM,
    'inductive': TokenKind.INDUCTIVE,
    'return': TokenKind.RETURN,
    'break': TokenKind.BREAK,
    'continue': TokenKind.CONTINUE,
    'defer': TokenKind.DEFER,
    'var': TokenKind.VAR,
    'let': TokenKind.LET,
    'pub': TokenKind.PUB,
    'priv': TokenKind.PRIV,
    'inline': TokenKind.INLINE,
    'module': TokenKind.MODULE,
    'variable': TokenKind.VARIABLE,
};

const OPERATORS = [
    '>', '<', '=', '|', '~', '!', '&', '@', '^', '%', '+', '-', '*', '/'
].map(s => s.charCodeAt(0));
const OPERATOR_PRECEDENCES = (() => {
    const ret: number[] = Array(256);
    for (let i = 0, a = OPERATORS; i < a.length; i++) {
        ret[a[i]] = i;
    }
    return ret;
})();

export const enum AstKind {
    IDENTIFIER,
    NUMBER,
    STRING,
    FN_TYPE,
    INT_TYPE,
    IF,
    WHILE,
    STRUCT,
    BLOCK,
    LET,
    BREAK,
    CONTINUE,
    RETURN,
    CALL,
    SUBSCRIPT,
    LAMBDA,
    BINARY,
    STRUCT_LITERAL,
    MEMBER_ACCESS,
    DEFER,
    ASSIGN,
    VAR,
    MODULE_DECL,
    MODULE,
    DOWN_VALUE,
    PATTERN,
    PARTIAL_FN_TYPE,
    VARIABLE,
}

export type FileId = number & { __type: FileId };

export const enum StructVariant {
    MODULE,
    STRUCT,
    ENUM,
    INDUCTIVE,
}

export interface SourceRange {
    readonly file: FileId;
    readonly start: number;
    readonly length: number;
}

export type Ast =
    | AstIdentifier
    | AstNumber
    | AstString
    | AstFnType
    | AstBlock
    | AstLet
    | AstIf
    | AstBreak
    | AstContinue
    | AstReturn
    | AstCall
    | AstLambda
    | AstBinary
    | AstStructLiteral
    | AstMemberAccess
    | AstDefer
    | AstAssign
    | AstStructLike
    | AstModuelDecl
    | AstDownValue
    | AstPattern
    | AstModule
    | AstVariable
;

export interface AstIdentifier extends SourceRange {
    readonly kind: AstKind.IDENTIFIER;
    readonly name: string;
}

export interface AstNumber extends SourceRange {
    readonly kind: AstKind.NUMBER;
    readonly value: number;
}

export interface AstString extends SourceRange {
    readonly kind: AstKind.STRING;
    readonly value: string;
}

export interface FnTypeArg {
    readonly name?: AstIdentifier;
    readonly type: Ast;
    readonly defaultValue: Ast;
}

export interface AstFnTypeArgList extends SourceRange {
    readonly isArgList: true;
    readonly args: [AstIdentifier, Ast | undefined][];
    readonly color: number;
}

export interface AstFnTypeOneArg {
    readonly isArgList: false;
    readonly type: Ast;
}

export type AstFnTypeArg = AstFnTypeArgList | AstFnTypeOneArg;

export interface AstFnType extends SourceRange {
    readonly kind: AstKind.FN_TYPE;
    readonly inputType: AstFnTypeArg;
    readonly outputType: Ast;
}

export interface AstBlock extends SourceRange {
    readonly kind: AstKind.BLOCK;
    readonly label?: AstIdentifier;
    readonly body: Ast[];
}

export interface AstLet extends SourceRange {
    readonly kind: AstKind.LET;
    readonly name: AstIdentifier;
    readonly type?: Ast;
    readonly initializer?: Ast;
    readonly isVar: boolean;
    readonly isPub: boolean;
    readonly isInline: boolean;
}

export interface AstIf extends SourceRange {
    readonly kind: AstKind.IF;
    readonly cond: Ast;
    readonly body: Ast;
    readonly elseBlock?: Ast;
}

export interface AstWhile extends SourceRange {
    readonly kind: AstKind.WHILE;
    readonly cond: Ast;
    readonly body: Ast;
    readonly elseBlock?: Ast;
}

export interface AstBreak extends SourceRange {
    readonly kind: AstKind.BREAK;
    readonly label?: AstIdentifier;
    readonly expr: Ast;
}

export interface AstContinue extends SourceRange {
    readonly kind: AstKind.CONTINUE;
    readonly label?: AstIdentifier;
    readonly expr: Ast;
}

export interface AstReturn extends SourceRange {
    readonly kind: AstKind.RETURN;
    readonly expr: Ast;
}

export interface AstCall extends SourceRange {
    readonly kind: AstKind.CALL;
    readonly color: number;
    readonly fn: Ast;
    readonly arg?: Ast;
}

export interface AstLambda extends SourceRange {
    readonly kind: AstKind.LAMBDA;
    readonly body: Ast;
    readonly arg: AstIdentifier;
}

export interface AstBinary extends SourceRange {
    readonly kind: AstKind.BINARY;
    readonly left: Ast;
    readonly right: Ast;
    readonly operator: string;
}

export interface AstStructLiteral extends SourceRange {
    readonly kind: AstKind.STRUCT_LITERAL;
    readonly type?: Ast;
    readonly args: [AstIdentifier | undefined, Ast][];
}

export interface AstMemberAccess extends SourceRange {
    readonly kind: AstKind.MEMBER_ACCESS;
    readonly lhs: Ast;
    readonly member: Ast;
}

export interface AstDefer extends SourceRange {
    readonly kind: AstKind.DEFER;
    readonly body: Ast;
}

export interface AstAssign extends SourceRange {
    readonly kind: AstKind.ASSIGN;
    readonly lhs: Ast;
    readonly rhs: Ast;
    readonly operator: string;
}

export interface AstStructField {
    readonly name: AstIdentifier;
    readonly type: Ast;
    readonly defaultValue?: Ast;
    readonly isPub: boolean;
}

export interface AstStructLike extends SourceRange {
    readonly kind: AstKind.STRUCT;
    readonly type?: Ast;
    readonly variant: StructVariant;
    readonly fields: AstStructField[];
    readonly decls: AstLet[];
}

export interface AstModuelDecl extends SourceRange {
    readonly kind: AstKind.MODULE_DECL;
    readonly lhs: Ast;
    readonly args?: AstFnTypeArgList;
    readonly rhs?: Ast;
    readonly type?: Ast;
}

export interface AstModule extends SourceRange {
    readonly kind: AstKind.MODULE;
    readonly name: AstIdentifier;
    readonly decls: Ast[];
}

export interface AstDownValue extends SourceRange {
    readonly kind: AstKind.DOWN_VALUE;
    readonly lhs: Ast;
    readonly rhs: Ast;
}

export interface AstPattern extends SourceRange {
    readonly kind: AstKind.PATTERN;
    readonly name?: AstIdentifier;
}

export interface AstVariable extends SourceRange {
    readonly kind: AstKind.VARIABLE;
    readonly name: AstIdentifier;
    readonly type?: Ast;
}

export interface ParenthExpressionItem {
    readonly expr: Ast;
    readonly type?: Ast;
    readonly defaultValue?: Ast;
}

export interface SourceRangeMessage extends SourceRange {
    readonly msg: string;
    readonly notes?: SourceRangeMessage[];
};

export function asSourceRange(r: SourceRange): SourceRange {
    return {start: r.start, length: r.length, file: r.file};
}

export function sourceRangeBetween(a1: SourceRange, a2: SourceRange): SourceRange {
    assert(a1.file === a2.file);
    const start = a1.start <= a2.start ? a1.start : a2.start;
    const end1 = a1.start + a1.length;
    const end2 = a2.start + a2.length;
    const end = end1 >= end2 ? end1 : end2;
    return {file: a1.file, start, length: end - start};
}

export function sourceLocationToPosition(source: string[], loc: number): [number, number] {
    for (let line = 0; line < source.length; line++) {
        const l = source[line].length;
        if (loc < l) {
            return [line, loc];
        } else {
            loc -= l;
        }
    }
    return [source.length, loc];
}

export function renderMarkedSource(source: string[], range: SourceRange, sourceStart: string) {
    const [startLine, startColumn] = sourceLocationToPosition(source, range.start);
    const [endLine, endColumn] = sourceLocationToPosition(source, range.start + range.length - 1);
    const ret: string[] = [];
    for (let i = startLine; i <= endLine; i++) {
        ret.push(sourceStart + source[i].replace(/\n/g, ''));
        const c1 = i === startLine ? startColumn : 0;
        const c2 = i === endLine ? endColumn : source[i].length;
        ret.push(' '.repeat(c1 + sourceStart.length) + '^'.repeat(c2 + 1 - c1));
    }
    return ret;
}
export function renderLocationAndMarkedSource(source: string[], fileName: string, range: SourceRange, sourceStart: string) {
    const loc = sourceLocationToPosition(source, range.start);
    return [`${fileName}:${loc[0] + 1}:${loc[1] + 1}`, ...renderMarkedSource(source, range, sourceStart)];
}

export function renderSourceMessage(msg: SourceRangeMessage, fileProvider: (f: FileId) => [string, string[]]) {
    const [fname, lines] = fileProvider(msg.file);
    const loc = sourceLocationToPosition(lines, msg.start);
    return [`${fname}:${loc[0] + 1}:${loc[1] + 1}: ${msg.msg}`, ...renderMarkedSource(lines, msg, '   |')];
}

function isWhitespace(ch: number) {
    return ch === CCODE_CR || ch === CCODE_LF || ch === CCODE_SPACE || ch === CCODE_TAB;
}

function isIdentifierStart(ch: number) {
    return ch >= CCODE_A && ch <= CCODE_Z || ch >= CCODE_LOWER_A && ch <= CCODE_LOWER_Z || ch === CCODE_UNDERSCORE;
}

function isIdentifierPart(ch: number) {
    return ch >= CCODE_A && ch <= CCODE_Z || ch >= CCODE_LOWER_A && ch <= CCODE_LOWER_Z || ch >= CCODE_0 && ch <= CCODE_9 || ch === CCODE_UNDERSCORE;
}

function isDigit(ch: number) {
    return ch >= CCODE_0 && ch <= CCODE_9;
}

function isOperatorPart(ch: number) {
    return ch === CCODE_GT || ch === CCODE_LT || ch === CCODE_BAR || ch === CCODE_PLUS || ch === CCODE_DASH;
}

function compareOperatorPrecedence(op1: string, op2: string) {
    for (let i = 0; i < op1.length && i < op2.length; i++) {
        const p1 = OPERATOR_PRECEDENCES[op1.charCodeAt(i)];
        const p2 = OPERATOR_PRECEDENCES[op2.charCodeAt(i)];
        if (p1 > p2) {
            return 1;
        }
        if (p1 < p2) {
            return -1;
        }
    }
    if (op1.length > op2.length) {
        return 1;
    }
    if (op2.length > op1.length) {
        return -1;
    }
    if (op1 === '**') {
        return 1;
    }
    return -1;
}

export function parse(source: string, file: FileId): Either<Ast[], SourceRangeMessage[]> {
    let cursor = 0;
    const diagnostics: SourceRangeMessage[] = [];
    let token = scanToken();
    let lah: Token[] = [];

    try {
        return {isLeft: true, value: parseFile()};
    } catch (e) {
        return {isLeft: false, value: diagnostics};
    }

    function scanOperator(start: number): Token {
        while (cursor < source.length && isOperatorPart(source.charCodeAt(cursor))) {
            cursor++;
        }
        const value = source.substring(start, cursor);
        if (cursor < source.length && source.charCodeAt(cursor) === CCODE_EQUAL) {
            cursor++;
            return {
                kind: TokenKind.ASSIGN_OPERATOR,
                start,
                length: cursor - start,
                file,
                value,
            };
        } else {
            return {
                kind: TokenKind.OPERATOR,
                start,
                length: cursor - start,
                file,
                value,
            };
        }
    }

    function scanToken(): Token {
        while (cursor < source.length && isWhitespace(source.charCodeAt(cursor))) {
            cursor++;
        }
        const start = cursor;
        function tk(kind: TokenKind): Token {
            return {
                kind,
                start,
                length: cursor - start,
                value: null,
                file,
            };
        }
        if (cursor >= source.length) {
            return tk(TokenKind.EOF);
        }
        switch (source.charCodeAt(cursor)) {
            case CCODE_COLON: cursor++; return tk(TokenKind.COLON);
            case CCODE_EQUAL:
                cursor++;
                if (cursor < source.length + 1 && source.charCodeAt(cursor) === CCODE_EQUAL && source.charCodeAt(cursor + 1) === CCODE_EQUAL) {
                    cursor += 2;
                    return tk(TokenKind.EQUIV);
                } else {
                    return tk(TokenKind.ASSIGN);
                }
            case CCODE_OPEN_PARENTH: cursor++; return tk(TokenKind.OPEN_PARENTH);
            case CCODE_CLOSE_PARENTH: cursor++; return tk(TokenKind.CLOSE_PARENTH);
            case CCODE_OPEN_BRACKET: cursor++; return tk(TokenKind.OPEN_BRACKET);
            case CCODE_CLOSE_BRACKET: cursor++; return tk(TokenKind.CLOSE_BRACKET);
            case CCODE_OPEN_BRACE: cursor++; return tk(TokenKind.OPEN_BRACE);
            case CCODE_CLOSE_BRACE: cursor++; return tk(TokenKind.CLOSE_BRACE);
            case CCODE_COMMA: cursor++; return tk(TokenKind.COMMA);
            case CCODE_DOT: cursor++; return tk(TokenKind.DOT);
            case CCODE_EAR: cursor++; return tk(TokenKind.EAR);
            case CCODE_SEMI_COLON: cursor++; return tk(TokenKind.SEMI_COLON);
            case CCODE_DASH:
                cursor++;
                if (cursor < source.length && source.charCodeAt(cursor) === CCODE_GT) {
                    cursor++;
                    return tk(TokenKind.ARROW);
                } else {
                    return scanOperator(start);
                }
            case CCODE_BSLASH:
                cursor++;
                if (cursor < source.length && source.charCodeAt(cursor) === CCODE_BSLASH) {
                    cursor++;
                    return tk(TokenKind.DOUBLE_BSLASH);
                } else {
                    return tk(TokenKind.BSLASH);
                }
            default: {
                if (isDigit(source.charCodeAt(cursor))) {
                    const c = cursor;
                    let value = 0;
                    while (cursor < source.length && isDigit(source.charCodeAt(cursor))) {
                        value *= 10;
                        value += source.charCodeAt(cursor) - CCODE_0;
                        cursor++;
                    }
                    return {
                        kind: TokenKind.NUMBER,
                        value,
                        start,
                        length: cursor - start,
                        file,
                    };
                }
                if (isOperatorPart(source.charCodeAt(cursor))) {
                    return scanOperator(start);
                }
                if (isIdentifierStart(source.charCodeAt(cursor))) {
                    let value = '';
                    while (cursor < source.length && isIdentifierPart(source.charCodeAt(cursor))) {
                        value += source.charAt(cursor);
                        cursor++;
                    }
                    if (KEYWORKDS.hasOwnProperty(value)) {
                        return tk(KEYWORKDS[value]);
                    } else return {
                        kind: TokenKind.IDENTIFIER,
                        value,
                        start,
                        length: cursor - start,
                        file,
                    };
                } else {
                    diagnostics.push({
                        msg: 'unexpected character ' + source.charAt(cursor),
                        start,
                        length: 1,
                        file,
                    });
                    throw new Error();
                }
            }
        }
    }

    function nextToken() {
        if (lah.length > 0) {
            token = lah.shift()!;
        } else {
            token = scanToken();
        }
    }

    function unexpected(): never {
        diagnostics.push({...asSourceRange(token), msg: 'unexpected token'});
        throw new Error();
    }

    function expect(tk: TokenKind) {
        if (token.kind !== tk) {
            unexpected();
        }
        nextToken();
    }

    function doLah(count: number) {
        while (lah.length < count) {
            lah.push(scanToken());
        }
    }

    function clearLah() {
        token = lah[lah.length - 1];
        lah.length = 0;
    }

    function parseIdentifier(): AstIdentifier {
        if (token.kind === TokenKind.IDENTIFIER) {
            const ret: AstIdentifier = {...asSourceRange(token), kind: AstKind.IDENTIFIER, name: token.value as string};
            nextToken();
            return ret;
        } else unexpected();
    }

    function parseExpression(): Ast {
        if (token.kind === TokenKind.BSLASH) {
            const s = token.start;
            nextToken();
            const name = parseIdentifier();
            const body = parseExpression();
            return {kind: AstKind.LAMBDA, arg: name, body, file, start: s, length: token.start - s};
        }
        return parseFnType();
    }

    function isFnTypeStart() {
        if (token.kind === TokenKind.OPEN_PARENTH) {
            doLah(2);
            return lah[0].kind === TokenKind.IDENTIFIER && lah[1].kind === TokenKind.COLON;
        } else return token.kind === TokenKind.OPEN_BRACKET;
    }

    function parseFnArg(): [AstIdentifier, Ast | undefined] {
        const arg = parseIdentifier();
        let type: Ast | undefined = void 0;
        if (tryExpect(TokenKind.COLON)) {
            type = parseExpression();
        }
        return [arg, type];
    }

    function parseFnTypeArgs(): AstFnTypeArgList {
        const start = token.start;
        const args: [AstIdentifier, Ast | undefined][] = [];
        const color = token.kind === TokenKind.OPEN_BRACKET ? 1 : 0;
        const closeToken = color === 0 ? TokenKind.CLOSE_PARENTH : TokenKind.CLOSE_BRACKET;
        nextToken();
        args.push(parseFnArg());
        while (token.kind === TokenKind.COMMA as TokenKind) {
            nextToken();
            if (token.kind === closeToken) break;
            args.push(parseFnArg());
        }
        expect(closeToken);
        return {isArgList: true, args, color, file, start, length: token.start - start};
    }

    function parseFnTypeArgLists(): AstFnTypeArgList[] {
        const ret: AstFnTypeArgList[] = [];
        while (token.kind === TokenKind.OPEN_PARENTH || token.kind === TokenKind.OPEN_BRACKET) {
            ret.push(parseFnTypeArgs());
        }
        return ret;
    }

    function parseFnType(): Ast {
        const s = token.start;
        if (isFnTypeStart()) {
            const args = parseFnTypeArgs();
            if (isFnTypeStart()) {
                const outputType = parseExpression();
                return {kind: AstKind.FN_TYPE, inputType: args, outputType, file, start: s, length: token.start - s};
            } else {
                expect(TokenKind.ARROW);
                const outputType = parseExpression();
                return {kind: AstKind.FN_TYPE, inputType: args, outputType, file, start: s, length: token.start - s};
            }
        } else return parseNonDependentFnType();
    }

    function parseNonDependentFnType(): Ast {
        const s = token.start;
        const inputType = parseBinaryExpression();
        if (token.kind === TokenKind.ARROW) {
            nextToken();
            const outputType = parseExpression();
            return {
                kind: AstKind.FN_TYPE,
                inputType: {isArgList: false, type: inputType},
                outputType,
                file,
                start: s,
                length: token.start - s,
            };
        } else {
            return inputType;
        }
    }

    function parseBinaryExpression(): Ast {
        const s = token.start;
        function popStack() {
            const op = opStack.pop()!;
            const right = operandStack.pop()!;
            const left = operandStack.pop()!;
            operandStack.push({kind: AstKind.BINARY, left, right, operator: op.value as string, file, start: left.start, length: right.start + right.length - left.start});
        }
        const opStack: Token[] = [];
        const operandStack = [parseUnaryExpression()];
        while (token.kind === TokenKind.OPERATOR) {
            while (opStack.length > 0 && compareOperatorPrecedence(token.value as string, opStack[opStack.length - 1].value as string) < 0) {
                popStack();
            }
            opStack.push(token);
            nextToken();
            operandStack.push(parseUnaryExpression());
        }
        while (opStack.length > 0) {
            popStack();
        }
        return operandStack.pop()!;
    }

    function tryExpect(tk: TokenKind) {
        if (token.kind === tk) {
            nextToken();
            return true;
        }
        return false;
    }

    function parseUnaryExpression(): Ast {
        const s = token.start;
        if (token.kind === TokenKind.BREAK || token.kind === TokenKind.CONTINUE) {
            const isbreak = token.kind === TokenKind.BREAK;
            nextToken();
            let label: AstIdentifier | undefined = void 0;
            if (tryExpect(TokenKind.COLON)) {
                label = parseIdentifier();
            }
            const expr = parseExpression();
            const length = token.start - s;
            return isbreak ? {kind: AstKind.BREAK, label, expr, file, start: s, length} : {kind: AstKind.CONTINUE, label, expr, file, start: s, length};
        }
        return parseTrailerExpression();
    }

    function parseTrailerExpression() {
        let expr = parsePrimitiveExpression();
        while (true) {
            switch (token.kind) {
                case TokenKind.DOT: {
                    nextToken();
                    const name = parseIdentifier();
                    expr = {kind: AstKind.MEMBER_ACCESS, lhs: expr, member: name, file, start: expr.start, length: token.start - expr.start};
                    break;
                }
                case TokenKind.OPEN_BRACKET:
                case TokenKind.OPEN_PARENTH: {
                    expr = parseArgLists(expr);
                    break;
                }
                case TokenKind.OPEN_BRACE: {
                    expr = parseStructLiteral(expr, expr.start);
                    break;
                }
                default: return expr;
            }
        }
    }

    function parseArgList(fn: Ast): Ast {
        let color: number;
        if (token.kind === TokenKind.OPEN_PARENTH as TokenKind) {
            color = 0;
        } else if (token.kind === TokenKind.OPEN_BRACKET) {
            color = 1;
        } else unexpected();
        nextToken();
        if (token.kind === TokenKind.CLOSE_PARENTH as TokenKind|| token.kind === TokenKind.CLOSE_BRACKET as TokenKind) {
            nextToken();
            return {kind: AstKind.CALL, fn, file, start: fn.start, length: token.start - fn.start, color: 0};
        }
        fn = {kind: AstKind.CALL, arg: parseExpression(), fn, color, start: fn.start, length: token.start - fn.start, file};
        while (token.kind === TokenKind.COMMA as TokenKind) {
            nextToken();
            if (token.kind === TokenKind.CLOSE_PARENTH || token.kind === TokenKind.CLOSE_BRACKET) {
                break;
            }
            fn = {kind: AstKind.CALL, arg: parseExpression(), fn, color, start: fn.start, length: token.start - fn.start, file};
        }
        expect(color === 0 ? TokenKind.CLOSE_PARENTH : TokenKind.CLOSE_BRACKET);
        return fn;
    }

    function parseArgLists(fn: Ast): Ast {
        while (token.kind === TokenKind.OPEN_PARENTH || token.kind === TokenKind.OPEN_BRACKET) {
            fn = parseArgList(fn);
        }
        return fn;
    }

    function parseStructLiteral(type: Ast | undefined, start: number): Ast {
        const args: [AstIdentifier | undefined, Ast][] = [];
        expect(TokenKind.OPEN_BRACE);
        if (token.kind !== TokenKind.CLOSE_BRACE as TokenKind) {
            args.push(parseStructLiteralElement());
            while (token.kind === TokenKind.COMMA) {
                nextToken();
                if (token.kind === TokenKind.CLOSE_BRACE as TokenKind) {
                    break;
                }
                args.push(parseStructLiteralElement());
            }
        }
        return {kind: AstKind.STRUCT_LITERAL, type, args, file, start, length: token.start - start};
    }

    function parseStructLiteralElement(): [AstIdentifier | undefined, Ast] {
        if (token.kind === TokenKind.IDENTIFIER) {
            doLah(1);
            if (lah[0].kind === TokenKind.COLON) {
                const name = parseIdentifier();
                clearLah();
                return [name, parseExpression()];
            }
        }
        return [void 0, parseExpression()];
    }

    function parseLabels() {
        const ret: AstIdentifier[] = [];
        while (true) {
            if (token.kind === TokenKind.IDENTIFIER as TokenKind) {
                doLah(1);
                if (token.kind as TokenKind === TokenKind.COLON as TokenKind) {
                    ret.push(parseIdentifier());
                    nextToken();
                } else return ret;
            } else return ret;
        }
    }

    function parsePrimitiveExpression(): Ast {
        const labels = parseLabels();
        switch (token.kind as TokenKind) {
            case TokenKind.IDENTIFIER: {
                const ret: Ast = {...asSourceRange(token), kind: AstKind.IDENTIFIER, name: token.value as string};
                nextToken();
                return ret;
            }
            case TokenKind.NUMBER: {
                const ret: Ast = {...asSourceRange(token), kind: AstKind.NUMBER, value: token.value as number};
                nextToken();
                return ret;
            }
            case TokenKind.STRING: {
                const ret: Ast = {...asSourceRange(token), kind: AstKind.STRING, value: token.value as string};
                nextToken();
                return ret;
            }
            case TokenKind.DOT: {
                const start = token.start;
                nextToken();
                return parseStructLiteral(void 0, start);
            }
            case TokenKind.EAR: {
                const start = token.start;
                nextToken();
                let name: AstIdentifier | undefined = void 0
                if (token.kind === TokenKind.IDENTIFIER) {
                    name = parseIdentifier();
                }
                return {kind: AstKind.PATTERN, name, file, start, length: token.start - start};
            }
            case TokenKind.OPEN_PARENTH: {
                nextToken();
                const ret = parseExpression();
                expect(TokenKind.CLOSE_PARENTH);
                return ret;
            }
            case TokenKind.OPEN_BRACE: return parseBlock(labels[0]);
            default: unexpected();
        }
    }

    function parseSemicolons() {
        while (token.kind === TokenKind.SEMI_COLON) {
            nextToken();
        }
    }

    function parseModule(): Ast {
        const start = token.start;
        expect(TokenKind.MODULE);
        const name = parseIdentifier();
        expect(TokenKind.OPEN_BRACE);
        const decls: Ast[] = [];
        while (token.kind !== TokenKind.CLOSE_BRACE) {
            decls.push(parseModuleDecl());
            parseSemicolons();
        }
        expect(TokenKind.CLOSE_BRACE);
        return {kind: AstKind.MODULE, name, decls, file, start, length: token.start - start};
    }

    function parseLet(requireInitializer: boolean, isPub: boolean): AstLet {
        const start = token.start;
        let isVar = false;
        if (token.kind === TokenKind.LET) {
            nextToken();
        } else if (token.kind === TokenKind.VAR) {
            isVar = true;
            nextToken();
        } else unexpected();
        const isInline = tryExpect(TokenKind.INLINE);
        const name = parseIdentifier();
        let type: Ast | undefined = void 0;
        if (tryExpect(TokenKind.COLON)) {
            type = parseExpression();
        }
        let initializer: Ast | undefined = void 0;
        if (tryExpect(TokenKind.ASSIGN)) {
            initializer = parseExpression();
        } else if (requireInitializer) unexpected();
        return {kind: AstKind.LET, isPub, isVar, isInline, name, type, initializer, file, start, length: token.start - start};
    }

    function parseAssign(): Ast {
        const lhs = parseExpression();
        if (token.kind === TokenKind.ASSIGN || token.kind === TokenKind.ASSIGN_OPERATOR) {
            const operator = (token.value ?? '') as string;
            const rhs = parseExpression();
            return {kind: AstKind.ASSIGN, operator, lhs, rhs, file, start: lhs.start, length: token.start - lhs.start};
        }
        return lhs;
    }

    function parseBlock(label?: AstIdentifier): AstBlock {
        const start = token.start;
        const body: Ast[] = [];
        expect(TokenKind.OPEN_BRACE);
        while (token.kind !== TokenKind.CLOSE_BRACE) {
            switch (token.kind) {
                case TokenKind.VAR:
                case TokenKind.LET:
                    body.push(parseLet(true, false));
                    parseSemicolons();
                    break;
                case TokenKind.DEFER: {
                    const start = token.start;
                    const b = parseExpression();
                    body.push({kind: AstKind.DEFER, body: b, file, start, length: token.start - start});
                    parseSemicolons();
                    break;
                }
                default:
                    body.push(parseAssign());
                    parseSemicolons();
                    break;
            }
        }
        expect(TokenKind.CLOSE_BRACE);
        return {kind: AstKind.BLOCK, label, body, file, start, length: token.start - start};
    }

    function parseStructLike(start: number, variant: StructVariant): AstStructLike {
        let type: Ast | undefined = void 0;
        if (token.kind !== TokenKind.OPEN_BRACE) {
            type = parseExpression();
        }
        expect(TokenKind.OPEN_BRACE);
        const fields: AstStructField[] = [];
        const decls: AstLet[] = [];
        while (token.kind !== TokenKind.CLOSE_BRACE) {
            const isPub = tryExpect(TokenKind.PUB);
            if (token.kind === TokenKind.IDENTIFIER as TokenKind) {
                const name = parseIdentifier();
                expect(TokenKind.COLON);
                const type = parseExpression();
                let defaultValue: Ast | undefined = void 0;
                if (variant === StructVariant.ENUM && tryExpect(TokenKind.ASSIGN)) {
                    defaultValue = parseExpression();
                }
                if (token.kind === TokenKind.COMMA) {
                    nextToken();
                } else {
                    parseSemicolons();
                }
                fields.push({name, type, defaultValue, isPub});
            } else {
                decls.push(parseLet(false, isPub));
                parseSemicolons();
            }
        }
        expect(TokenKind.CLOSE_BRACE);
        return {kind: AstKind.STRUCT, variant, type, fields, decls, start, length: token.start - start, file};
    }

    function parseModuleDecl(): Ast {
        const start = token.start;
        switch (token.kind) {
            case TokenKind.VARIABLE: {
                const name = parseIdentifier();
                let type: Ast | undefined = void 0;
                if (tryExpect(TokenKind.COLON)) {
                    type = parseExpression();
                }
                return {kind: AstKind.VARIABLE, name, type, file, start, length: token.start - start};
            }
            case TokenKind.MODULE: return parseModule();
            default: {
                const lhs = parseExpression();
                let type: Ast | undefined = void 0;
                let initializer: Ast | undefined = void 0;
                if (tryExpect(TokenKind.COLON)) {
                    type = parseExpression();
                }
                if (tryExpect(TokenKind.ASSIGN)) {
                    initializer = parseExpression();
                }
                return {kind: AstKind.MODULE_DECL, lhs, type, rhs: initializer, file, start, length: token.start - start};
            }
        }
    }

    function parseFile(): Ast[] {
        const start = token.start;
        const decls: Ast[] = [];
        while (token.kind !== TokenKind.EOF) {
            decls.push(parseModuleDecl());
            parseSemicolons();
        }
        return decls;
    }
}
