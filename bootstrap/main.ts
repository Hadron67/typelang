import {readFile} from 'fs/promises';
import { FileId, renderSourceMessage } from './parser';
import { BuiltinSymbols, ConstraintSolver, Expression, ExpressionKind, ExpressionStringifier, HIRSolver, renderTypeCheckDiagnostic, SymbolExpression } from './analyse';
import { parseAndIrgen } from './irgen';
import { Logger } from './util';

const VERBOSE: Logger = {
    info(msg) {
        const l = msg();
        if (Array.isArray(l)) {
            for (const line of l) {
                console.log(line);
            }
        } else {
            console.log(l);
        }
    }
};

const NO_LOG: Logger = {
    info() {},
};

async function run(args: string[]) {
    let logger = NO_LOG;
    if (args[0] === '-v') {
        logger = VERBOSE;
        args.shift();
    }
    const entry = args[0];

    const file = await readFile(entry, 'utf-8');
    const lines = file.split('\n').map(e => e + '\n');
    const builtins = new BuiltinSymbols();
    const stringifier = new ExpressionStringifier();
    const parseResult = parseAndIrgen(builtins, builtins.getInitialScope(), file, 0 as FileId);

    const root: SymbolExpression = {kind: ExpressionKind.SYMBOL, name: 'root', flags: 0, downValueCount: 0, upValueCount: 0};
    if (parseResult.isLeft) {
        logger.info(() => parseResult.value.dump(stringifier));
        const typeCache = new WeakMap<Expression, Expression>();
        const evaluationCache = new WeakMap<Expression, Expression>();
        const csolver = new ConstraintSolver(logger, stringifier, builtins, typeCache, evaluationCache);
        const solver = new HIRSolver(root, parseResult.value.regs, csolver);
        solver.run();
        const diag = solver.collectDiagnostics();
        for (const line of stringifier.dumpSymbol(root)) {
            console.log(line);
        }
        if (diag.length > 0) {
            for (const d of diag) {
                for (const line of renderTypeCheckDiagnostic(d, stringifier)) {
                    console.log(line);
                }
            }
        }
    } else {
        for (const msg of parseResult.value) {
            for (const l of renderSourceMessage(msg, () => [entry, lines])) {
                console.log(l);
            }
        }
    }
}

run(process.argv.slice(2));
