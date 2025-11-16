import {readFile} from 'fs/promises';
import { FileId, renderSourceMessage } from './parser';
import { BuiltinSymbols, checkTypes, renderTypeCheckResult, SymbolRegistry } from './analyse';
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

async function run(entry: string, logger: Logger) {
    const file = await readFile(entry, 'utf-8');
    const lines = file.split('\n').map(e => e + '\n');
    const reg = new SymbolRegistry(null);
    const builtins = new BuiltinSymbols(reg);
    const parseResult = parseAndIrgen(builtins, builtins.getInitialScope(), file, 0 as FileId);
    if (parseResult.isLeft) {
        logger.info(() => parseResult.value.dump(reg));
        const typeCheck = checkTypes(reg, builtins, parseResult.value, logger);
        if (typeCheck !== null) {
            for (const line of renderTypeCheckResult(typeCheck)) {
                console.log(line);
            }
        } else {
            logger.info(() => reg.dump());
        }
    } else {
        for (const msg of parseResult.value) {
            for (const l of renderSourceMessage(msg, () => [entry, lines])) {
                console.log(l);
            }
        }
    }
}

run(process.argv[2], NO_LOG);
