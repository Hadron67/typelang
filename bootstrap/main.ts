import {readFile} from 'fs/promises';
import { FileId, parse, renderSourceMessage } from './parser';
import { BuiltinSymbols, checkTypes, Expression, renderTypeCheckResult, SymbolRegistry } from './analyse';
import { HIRHost, irgen, parseAndIrgen } from './irgen';

async function run(entry: string) {
    const file = await readFile(entry, 'utf-8');
    const lines = file.split('\n').map(e => e + '\n');
    const reg = new SymbolRegistry(null);
    const builtins = new BuiltinSymbols(reg);
    const parseResult = parseAndIrgen(builtins, builtins.getInitialScope(), file, 0 as FileId);
    if (parseResult.isLeft) {
        console.log('hir:');
        for (const line of parseResult.value.dump(reg)) {
            console.log(line);
        }
        const typeCheck = checkTypes(reg, builtins, parseResult.value, true);
        if (typeCheck !== null) {
            for (const line of renderTypeCheckResult(typeCheck)) {
                console.log(line);
            }
        } else {
            for (const line of reg.dump()) {
                console.log(line);
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

run(process.argv[2]);
