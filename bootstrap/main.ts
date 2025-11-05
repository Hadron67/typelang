import {readFile} from 'fs/promises';
import { FileId, parse, renderSourceMessage } from './parser';
import { BuiltinSymbols, Expression, SymbolRegistry } from './analyse';
import { HIRHost, irgen, parseAndIrgen } from './irgen';

async function run(entry: string) {
    const file = await readFile(entry, 'utf-8');
    const lines = file.split('\n').map(e => e + '\n');
    const reg = new SymbolRegistry(null);
    const builtins = new BuiltinSymbols(reg);
    const parseResult = parseAndIrgen(builtins, builtins.getInitialScope(), file, 0 as FileId);
    if (parseResult.isLeft) {
        for (const line of parseResult.value.dump(reg)) {
            console.log(line);
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
