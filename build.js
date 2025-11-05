import { watch } from 'rolldown';

const watcher = watch({
    input: 'bootstrap/main.ts',
    output: {
        file: 'dist/main.js',
        sourcemap: true,
    },
});

watcher.close();
