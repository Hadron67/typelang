export class IndexedMap<K, V> {
    readonly byName: Map<K, number> = new Map();
    readonly byId: V[] = [];
    getId(name: K): number | undefined {
        return this.byName.get(name);
    }
    getById(id: number): V {
        return this.byId[id];
    }
    get(name: K): V | undefined {
        const id = this.byName.get(name);
        return id === void 0 ? void 0 : this.byId[id];
    }
    add(name: K, value: V): number {
        const id = this.byId.length;
        this.byName.set(name, id);
        this.byId.push(value);
        return id;
    }
    // getNextUniqueName(name: K) {
    //     let counter = 0;
    //     let altName = name;
    //     while (this.byName.has(altName)) {
    //         altName = name + '.' + counter.toString();
    //         counter++;
    //     }
    //     return altName;
    // }
    getNextId() {
        return this.byId.length;
    }
}

export function panic(msg?: string): never {
    throw new Error(msg ?? '<no further info>');
}

export function assert(cond: unknown): asserts cond {
    if (!cond) {
        panic('assertion failed');
    }
}

export function pushReversed<T, U extends T>(dest: T[], src: U[]) {
    for (let i = 0; i < src.length; i++) {
        dest.push(src[src.length - 1 - i]);
    }
}

export function popReversed<T, U extends T>(dest: U[], src: T[], length: number) {
    src.length += length;
    for (let i = 0; i < length; i++) {
        src[src.length - i - 1] = dest.pop() ?? panic();
    }
}

export function copyMap<K, V>(map: Map<K, V>): Map<K, V> {
    const ret: Map<K, V> = new Map();
    map.forEach((k, v) => ret.set(v, k));
    return ret;
}

export function complement<K, V>(map: Map<K, V>, set: Set<K>) {
    const ret = copyMap(map);
    set.forEach(v => ret.delete(v));
    return ret;
}

export function constArray<T>(value: T, length: number) {
    const ret: T[] = [];
    for (let i = 0; i < length; i++) {
        ret.push(value);
    }
    return ret;
}

export type Either<L, R> = EitherLeft<L> | EitherRight<R>;

export interface EitherLeft<T> {
    readonly isLeft: true;
    readonly value: T;
}

export interface EitherRight<T> {
    readonly isLeft: false;
    readonly value: T;
}

export type Mutable<T> = {
    -readonly [P in keyof T]: T[P]
}
