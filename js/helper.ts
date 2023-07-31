(BigInt.prototype as any).toJSON = function() { return this.toString() }

const primes = [
  74684543326020202269309830312831319757532706564253n,
  33691779876666245027903078753942696838547278695717n,
  20598741005597686126931828390945874928273828922699n,
  94853440291242852401182618564733101294907538620699n,
  40835068024229774243647547425594128160481750366071n,
  70452110497633128172916554766885687618496820260271n,
  14936141114781610764017981716380571117082719917853n,
  41511757973927508900846697623173071685243017785227n,
  16916887828722141846501982182026707187947653247991n,
  58723683284513808772674981369925821477489704790317n,
];

const findModuli = (useNativeFieldAsModulo: boolean, nativeField: bigint, nonNativeField: bigint, numLimbs: bigint, base: bigint) => {
    let lcm = 1n;
    const moduli: bigint[] = [];
    if (useNativeFieldAsModulo) {
        lcm = lcm * nativeField;
        moduli.push(nativeField);
    }
    while (lcm < (2n * (numLimbs ** 2n) * nonNativeField * (base ** 2n))) {
        const prime = primes.shift();
        if (prime === undefined) {
            throw new Error('LCM constraint not satisfied');
        }
        moduli.push(prime);
        lcm = lcm * prime;
    }
    const moduliMax = nativeField / (4n * (numLimbs ** 2n) * (base ** 2n));
    // To avoid wrap-around, we require each mi (except for p itself)
    // to satisfy mi ≤ p/(4n^2b^2)
    const wrapAroundConstraintSatisfied = moduli.every((mi) => {
        return mi === nativeField || mi <= moduliMax;
    });
    if (!wrapAroundConstraintSatisfied) {
        throw new Error('Wrap-around constraint not satisfied');
    }
    return moduli;
};

// Returns little-endian
const baseConverter = (num: bigint, base: bigint): bigint[] => {
    let unconverted = num;
    const converted: bigint[] = [];
    while (unconverted >= base) {
        converted.unshift(unconverted % base);
        unconverted /= base;
    }
    converted.unshift(unconverted);
    return converted.reverse();
}

const partiallyReducedProduct = (base : bigint, reductionModulo : bigint, x : bigint[], y : bigint[]): bigint => {
    const product = x.map(x_i => BigInt(x_i)).reduce((outerSum, x_i, i) => {
        return outerSum + y.map(y_j => BigInt(y_j)).reduce((innerSum, y_j, j) => {
            const iPlusJ = BigInt(i + j);
            return innerSum + ((base**iPlusJ) % reductionModulo) * (x_i * y_j);
         }, 0n);
    }, 0n);
    return product;
}

const partiallyReducedProductModQ = (base : bigint, q : bigint, reductionModulo : bigint, x : bigint[], y : bigint[]): bigint => {
    const product = x.map(x_i => BigInt(x_i)).reduce((outerSum, x_i, i) => {
        return outerSum + y.map(y_j => BigInt(y_j)).reduce((innerSum, y_j, j) => {
            const iPlusJ = BigInt(i + j);
            const baseExponentiation = (((base**iPlusJ) % q) % reductionModulo);
            return innerSum + baseExponentiation * (x_i * y_j);
         }, 0n);
    }, 0n);
    return product;
}

const partiallyReducedSum = (base : bigint, reductionModulo : bigint, x : bigint[]): bigint => {
    const sum = x.map(x_i => BigInt(x_i)).reduce((s, x_i, i) => {
        return s + ((base**BigInt(i)) % reductionModulo) * x_i;
    }, 0n);
    return sum;
}

const partiallyReducedSumModQ = (base : bigint, q : bigint, reductionModulo : bigint, x : bigint[]): bigint => {
    const sum = x.map(x_i => BigInt(x_i)).reduce((s, x_i, i) => {
        return s + (((base**BigInt(i)) % q) % reductionModulo) * x_i;
    }, 0n);
    return sum;
}

const padArrayToLen = (arr: bigint[], len: number): bigint[] => {
    return Array.from({length: len}, (_, i) => arr[i] ?? 0n)
};

const stringifyBigintArray = (arr: bigint[]): string => {
    let str = JSON.stringify(arr);
    // remove quotes
    str = str.replace(/"/ig, '');
    // separate values by ', '
    str = str.replace(/,/ig, ', ');
    return str;
}

const genProverToml = (numLimbs: number, x: bigint[], y: bigint[], zModQ: bigint[], r: bigint, s: bigint[]): string => {
    let tomlStr = '# Prover.toml'
    tomlStr += `\nx=${stringifyBigintArray(padArrayToLen(x, numLimbs))}`;
    tomlStr += `\ny=${stringifyBigintArray(padArrayToLen(y, numLimbs))}`;
    tomlStr += `\nz_mod_q=${stringifyBigintArray(padArrayToLen(zModQ, numLimbs))}`;
    tomlStr += `\nr=${r}`;
    tomlStr += `\ns=${stringifyBigintArray(s)}`;
    return tomlStr;
}

const genParamsStruct = (numLimbs: number, base: bigint, q: bigint[], m: bigint[], qModM: bigint[], baseExponentiations: bigint[][]): string => {
    let paramsStructStr = 'MulModNonDetermParams {';
    paramsStructStr += `\nbase: ${base},`;
    paramsStructStr += `\nq: ${stringifyBigintArray(padArrayToLen(q, numLimbs))},`;
    paramsStructStr += `\nm: ${stringifyBigintArray(m)},`;
    paramsStructStr += `\nq_mod_m: ${stringifyBigintArray(qModM)},`;
    paramsStructStr += `\nbase_exponentiations: ${stringifyBigintArray(baseExponentiations.flat())},`;
    paramsStructStr += `\n}`;
    return paramsStructStr;
}

const mulModNonDeterministicHelper = (
    b: bigint,
    numLimbs: number,
    x: bigint,
    y: bigint,
    q: bigint,
    m: bigint[],
    useNativeFieldAsModulo: boolean,
) => {
    const baseExponentiations: bigint[][] = [];
    const qModM: bigint[] = [];
    const s: bigint[] = []; // witness
    const zModQ = (x * y) % q;
    const xBase32 = baseConverter(x, b); // witness
    const yBase32 = baseConverter(y, b); // witness
    const qBase32 = baseConverter(q, b); // witness
    const zModQBase32 = baseConverter(zModQ, b); // witness
    const productReducedQ = partiallyReducedProduct(b, q, xBase32, yBase32);
    const sumReducedQ = partiallyReducedSum(b, q, zModQBase32);
    const r = (productReducedQ - sumReducedQ) / q; // witness
    m.forEach((m_i) => {
        const baseExponentiationsModQMi: bigint[] = [];
        for (let i = 0; i < (numLimbs - 1) * 2 + 1; i++) {
            const baseExponentiationModQMi = (b ** BigInt(i)) % q % m_i;
            baseExponentiationsModQMi.push(baseExponentiationModQMi);
        }
        const qModMi = q % m_i;
        qModM.push(qModMi);
        const productReducedQMi = partiallyReducedProductModQ(b, q, m_i, xBase32, yBase32);
        const sumReducedQMi = partiallyReducedSumModQ(b, q, m_i, zModQBase32);
        const s_i = (productReducedQMi - sumReducedQMi - (r * qModMi)) / m_i; // witness
        s.push(s_i);
        baseExponentiations.push(baseExponentiationsModQMi);
    });
    // console.log(`x=${x}`);
    // console.log(`y=${y}`);
    // console.log(`q=${q}`);
    // console.log(`z_mod_q=${zModQ}`);
    // console.log(`M=${JSON.stringify(m)}`.replace(/"/ig, '').replace(/,/ig, ', '));
    // console.log(`partially_reduced_product=${productReducedQ.valueOf()}`);
    // console.log(`partially_reduced_sum=${sumReducedQ.valueOf()}`);
    // console.log(`base_exponentiations=${JSON.stringify(baseExponentiations)}`.replace(/"/ig, '').replace(/,/ig, ', '));

    // console.log(`x=${JSON.stringify(padArrayToLen(xBase32, numLimbs))}`.replace(/"/ig, '').replace(/,/ig, ', '));
    // console.log(`y=${JSON.stringify(padArrayToLen(yBase32, numLimbs))}`.replace(/"/ig, '').replace(/,/ig, ', '));
    // console.log(`z_mod_q=${JSON.stringify(padArrayToLen(zModQBase32, numLimbs))}`.replace(/"/ig, '').replace(/,/ig, ', '));
    // console.log(`r=${r.valueOf()}`);
    // console.log(`s=${JSON.stringify(s)}`.replace(/"/ig, '').replace(/,/ig, ', '));
    // console.log(s.map(n => String(n).length));

    // console.log(`base: ${b.valueOf()},`);
    // console.log(`q: ${JSON.stringify(padArrayToLen(qBase32, numLimbs))}`.replace(/"/ig, '').replace(/,/ig, ', ') + ',');
    // if (useNativeFieldAsModulo) {
    //     m.shift();
    //     const nativeFieldQModM = qModM.shift();
    //     const nativeFieldBaseExponentiation = baseExponentiations.shift();
    //     console.log(`m: ${JSON.stringify(m)}`.replace(/"/ig, '').replace(/,/ig, ', ') + ',');
    //     console.log(`q_mod_m: ${JSON.stringify(qModM)}`.replace(/"/ig, '').replace(/,/ig, ', ') + ',');
    //     console.log(`base_exponentiations: ${JSON.stringify(baseExponentiations)}`.replace(/"/ig, '').replace(/,/ig, ', ') + ',');
    //     console.log(`native_field_q_mod_m: ${JSON.stringify(nativeFieldQModM)}`.replace(/"/ig, '').replace(/,/ig, ', ') + ',');
    //     console.log(`native_field_base_exponentiation: ${JSON.stringify(nativeFieldBaseExponentiation)}`.replace(/"/ig, '').replace(/,/ig, ', ') + ',');
    // } else {
    //     console.log(`m: ${JSON.stringify(m)}`.replace(/"/ig, '').replace(/,/ig, ', ') + ',');
    //     console.log(`q_mod_m: ${JSON.stringify(qModM)}`.replace(/"/ig, '').replace(/,/ig, ', ') + ',');
    //     console.log(`base_exponentiations: ${JSON.stringify(baseExponentiations)}`.replace(/"/ig, '').replace(/\],\[/ig, ',\n').replace(/,/ig, ', ') + ',');
    // }
    return {
        xBase32,
        yBase32,
        qBase32,
        zModQBase32,
        r,
        s,
        qModM,
        baseExponentiations,
    }
}


const run = () => {
    const curveBN254 = 21888242871839275222246405745257275088548364400416034343698204186575808495617n;
    const curve25519 = 57896044618658097711785492504343953926634992332820282019728792003956564819949n;
    const useNativeFieldAsModulo = false;
    const base = 4294967296n;
    const numLimbs = 16;
    const x = 10000000000000000000000000000000000000n;
    const y = 2000000000000000000000000n;
    const q = 7119287143249333354889128798179350518180399418416332829217664645868799761194181510624307827552671999981622353090775540065012971162867986538013940058153311n;

    const non_native =
      9949599596347937514759676162951696763606409586138110515321513215962748617538766726657044390691573709021009246340083902867062520099469280056178304467241551n;

    const m = findModuli(
      useNativeFieldAsModulo,
      curveBN254,
      non_native,
      BigInt(numLimbs),
      2n ** 32n
    );

    const {
        xBase32,
        yBase32,
        qBase32,
        zModQBase32,
        r,
        s,
        qModM,
        baseExponentiations,
    } = mulModNonDeterministicHelper(
        base,
        numLimbs,
        x,
        y,
        q,
        m,
        useNativeFieldAsModulo,
    );

    console.log(genProverToml(numLimbs, xBase32, yBase32, zModQBase32, r, s));
    console.log();
    console.log(genParamsStruct(numLimbs, base, qBase32, m, qModM, baseExponentiations));
}
run();