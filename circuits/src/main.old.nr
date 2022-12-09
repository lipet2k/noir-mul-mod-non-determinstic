global NUM_LIMBS : Field = 8;
global PRODUCT_MODULI_LENGTH : Field = 15;
global NUM_REDUCTION_MODULI : Field = 3;
global NUM_BASE_EXPONENTIATIONS : Field = 15; // ((NUM_LIMBS - 1) * 2) + 1
global NUM_TOTAL_BASE_EXPONENTIATIONS : Field = 45; // NUM_BASE_EXPONENTIATIONS * NUM_REDUCTION_MODULI

struct MulModNonDetermParams {
    base : u124,
    q : [u32; NUM_LIMBS], // Bigint
    m : [u124; NUM_REDUCTION_MODULI],
    q_mod_m : [u124; NUM_REDUCTION_MODULI],
    base_exponentiations : [u124; NUM_TOTAL_BASE_EXPONENTIATIONS], // base^i mod q mod m_i
}

fn partially_reduced_sum_mod_q(base_exponentiations : [u124; NUM_BASE_EXPONENTIATIONS], x : [u124; NUM_LIMBS]) -> u124 {
    let mut result = 0;
    for i in 0..NUM_LIMBS {
        result = result + (base_exponentiations[i] * x[i]);
    };
    result
}

fn partially_reduced_product_mod_q(base_exponentiations : [u124; NUM_BASE_EXPONENTIATIONS], x : [u124; NUM_LIMBS], y : [u124; NUM_LIMBS]) -> u124 {
    let mut result = 0;
    for i in 0..NUM_LIMBS {
        for j in 0..NUM_LIMBS {
            result = result + (base_exponentiations[i + j] * (x[i] * y[j]));
        };
    };
    result
}

fn mul_mod_non_deterministic(
    params : MulModNonDetermParams,
    x : [u124; NUM_LIMBS],
    y : [u124; NUM_LIMBS],
    z_mod_q : [u124; NUM_LIMBS],
    r : u124,
    s : [u124; NUM_REDUCTION_MODULI],
) {
    constrain s[0] != 0;
    // parameter range checks
    // small-moduli checks
    // for i in 0..NUM_REDUCTION_MODULI {
    for i in 0..1 {
        let mut base_exponentiations = [0 as u124; NUM_BASE_EXPONENTIATIONS];
        for j in 0..NUM_BASE_EXPONENTIATIONS {
            base_exponentiations[j] = params.base_exponentiations[(i * NUM_BASE_EXPONENTIATIONS) + j];
        };
        let product = partially_reduced_product_mod_q(base_exponentiations, x, y);
        let sum = partially_reduced_sum_mod_q(base_exponentiations, z_mod_q);
        constrain product == 2418553383339735974797683108;
        // constrain sum == 196387155814770375;
        
        constrain base_exponentiations == [1, 46686251, 2591258, 21185481, 34901722, 9764953, 10249013, 980199, 38, 24785343, 48488027, 5371846, 26791234, 21209775, 39604055];
        constrain z_mod_q == [4104057479,1317660176,3369491359,1574675528,718719913,3448263837,3220071330,1040409407];

        // constrain sum == 196387155814770375;
        // constrain product - sum == 2418553383143348818982912733;
        constrain r * params.q_mod_m[i] == 37849704264603519;
        // constrain product - sum - r * (params.q_mod_m[i]) == 2418553383105499114718309214;
        // constrain s[i] == 48390639740259327582;
        // constrain params.m[i] == 49979777;
        // constrain s[i] * params.m[i] == 2418553383105499114718309214;
        // wrong
        // constrain s[i] * params.m[i] == 2418553383105499114768288991;
        let left = product - sum - (r * params.q_mod_m[i]);
        let right = s[i] * params.m[i];
        // constrain left == 2418553383105499114718309214;
        // constrain right == 2418553383105499114768288991;
        constrain left == right;
        // constrain product - sum - (r * params.q_mod_m[i]) == s[i] * params.m[i];
    };
    // let mut base_exponentiations = [0 as u124; NUM_BASE_EXPONENTIATIONS];
    // for j in 0..NUM_BASE_EXPONENTIATIONS {
    //     base_exponentiations[j] = params.base_exponentiations[j];
    // };
    // let product = partially_reduced_product_mod_q(base_exponentiations, x, y);
    // let sum = partially_reduced_sum_mod_q(base_exponentiations, z_mod_q);
    // constrain (product - sum - r * (params.q_mod_m[0])) as Field == s[0] * params.m[0] as Field;
}

fn mul_mod_25519_non_deterministic_params() -> MulModNonDetermParams {
    // Note the following params are particular to 256-bit bigints consisting of 8 32-bit limbs
    MulModNonDetermParams {
        base : 4294967296,
        q : [4294967277, 4294967295, 4294967295, 4294967295, 4294967295, 4294967295, 4294967295, 2147483647],
        m : [49979777, 49979791, 49979821],
        q_mod_m : [41411913, 31939193, 49837382],
        base_exponentiations : [
            1, 46686251, 2591258, 21185481, 34901722, 9764953, 10249013, 980199, 38, 24785343, 48488027, 5371846, 26791234, 21209775, 39604055,
            1, 46685061, 35006028, 4250591, 37651725, 22362509, 29321945, 45365690, 38, 24739633, 30754498, 11583085, 31331402, 118895, 14678508,
            1, 46682511, 42814328, 40881963, 19819749, 8070675, 38387916, 36165800, 38, 24641683, 27590192, 4140143, 3453147, 6806724, 9325999,
        ],
    }
}

fn main(
    x : [u124; NUM_LIMBS],
    y : [u124; NUM_LIMBS],
    z_mod_q : [u124; NUM_LIMBS],
    r : u124,
    // s : [u124; NUM_REDUCTION_MODULI],
) {
    constrain x != y;
    constrain x != z_mod_q;
    constrain r != 0;
    // |r| < n^2 * b^2
    let params = mul_mod_25519_non_deterministic_params();
    mul_mod_non_deterministic(
        params,
        x,
        y,
        z_mod_q,
        r,
        [48390639740259327583,60158973076642157527,74026630663740960542],
    );
    run_tests();
}

// fn main(
//     x : [u124; NUM_LIMBS],
// ) {
//     // |r| < n^2 * b^2
//     let params = mul_mod_25519_non_deterministic_params();
//     mul_mod_non_deterministic(
//         params,
//         x,
//         [2912727897,3590519536,1687587470,3896107618,1092831095,0,0,0],
//         [4104057479,1317660176,3369491359,1574675528,718719913,3448263837,3220071330,1040409407],
//         913981063,
//         [48390639740259327582,60158973076642157527,74026630663740960542],
//     );
// }


// Tests
fn run_tests() {
    test_partially_reduced_sum_mod_q();
    test_partially_reduced_product_mod_q();
}

// partially_reduced_product=2418553383339735974797683108
// partially_reduced_sum=196387155814770375
// partially_reduced_product=3006732901606345213513045969
// partially_reduced_sum=431951380955006953
// partially_reduced_product=3699837750325898577590623371
// partially_reduced_sum=473463755955903323

// partially_reduced_sum_mod_q
fn test_partially_reduced_sum_mod_q_case1() {
    // base_exponentiations : [
    //     1, 46686251, 2591258, 21185481, 34901722, 9764953, 10249013, 980199, 38, 24785343, 48488027, 5371846, 26791234, 21209775, 39604055,
    //     1, 46685061, 35006028, 4250591, 37651725, 22362509, 29321945, 45365690, 38, 24739633, 30754498, 11583085, 31331402, 118895, 14678508,
    //     1, 46682511, 42814328, 40881963, 19819749, 8070675, 38387916, 36165800, 38, 24641683, 27590192, 4140143, 3453147, 6806724, 9325999,
    // ],

    let base_exponentiations = [1, 46686251, 2591258, 21185481, 34901722, 9764953, 10249013, 980199, 38, 24785343, 48488027, 5371846, 26791234, 21209775, 39604055];
    let x=[4104057479,1317660176,3369491359,1574675528,718719913,3448263837,3220071330,1040409407];
    let expected_sum = 196387155814770375;
    let sum = partially_reduced_sum_mod_q(base_exponentiations, x);
    constrain sum == expected_sum;
}

fn test_partially_reduced_sum_mod_q() {
    test_partially_reduced_sum_mod_q_case1();
}

fn test_partially_reduced_product_mod_q_case1() {
    let base_exponentiations = [1, 46686251, 2591258, 21185481, 34901722, 9764953, 10249013, 980199, 38, 24785343, 48488027, 5371846, 26791234, 21209775, 39604055];
    let x=[3320379920,1938147428,1942509796,1795943184,24853,0,0,0];
    let y=[2912727897,3590519536,1687587470,3896107618,1092831095,0,0,0];
    let expected_product = 2418553383339735974797683108;
    let product = partially_reduced_product_mod_q(base_exponentiations, x, y);
    constrain product == expected_product;
}

fn test_partially_reduced_product_mod_q() {
    test_partially_reduced_product_mod_q_case1();
}
