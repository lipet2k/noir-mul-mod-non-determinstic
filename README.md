# Nondeterministic Bigint Modular Multiplication

Prototype of the modular multiplication algorithm described in this paper https://blog.polygon.technology/wp-content/uploads/2022/10/casting-3.pdf

This Repository contains the following:

- `circuits/src/main.nr` is a simple example that validates a modular multiplication product using the nondetermnistic method
- `circuits/Prover.toml` contains the witness data
- `js/helper.ts` contains some helper functions that
  - generates the required parameters for a given modulo (`q`)
  - generates the witness data for validating the modular product (`z_mod_q`) given multiplicands (`x` & `y`)

## How to use it

Edit `js/helper.ts` with the `x`, `y`, and `q` for which you want to compute the product.

``` bash
# From the js directory
npm run generate-params
```

Copy the parameters into the modular multiplication circuit `circuits/src/main.nr`
Copy the witness data into `circuits/Prover.toml`

``` bash
# From the circuits directory
nargo prove main
```
