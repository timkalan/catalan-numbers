# Catalan numbers

Formalization project for the course Logika v računalništvu, FMF, 2023/24.

$$
C_0 := 0, ~ C_{n+1} := \sum_{i=0}^{n} C_i C_{n-i}
$$

## Instructions
Create a Lean project that uses `mathlib` as a dependency by running the command:
```bash
lake +leanprover-community/mathlib4:lean-toolchain new catalan-numbers math
```
`cd` into the newly created `catalan-numbers` folder and run the command:
```bash
lake exe cache get
```
Then you can clone this repo and place the file `catalan_numbers.lean`into the
`CatalanNumbers` folder of the `catalan-numbers` project. The entire project is 
contained in this file.

## Troubleshooting
- For mathlib related issues, look at [this](https://github.com/leanprover-community/mathlib4/wiki/Using-mathlib4-as-a-dependency)
- Sometimes, running `lake update` from inside the project directory helps (at the risk of rebuilding `mathlib`