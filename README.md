# Catalan numbers

Formalization project for the course Logika v računalništvu, FMF, 2023/24.

$$
C_0 := 0, ~ C_{n+1} := \sum_{i=0}^{n} C_i C_{n-i}
$$

## Instructions
Clone the project, `cd` into it and configure `mathlib` by running the command:
```bash
lake exe cache get
```
In case of any issues, try first running `lake clean`. If issues persist, deleting 
the `.lake/` directory and running `lake exe cache get` again should solve the problem.

## Troubleshooting
- For mathlib related issues, look at [this](https://github.com/leanprover-community/mathlib4/wiki/Using-mathlib4-as-a-dependency)
- Sometimes, running `lake update` from inside the project directory helps (at the risk of rebuilding `mathlib`
