# Catalan numbers

$$
C_{n+1} = \sum_{i=0}^{n} C_i C_{n-i}
$$

## Troubleshooting
- For mathlib related issues, look at [this](https://github.com/leanprover-community/mathlib4/wiki/Using-mathlib4-as-a-dependency)
- Sometimes, running `lake update` from inside the project directory helps (at the risk of rebuilding `mathlib`)