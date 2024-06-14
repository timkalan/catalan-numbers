# Catalan numbers
Formalization project for the course Logika v računalništvu, FMF, 2023/24.

$$
C_0 := 0, ~ C_{n+1} := \sum_{i=0}^{n} C_i C_{n-i}
$$

## Structure of the project
All the project files are in the folder `CatalanNumbers`. All the small tasks are in the file `definitions.lean`. 
We completed 3 large tasks. They are the 4th, 5th, and 6th task. The 4th task i.e. showing an isomorphism between list plane trees and plane trees is in the file `list_plane_tree_isomorphism.lean`. The 5th task i.e. showing an isomorphism between full binary trees and plane trees(rotating isomorphism) is in the file `rotating_isomorphism.lean`. The 6th task i.e. showing that $(n+1) \mid {{2n}\choose{n}}$ is in the file `choose_divisibility.lean`.
 
## Instructions
Clone the project, `cd` into it and configure `mathlib` by running the command:
```bash
lake exe cache get
```
In case of any issues, try first running `lake clean`. If issues persist, deleting 
the `.lake/` directory and running `lake exe cache get` again should solve the problem.

## Troubleshooting
- For mathlib related issues, look at [this](https://github.com/leanprover-community/mathlib4/wiki/Using-mathlib4-as-a-dependency)
- Sometimes, running `lake update` from inside the project directory helps (at the risk of rebuilding `mathlib`)
