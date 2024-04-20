import mathlib
import «CatalanNumbers».a_binary_trees

open BigOperators
open Finset
open Finset.antidiagonal


-- Define Catalan numbers: C(n+1) = ∑_{i=0}^{n} C(i)C(n-i), C(0) = 1

def catalan_number : ℕ → ℕ
| 0 => 1
| (n+1) => ∑ i : Fin (n+1), catalan_number i * catalan_number (n-i)

-- C(n) is the number of full binary trees with n nodes (excluding leaves)
