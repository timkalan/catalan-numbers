import mathlib

-- SMALL TASKS

-- 1. Catalan number definition
def catalan_number : ℕ → ℕ
| 0 => 1
| (n+1) => ∑ i : Fin (n+1), catalan_number i * catalan_number (n-i)


-- 2. Plane tree definition
inductive plane_tree : Type
| node : List plane_tree → plane_tree


-- 3. Full binary tree definition
inductive full_binary_tree : Type
| leaf : full_binary_tree
| node : (T₁ T₂ : full_binary_tree) → full_binary_tree


-- 4. Full binary tree with n nodes (not counting leaves)
inductive full_binary_tree_n : ℕ → Type
| leaf : full_binary_tree_n 0
| node : (n : ℕ) → (T₁ T₂ : full_binary_tree_n n) → full_binary_tree_n (n+1)


-- 5. Ballot sequences of length n
inductive ballot_sequence : ℕ → Type
| empty : ballot_sequence 0
| plus_one : ballot_sequence n → ballot_sequence (n + 1)
| minus_one : ballot_sequence (n + 1) → ballot_sequence n
