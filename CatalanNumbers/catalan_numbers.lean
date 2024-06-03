import mathlib

open BigOperators
open Finset
open Finset.antidiagonal


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



-- LARGER TASKS


-- 1. Fin-sum bijection
def k : Fin n → ℕ := Fin.val

-- def fin_of_sum :

-- 3. full binary tree ≅ Fin catalan_number n


-- 4. list plane tree ≅ plane tree
-- Define both directions as functions and prove that they are inverses of each other
-- One direction is simply plane_tree.node, the other is given by:
def list_plane_tree_of_plane_tree : plane_tree → List plane_tree
| (plane_tree.node l) => l

theorem list_plane_tree_of_plane_tree_of_list_plane_tree : ∀ (l : List plane_tree), list_plane_tree_of_plane_tree (plane_tree.node l) = l := by
  intro l
  cases l with
  | nil => rfl
  | cons hd tl =>
    simp [plane_tree.node, list_plane_tree_of_plane_tree]
    done
  -- or simply:
  -- exact fun l ↦ rfl

theorem plane_tree_of_list_plane_tree_of_plane_tree : ∀ (t : plane_tree), plane_tree.node (list_plane_tree_of_plane_tree t) = t := by
  intro t
  cases t with
  | node l => simp [plane_tree.node, list_plane_tree_of_plane_tree]
  done


-- 5. Rotating isomorphism between full binary trees and plane trees
-- Define both directions as functions and prove that they are inverses of each other
def full_binary_tree_of_plane_tree : plane_tree → full_binary_tree
| plane_tree.node [] => full_binary_tree.leaf
| plane_tree.node (T :: l) => full_binary_tree.node (full_binary_tree_of_plane_tree T) (full_binary_tree_of_plane_tree (plane_tree.node l))

def plane_tree_of_full_binary_tree : full_binary_tree → plane_tree
| full_binary_tree.leaf => plane_tree.node []
| full_binary_tree.node T₁ T₂ => plane_tree.node (plane_tree_of_full_binary_tree T₁ :: list_plane_tree_of_plane_tree (plane_tree_of_full_binary_tree T₂))

theorem full_binary_tree_of_plane_tree_of_full_binary_tree : ∀ (t : full_binary_tree), full_binary_tree_of_plane_tree (plane_tree_of_full_binary_tree t) = t := by
  intro t
  induction t with
  | leaf => rfl
  | node T₁ T₂ ih₁ ih₂ =>
    simp [full_binary_tree_of_plane_tree, plane_tree_of_full_binary_tree]
    rw [ih₁]
    simp  -- Remove T₁ = T₁ from the goal
    rw [plane_tree_of_list_plane_tree_of_plane_tree]
    rw [ih₂]
    done

-- lemma aux : ∀ (l : List plane_tree), plane_tree_of_full_binary_tree (full_binary_tree_of_plane_tree (plane_tree.node l)) = plane_tree.node l := by
--   intro l
--   induction l with
--   | nil => rfl
--   | cons hd tl ih =>
--     simp [full_binary_tree_of_plane_tree]
--     simp [plane_tree_of_full_binary_tree]
--     rw [ih]
--     rw [list_plane_tree_of_plane_tree_of_list_plane_tree]
--     simp
--     sorry

theorem plane_tree_of_full_binary_tree_of_plane_tree : ∀ (t : plane_tree), plane_tree_of_full_binary_tree (full_binary_tree_of_plane_tree t) = t := by
  rintro ⟨⟨ ⟩ | ⟨T₁, l⟩⟩
  rfl
  simp [full_binary_tree_of_plane_tree, plane_tree_of_full_binary_tree]
  rw [plane_tree_of_full_binary_tree_of_plane_tree]
  rw [plane_tree_of_full_binary_tree_of_plane_tree]
  simp
  rw [list_plane_tree_of_plane_tree_of_list_plane_tree]



  -- intro t
  -- -- rcases h : plane_tree_of_full_binary_tree (full_binary_tree_of_plane_tree t) with ⟨⟨ ⟩ | ⟨T₁, l⟩⟩
  -- rcases h : t with ⟨⟨ ⟩ | ⟨T₁, l⟩⟩
  -- rfl
  -- simp [full_binary_tree_of_plane_tree, plane_tree_of_full_binary_tree]
  -- induction l with
  -- | nil =>
  --   simp [full_binary_tree_of_plane_tree]
  --   simp [plane_tree_of_full_binary_tree]
  --   rw [list_plane_tree_of_plane_tree_of_list_plane_tree]
  --   simp
  --   rw [plane_tree_of_full_binary_tree_of_plane_tree]
  --   done
  -- | cons hd tl ih =>
  --   simp [full_binary_tree_of_plane_tree]
  --   simp [plane_tree_of_full_binary_tree]
  --   rw [list_plane_tree_of_plane_tree_of_list_plane_tree]
  --   simp
  --   rw [plane_tree_of_full_binary_tree_of_plane_tree T₁]
  --   simp
  --   sorry




  -- intro T
  -- cases T with
  -- | node l =>
  --   induction l with
  --   | nil => rfl
  --   | cons hd tl ih =>
  --     simp [full_binary_tree_of_plane_tree]
  --     simp [plane_tree_of_full_binary_tree]
  --     rw [ih]
  --     rw [list_plane_tree_of_plane_tree_of_list_plane_tree]
  --     simp
  --     rw [plane_tree_of_full_binary_tree_of_plane_tree hd]
  --     done








  -- rintro ⟨⟨ ⟩ | ⟨T₁, l⟩⟩
  -- rfl
  -- simp [full_binary_tree_of_plane_tree, plane_tree_of_full_binary_tree]
  -- rw [plane_tree_of_full_binary_tree_of_plane_tree]
  -- simp
  -- induction l with
  -- | nil => rfl
  -- | cons hd tl ih =>
  --   simp [full_binary_tree_of_plane_tree]
  --   simp [plane_tree_of_full_binary_tree]
  --   rw [ih]
  --   rw [list_plane_tree_of_plane_tree_of_list_plane_tree]
  --   simp
  --   rw [plane_tree_of_full_binary_tree_of_plane_tree hd]
  --   done


-- 6. 2n choose n is divisible by n+1
