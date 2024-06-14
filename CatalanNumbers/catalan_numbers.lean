import mathlib

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Factorial.Basic

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

-- 4. list plane tree ≅ plane tree
-- Define both directions as functions and prove that they are inverses of each other
-- One direction is simply plane_tree.node, the other is given by:
def list_plane_tree_of_plane_tree : plane_tree → List plane_tree
| (plane_tree.node l) => l

-- Proof that the transformations are inverses of each other
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

-- Definition of transformation from plane tree to full binary tree
def full_binary_tree_of_plane_tree : plane_tree → full_binary_tree
| plane_tree.node [] => full_binary_tree.leaf
| plane_tree.node (T :: l) => full_binary_tree.node (full_binary_tree_of_plane_tree T) (full_binary_tree_of_plane_tree (plane_tree.node l))


-- Definition of transformation from full binary tree to plane tree
def plane_tree_of_full_binary_tree : full_binary_tree → plane_tree
| full_binary_tree.leaf => plane_tree.node []
| full_binary_tree.node T₁ T₂ => plane_tree.node (plane_tree_of_full_binary_tree T₁ :: list_plane_tree_of_plane_tree (plane_tree_of_full_binary_tree T₂))

-- Proof that the transformations are inverses of each other
theorem full_binary_tree_of_plane_tree_of_full_binary_tree : ∀ (t : full_binary_tree), full_binary_tree_of_plane_tree (plane_tree_of_full_binary_tree t) = t := by
  intro t
  induction t with
  | leaf => rfl
  | node T₁ T₂ ih₁ ih₂ =>
    simp [full_binary_tree_of_plane_tree, plane_tree_of_full_binary_tree]
    rw [ih₁]
    simp  -- Remove T₁ = T₁ from the goal
    rw [plane_tree_of_list_plane_tree_of_plane_tree] -- use of the isomorphism list plane tree ≅ plane tree
    rw [ih₂]
    done

theorem plane_tree_of_full_binary_tree_of_plane_tree : ∀ (t : plane_tree), plane_tree_of_full_binary_tree (full_binary_tree_of_plane_tree t) = t := by
  rintro ⟨⟨ ⟩ | ⟨T₁, l⟩⟩ -- here we have to use rintro because induction does not work
  -- case where t = plane_tree.node []
  rfl
  -- case where t = plane_tree.node (T₁ :: l)
  simp [full_binary_tree_of_plane_tree, plane_tree_of_full_binary_tree]
  rw [plane_tree_of_full_binary_tree_of_plane_tree] -- to use the induction hypothesis we call the theorem we are proving
  rw [plane_tree_of_full_binary_tree_of_plane_tree]
  simp
  rw [list_plane_tree_of_plane_tree_of_list_plane_tree] -- use of the isomorphism list plane tree ≅ plane tree
  done


-- 6. 2n choose n is divisible by n+1
-- idea: https://math.stackexchange.com/questions/189346/n1-is-a-divisor-of-binom2n-n

 --helper function for transforming (n+1)! = (2 * (n + 1) - (n + 1))!
theorem rewrite_n_plus_1 : ∀ (n : ℕ), n + 1 = 2 * (n + 1) - (n + 1) := by
  intro n
  rw [← Nat.add_left_inj]
  rw [Nat.sub_add_cancel]
  nth_rw 1 [← Nat.add_assoc]
  ring
  linarith

--helper function for transforming n! = (2 * (n + 1) - (n + 1 + 1))!
theorem rewrite_n : ∀ (n : ℕ), n  = 2 * (n + 1) - (n + 1 + 1) := by
  intro n
  rw [← Nat.add_left_inj]
  rw [Nat.sub_add_cancel]
  nth_rw 1 [← Nat.add_assoc]
  ring
  linarith

-- we first want to show this equality which will make proving the divisibility trivial
theorem from_2n_choose_n_equality (n : ℕ) : Nat.choose (2*n) n = (n+1) * (Nat.choose (2*n) n - Nat.choose (2*n) (n+1)) := by
  cases n with
  | zero => -- the case where n = 0
    rw [Nat.choose_zero_right]
    rw [zero_add]
    rw [one_mul]
    rw [Nat.choose_one_right]
  | succ n => -- case where n = n + 1
  -- goal: (2 * (n + 1)).choose (n + 1) = (n + 1 + 1) * ((2 * (n + 1)).choose (n + 1) - (2 * (n + 1)).choose (n + 1 + 1))
  rw [Nat.mul_sub_left_distrib]
  rw [Nat.right_distrib]
  rw [Nat.one_mul]
  nth_rw 3 [Nat.add_comm]
  apply Eq.symm
  -- We add Nat.choose (2*n) (n+1) to both sides (we just put a parameter which lean figures out what we want it to be)
  -- so (- Nat.choose (2*n) (n+1) + Nat.choose (2*n) (n+1)) cancels out
  -- with tactic Nat.sub_add_cancel (m ≤ n → n - m + m = n) because of this we later have to prove m ≤ n
  rw [← Nat.add_left_inj]
  rw [Nat.sub_add_cancel]
  rw [Nat.add_right_inj]
  nth_rw 1 [Nat.mul_comm]
  nth_rw 3 [Nat.mul_comm]
  -- we want to multiply both sides of equation by (n+1)! (n)! so we have to show these two are positive
  have h : 0 < Nat.factorial (n+1) * Nat.factorial (n) := by
    apply Nat.mul_pos
    exact Nat.factorial_pos (n+1)
    exact Nat.factorial_pos n
  -- multiply both sides by (n+1)! (n)!
  apply Nat.eq_of_mul_eq_mul_right h
   -- Now we want to remove the choose from both sides with tactic Nat.choose_mul_factorial_mul_factorial
   -- To do this we have to prepare the equation to form n.choose k * k.factorial * (n - k).factorial = n.factorial
   -- The hard part here is to get (n - k).factorial. For this i defined helper functions rewrite_n_plus_1 and rewrite_n
   -- which help to get the correct form of the factorials
  nth_rw 4 [Nat.mul_comm]
  nth_rw 1 [Nat.mul_assoc]
  nth_rw 2 [← Nat.mul_assoc]
  rw [← Nat.factorial_succ]
  nth_rw 1 [Nat.mul_assoc]
  nth_rw 3 [← Nat.mul_assoc]
  rw [← Nat.factorial_succ]
  nth_rw 1 [← Nat.mul_assoc]
  nth_rw 4 [rewrite_n_plus_1]
  rw [Nat.choose_mul_factorial_mul_factorial]
  --removing second choose
  nth_rw 5 [rewrite_n n]
  rw [← Nat.mul_assoc]
  rw [Nat.choose_mul_factorial_mul_factorial]
  -- just some trivial inequalities left to prove which are done automatically
  linarith
  linarith

  -- proof of m ≤ n from tactic Nat.sub_add_cancel
  -- goal: (n + 1 + 1) * (2 * (n + 1)).choose (n + 1 + 1) ≤ (2 * (n + 1)).choose (n + 1) + (n + 1) * (2 * (n + 1)).choose (n + 1)
  nth_rw 1 [← Nat.one_mul ((2 * (n + 1)).choose (n + 1))]
  rw [← Nat.right_distrib]
  rw [← Nat.add_assoc]
  nth_rw 1 [Nat.add_comm 1 n]
  apply Nat.mul_le_mul_left
  -- In this part of the proof h is the part where we prove that the inequality holds when we multiply with (n+2)! and (n+1)!
  -- Before when proving the equality the part inside h was just proving positivity but here it is the actual proof of the inequality
  have h : (Nat.choose (2 * (n + 1)) (n + 1 + 1)) * (Nat.factorial (n+1+1) * Nat.factorial (n+1)) ≤ (Nat.choose (2 * (n + 1)) (n + 1)) *  (Nat.factorial (n+1+1) * Nat.factorial (n+1)) := by
    -- removing choose from left side of ≤
    nth_rw 2 [Nat.factorial_succ]
    nth_rw 1 [← Nat.mul_assoc]
    nth_rw 4 [Nat.mul_comm]
    nth_rw 1 [← Nat.mul_assoc]
    nth_rw 4 [rewrite_n n]
    rw [Nat.choose_mul_factorial_mul_factorial]
    -- removing choose from right side of ≤
    nth_rw 1 [Nat.factorial_succ]
    nth_rw 6 [Nat.mul_comm]
    nth_rw 1 [Nat.mul_assoc]
    nth_rw 6 [Nat.mul_comm]
    nth_rw 2 [← Nat.mul_assoc]
    nth_rw 1 [← Nat.mul_assoc]
    nth_rw 1 [← Nat.mul_assoc]
    nth_rw 6 [rewrite_n_plus_1]
    rw [Nat.choose_mul_factorial_mul_factorial]
    -- the rest of the inequalities are trivial
    linarith
    linarith
    linarith
  -- the rest after we prove h is just telling Lean that (n+2)! and (n+1)! are positive
  apply Nat.le_of_mul_le_mul_right h
  apply Nat.mul_pos
  exact Nat.factorial_pos (n+1+1)
  exact Nat.factorial_pos (n+1)


-- actually proving that 2n choose n is divisible by n+1
theorem from_2n_choose_n_divisible_by_n_plus_1 (n : ℕ) : (n+1) ∣ Nat.choose (2*n) n := by
  rw [from_2n_choose_n_equality]
  apply dvd_mul_right
