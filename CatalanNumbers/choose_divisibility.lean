import mathlib
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Factorial.Basic


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
