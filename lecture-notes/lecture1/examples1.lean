import Std

#check Nat.add_zero

#check Nat.mul_succ

#check Nat.mul_zero

-- Example 1
theorem example1 (n : Nat) : n * Nat.succ 0 = n := by
  rw[Nat.mul_succ]



  --rw [Nat.mul_succ]
  --rw[Nat.mul_zero]
  sorry

-- Example 2
theorem example2 (n : Nat) : 0 + n = n := by
  induction n with
  | zero =>
      exact Nat.zero_add 0
  | succ n inductionHypothesis =>
      rw [Nat.add_succ, inductionHypothesis]


-- Example 1 - finished
theorem example1' (n : Nat) : n * Nat.succ 0 = n := by
  rw [Nat.mul_succ]
  rw[Nat.mul_zero]
  exact example2 n

-- Example 3
theorem example3 (n :Nat) : ∀ m, n + m = m + n := by
  induction n with
  | zero =>
      intro m
      rw [Nat.add_zero]
      rw [example2 m]
  | succ n inductionHypothesis =>
      intro m
      rw [Nat.succ_add]
      rw [inductionHypothesis]
      rw [Nat.add_succ]
