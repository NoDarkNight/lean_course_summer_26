import Mathlib.Tactic
import Mathlib.Data.Fin.Basic

import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Prime.Defs

import Mathlib.Data.Nat.Factorial.Basic

/-
Your first task is to prove lemmas 0-3 from the lecture notes.
-/

section -- More on divisiblity

theorem exercise0 {d k n : ℕ} (hn : n ≠ 0) (hd : d ≠ 1) (h : n = d * k) : k < n := by
  have hdneq : d ≠ 0 := by
    intro hd
    rw[hd, Nat.zero_mul] at h
    exact hn h
  by_contra! hk_leq_n
  have hmul : d * n ≤ d * k := by
    exact Nat.mul_le_mul_left d hk_leq_n
  rw[← h] at hmul
  have hnemul : ¬ (d * n ≤ n) := by
    push Not
    refine (Nat.lt_mul_iff_one_lt_left ?_).mpr ?_
    · exact Nat.zero_lt_of_ne_zero hn
    · exact Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨hdneq, hd⟩
  exact hnemul hmul

theorem exercise1 {d n : ℕ} (hd : d ≠ 1) (h : d ∣ n) : ¬ (d ∣ n + 1):= by
  by_contra hsucc
  have hsub : d ∣ n + 1 - n := by
    exact Nat.dvd_sub hsucc h
  rw[Nat.add_sub_self_left n 1] at hsub
  apply Nat.eq_one_of_dvd_one at hsub
  exact hd hsub

theorem infinitely_many_primes : ∀ n : ℕ, ∃ p : ℕ, p.Prime ∧ p > n := by
  by_contra! h
  rcases h with ⟨n, hn⟩
  let m := Nat.factorial n + 1
  have hmneq1 : m ≠ 1 := by
    refine (Nat.add_one_ne_add_one_iff.mpr) ?_
    exact Nat.factorial_ne_zero n
  have ⟨p, ⟨hp1,hp2⟩⟩ := Nat.exists_prime_and_dvd (hmneq1)
  have hpdvd : p ∣ Nat.factorial n := by
    refine Nat.dvd_factorial (Nat.Prime.pos hp1) ?_
    exact hn p hp1
  have hpndvd : ¬ (p ∣ Nat.factorial n + 1):= by
    exact exercise1 (Nat.Prime.ne_one hp1) hpdvd
  exact hpndvd hp2
end

section -- Finsets

#check Finset ℕ -- the type of finite subsets of ℕ

variable {α : Type} [DecidableEq α] -- we need to be able to decide equality of elements

#check Finset α -- the type of finite sets formed by terms of type α

/-
A very useful feature of the Finset type is that we can perform induction over |I|.
This works similarly to induction over ℕ. Use #check to find out how it works.
For more details see: https://leanprover-community.github.io/mathematics_in_lean/C06_Discrete_Mathematics.html
-/
#check Finset.induction_on

-- We can sum over finite sets, using the ∑ notation.
variable {I : Finset α} {f : α → ℕ}

#check ∑ i ∈ I, f i


-- Use what we learned to prove the following theorem.
theorem exercise3 (d : ℕ) (h : ∀ x, d ∣ f x) : d ∣ ∑ i ∈ I, f i := by
  induction I using Finset.induction_on with
  | empty => exact Nat.dvd_of_mod_eq_zero rfl
  | @insert a I ha hI =>
    rcases hI with ⟨k, hk⟩
    have ⟨l, hl⟩ : d ∣ f a := h a
    use k + l
    rw[Finset.sum_insert ha, hl, hk, Nat.mul_add, Nat.add_comm]
end

/-
Open question: Think about the following question:
How can we formalize the prime factorization theorem in Lean?
What would be the type of the decomposition of a natural number into its prime factors?
How can you state the theorem that every natural number has a (unique) prime factorization?
How would you prove it?
-/
