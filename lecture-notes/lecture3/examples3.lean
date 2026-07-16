import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Finset.Range
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Rat.Init
import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic


section -- Divisiblity

variable {n m p d : ℕ}

-- We write \dvd to get the symbol ∣, which is used to denote divisibility.
#check (d ∣ n : Prop)

#check (Nat.Prime p)

#check p.Prime

#check (Nat.dvd_prime )

theorem example1 (hn : d ∣ n) (hm : d ∣ m) : d ∣ n + m := by
  rcases hn with ⟨k, hk⟩
  rcases hm with ⟨l, hl⟩
  use k + l
  rw [hk, hl]
  exact Eq.symm (Nat.mul_add d k l)

theorem example3 (h : n > 1) : n * n > n := by
  exact Nat.lt_mul_self_iff.mpr h

theorem example4 (hp : p.Prime) : ¬ ((p * p).Prime) := by
  have hpneq1 : p ≠ 1 := by
    exact Nat.Prime.ne_one hp
  have hpneqp2 : p ≠ p * p := by
    apply Nat.ne_of_lt
    exact Nat.lt_mul_self_iff.mpr (Nat.Prime.one_lt hp)
  by_contra h
  have h1 : p ∣ p * p := by
    use p
  have hpdvd : p = 1 ∨ p = p * p := by
    exact (Nat.dvd_prime h).mp h1
  cases hpdvd with
  | inl hp1 => contradiction
  | inr hp2 => contradiction

end

section -- Proof by Induction

variable (n : ℕ)

#check Finset.range n -- The set of natural numbers {0, 1, 2, ..., n-1}, has type Finset ℕ.

#check ∑ i ∈ Finset.range n, i -- The sum of the elements of the set Finset.range n.

#check Nat.add_mul_div_right

theorem Gauss_sum (n : ℕ) : ∑ i ∈ Finset.range (n + 1), i = n * (n + 1) / 2 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      calc
        ∑ i ∈ Finset.range (n + 1 + 1), i
          = (∑ i ∈ Finset.range (n + 1), i) + (n + 1) := by
            exact Finset.sum_range_succ (fun x ↦ x) (n + 1)
        _ = n * (n + 1) / 2 + (n + 1) := by rw [ih]
        _ = (n * (n + 1) + (n + 1) * 2) / 2 := by
          refine (Nat.add_mul_div_right (n * (n + 1)) (n + 1) ?_).symm
          exact Nat.succ_pos 1
        _ = (n + 2) * (n + 1) / 2 := by
              rw[Nat.mul_comm (n +1) 2, ← Nat.add_mul]
        _ = (n + 1) * (n + 2) / 2 := by
          rw[Nat.mul_comm (n + 2) (n + 1)]

/-
The refine tactic allows you to apply a theorem or lemma to the goal, even if the
theorem has additional hypotheses that are not yet satisfied.
The tactic creates goals for all hypotheses left out by ?_.
-/

#check (n : ℚ)

theorem Gauss_sum' (n : ℕ) : ∑ i ∈ Finset.range (n + 1) , i  = (n * (n + 1) / 2 : ℚ) := by
  sorry

/-
We have to decide if we want to prove the theorem in ℕ or in ℚ.
The types ℕ and ℚ are different, so we have to be aware of the meaning of the symbolds
in each of those contexts.
Below is a sneak peak for next week, when we will talk about sets/subtypes. In particular,
the above theorem implies that n * (n + 1)/2 ∈ NatinRat.
-/

def NatinRat := {q : ℚ // ∃ n : ℕ, q = (n : ℚ)}

end

section -- Complete Induction
variable (P : ℕ → Prop)

def complete_induction (P : ℕ → Prop) : Prop :=  (P 0 ∧ (∀ n, (∀ m, m ≤ n → P m) → P (n + 1))) → ∀ n, P n

def Q (P : ℕ → Prop) (n : ℕ) : Prop := ∀ m, m ≤ n → P m

lemma Q_zero_of_P_zero : P 0 → Q P 0 := by
  sorry

lemma P_n_of_Q_n (n : ℕ) : Q P n -> P n := by
  sorry

lemma Q_succ_of_Q_n_of_P_succ_of_Q_n (n : ℕ) : (Q P n -> P (n + 1)) -> (Q P n -> Q P (n + 1)) := by
  sorry

lemma P_of_Q : (∀ n, Q P n) -> ∀ n, P (n) := by
  sorry

theorem induction_implies_complete_induction : complete_induction P := by
  intro ⟨hP0, hQP⟩
  apply P_of_Q P
  intro n
  induction n with
  | zero =>
      exact Q_zero_of_P_zero P hP0
  | succ n ih =>
      exact Q_succ_of_Q_n_of_P_succ_of_Q_n P n (hQP n) ih
end
