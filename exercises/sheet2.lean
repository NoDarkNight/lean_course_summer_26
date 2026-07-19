import Mathlib.Tactic
import Mathlib.Data.Fin.Basic

import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Nat.Prime.Factorial


section -- Your first task is to prove lemmas 0-3 from the lecture notes.
variable (P : ℕ → Prop)

def Q (P : ℕ → Prop) (n : ℕ) : Prop := ∀ m, m ≤ n → P m

lemma Q_zero_of_P_zero : P 0 → Q P 0 := by
  intro hp m hm
  rw[Nat.le_zero.mp hm]
  exact hp

lemma P_n_of_Q_n (n : ℕ) : Q P n -> P n := by
  intro Qn
  exact Qn n le_rfl

lemma Q_succ_of_Q_n_of_P_succ_of_Q_n (n : ℕ) : (Q P n -> P (n + 1)) -> (Q P n -> Q P (n + 1)) := by
  intro hqp Qn
  have hp : P (n+1) := by
    exact hqp Qn
  intro m hm
  rcases Nat.le_succ_iff.mp hm with le_n | eq_n
  · exact Qn m le_n
  · rw [eq_n]; exact hp

lemma P_of_Q : (∀ n, Q P n) -> ∀ n, P (n) := by
  intro hq n
  exact P_n_of_Q_n P n (hq n)

end

section -- More on divisiblity

-- cleaner proof below; can skip grading this one (im too attached to delete it)
theorem exercise0 {d k n : ℕ} (hn : n ≠ 0) (hd : d ≠ 1) (h : n = d * k) : k < n := by
  have k0 : k > 0 := by
    by_contra k'
    push Not at k'
    rw[Nat.le_zero] at k'
    rw[k', Nat.mul_zero] at h
    contradiction
  have d1 : d > 1 := by
    have d0 : d ≠ 0 := by
      by_contra d'
      rw[d', Nat.zero_mul] at h
      contradiction
    exact Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨d0, hd⟩
  rw[h]
  exact (Nat.lt_mul_iff_one_lt_left k0).mpr d1

-- cleaner proof
theorem exercise0' {d k n : ℕ} (hn : n ≠ 0) (hd : d ≠ 1) (h : n = d * k) : k < n := by
  rw[h]; rw[h] at hn
  have d1 : d > 1 := by
    exact Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨(mul_ne_zero_iff.mp hn).left, hd⟩
  have k0 : k > 0 := by
    exact Nat.pos_of_ne_zero (Nat.mul_ne_zero_iff.mp hn).right
  exact (Nat.lt_mul_iff_one_lt_left k0).mpr d1


theorem exercise1 {d n : ℕ} (hd : d ≠ 1) (h : d ∣ n) : ¬ (d ∣ n + 1):= by
  rcases h with ⟨k, hk⟩
  rw[hk]
  intro h
  rcases h with ⟨l, hl⟩
  replace hl : d * (l - k) = 1 := by
    rw [Nat.mul_sub_left_distrib, ← hl, Nat.add_sub_cancel_left]
  rw[mul_comm, Nat.eq_one_of_mul_eq_one_right hl, Nat.one_mul] at hl
  contradiction

theorem infinitely_many_primes : ∀ n : ℕ, ∃ p : ℕ, p.Prime ∧ p > n := by
  intro n
  have nf : Nat.factorial n + 1 ≠ 1 := by
    by_contra eq
    rw[Nat.succ_inj] at eq
    exact (Nat.factorial_ne_zero n) eq
  rcases Nat.exists_prime_and_dvd nf with ⟨p, pp, hp⟩
  have pgn : p > n := by
    by_contra pn
    apply Nat.le_of_not_gt at pn
    have pdvd : p ∣ n.factorial := by
      exact (Nat.Prime.dvd_factorial pp).mpr pn
    replace pdvd : ¬ (p ∣ n.factorial + 1) := by
      exact exercise1 (Nat.Prime.ne_one pp) pdvd
    contradiction
  use p -- suprisingly lean autocompletes it without exact ⟨pp, pgn⟩

end

section -- Finsets

#check Finset ℕ -- the type of finite subsets of ℕ

variable {α : Type} [DecidableEq α] -- we need to be able to decide equality of elements

#check Finset α -- the type of finite sets formed by terms of type α

/-
A very useful feature of the Finset type is that we can perform induction over |I|.
This works similarly to induction over ℕ. Use #check to find out how it works.
-/
#check Finset.induction_on

-- We can sum over finite sets, using the ∑ notation.
variable {I : Finset α} {f : α → ℕ}

#check ∑ i ∈ I, f i


-- Use what we learned to prove the following theorem.
theorem exercise3 (d : ℕ) (h : ∀ x, d ∣ f x) : d ∣ ∑ i ∈ I, f i := by
  induction I using Finset.induction_on with
  | empty =>
    use 0
    apply Finset.sum_empty
  | insert x set xnotin ih =>
    rw[Finset.sum_insert]
    · exact (Nat.dvd_add_iff_right (h x)).mp ih;
    · exact xnotin

end

/-
Open question: Think about the following question:
How can we formalize the prime factorization theorem in Lean?
What would be the type of the decomposition of a natural number into its prime factors?
How can you state the theorem that every natural number has a (unique) prime factorization?
How would you prove it?
-/

/-
1.
We can formalize the prime factorization theorem in Lean with strong induction
For the base case, n = 2 is prime.
For the step, we assume that every number less than n is either prime or a product of primes.
  We seperate this into the cases for which n is prime and n is not prime.
  n is prime => proof holds
  n is not prime => n = a*b, with a, b < n => a, b are prime or product of primes, so n is as well
(this is just the typical proof for Fundamental Theorem of Arithmetic)

2.
Maybe a multiset containing natural number primes, such that the primes represent the factorization?

3.
I'm not really sure. If the type of the decomposition is a multiset, then the theorem should be that
every natural number can be represented by a unique multiset. However, I don't know how that can be
expressed in Lean.

4.
This may be possible with Euclid's Lemma, but I don't know if that is applicable to Lean
-/
