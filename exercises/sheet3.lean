import Mathlib.Tactic
import Mathlib.Data.Nat.Factorization.Defs

/-!
# Exercise sheet 3: removing one prime power

In `examples4.lean`, `PExp n p` is the exponent of `p` in `n`.  The two
definitions below give names to the corresponding entries of
`Nat.maxPowDvdDiv`.  Thus `primeExponent n p` is the exponent of `p`, while
`remainder n p` is what remains after the full power of `p` has been removed.

The four exercises isolate the number-theoretic input needed for lemmas 1--4
in the lecture notes. You may find the results in `Nat.MaxPowDiv` useful.
-/

namespace Sheet3

open Nat

abbrev primeExponent (n p : ℕ) : ℕ := (maxPowDvdDiv p n).1

abbrev remainder (n p : ℕ) : ℕ := (maxPowDvdDiv p n).2

/-
Lecture lemma 1: the largest power of `p` occurring in `n` divides `n`.
The lemma is a useful reformulation of exercise 1.
-/
lemma product_of_primeExponent (n p : ℕ) :
    n = p ^ primeExponent n p * remainder n p := by
  simp


theorem exercise1 (p n : ℕ) :
    p ^ primeExponent n p ∣ n := by
  have prod : n = p ^ primeExponent n p * remainder n p := by exact product_of_primeExponent n p
  exact Dvd.intro (remainder n p) (id (Eq.symm prod))

/-
Lecture lemma 2: after removing the largest power of `q`, every prime divisor of
`n` is either `q` itself or a prime divisor of the remainder.  The hypothesis
`q ∣ n` is the arithmetic content of saying that `q` lies in the support of
the prime factorization of `n`.
-/

lemma primes_notdvd_exp {p q : ℕ} (hp : p.Prime) : ∀ k : ℕ, ¬ (p ∣ q) → ¬ (p ∣ q ^ k) := by
  intro k h
  refine (Nat.Prime.coprime_iff_not_dvd hp).mp ?_
  refine Coprime.pow_right k ?_
  exact (Nat.Prime.coprime_iff_not_dvd hp).mpr h

theorem exercise2 {p q n : ℕ} (hp : p.Prime) (hq : q.Prime) (hqn : q ∣ n) :
    p ∣ n ↔ p = q ∨ p ∣ remainder n q := by
  have hn : n = q ^ primeExponent n q * remainder n q := by exact product_of_primeExponent n q
  constructor
  · intro pdn
    by_cases hpq : p = q
    · left; exact hpq
    · right
      have npdqexp : ¬ p ∣ q ^ primeExponent n q := by
        have npdq : ¬ p ∣ q := by
            refine (Nat.Prime.coprime_iff_not_dvd hp).mp ?_
            exact (coprime_primes hp hq).mpr hpq
        exact primes_notdvd_exp hp (primeExponent n q) npdq
      rw[hn] at pdn
      exact (hp.dvd_mul.mp pdn).resolve_left npdqexp
  · intro hpqn
    cases hpqn with
    | inl hpq =>
      rw[hpq]; exact hqn
    | inr hpq =>
      rw[hn]
      exact Nat.dvd_mul_left_of_dvd hpq (q ^ primeExponent n q)

/-
Lecture lemma 3: the chosen prime no longer divides the remainder.  The
nonzero hypothesis is necessary: every natural number divides zero.
-/
lemma primeExp_eq_padicVal {n p : ℕ} : primeExponent n p = padicValNat p n := by
  exact fst_maxPowDvdDiv p n

theorem exercise3 {p n : ℕ} (hp : p.Prime) (hn : n ≠ 0) :
    ¬p ∣ remainder n p := by
  have hnn : n = p ^ primeExponent n p * remainder n p := by exact product_of_primeExponent n p
  by_contra pdrem
  rcases pdrem with ⟨k, hk⟩
  rw[hk, ← mul_assoc, ← pow_succ] at hnn
  have primeExp_lt_self : primeExponent n p + 1 ≤ padicValNat p n := by
    exact (pow_dvd_iff_le_padicValNat hp.ne_one hn).mp ⟨k, hnn⟩
  rw[primeExp_eq_padicVal] at primeExp_lt_self
  exact Nat.not_succ_le_self _ primeExp_lt_self
  -- im assuming we should not use not_dvd_divMaxPow

/-
Lecture lemma 4: removing the largest power of `q` does not change the exponent
of a different prime `p`.
-/

/-
Start by using the first lemma to prove the other lemmas. (You can use simp? and exact?)
-/

lemma padicValNat_mul (n m p : ℕ) (hm : m ≠ 0) (hn : n ≠ 0) (hp : p.Prime) :
  padicValNat p (m * n) = padicValNat p m + padicValNat p n := by
  refine @padicValNat.mul _ _ _ ?_ hm hn
  exact { out := hp }

lemma primeExponent_mul {n m p : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) (hp : p.Prime) :
    primeExponent (m * n) p = primeExponent m p + primeExponent n p := by
  repeat rw[primeExp_eq_padicVal]
  exact padicValNat_mul n m p hm hn hp

lemma primeExponent_coprime {n p : ℕ} (hcoprime : ¬p ∣ n) :
    primeExponent n p = 0 := by
  rw[primeExp_eq_padicVal]
  simp only [padicValNat.eq_zero_iff]
  right; right; exact hcoprime
  -- i'm assuming we cannot use padicValNat.eq_zero_of_not_dvd

/- a useful result from the library, it is a reformulation of the fact that the prime exponent
is the largest power of p that divides n.
-/

#check pow_dvd_iff_le_padicValNat

theorem exercise4 {p q n : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (hn : n ≠ 0) :
    primeExponent n p = primeExponent (remainder n q) p := by
  have hqn : n = q ^ primeExponent n q * remainder n q := by exact product_of_primeExponent n q
  repeat rw[primeExp_eq_padicVal]; repeat rw[primeExp_eq_padicVal] at hqn
  have hr : remainder n q ≠ 0 := by
    by_contra h
    rw[h, mul_zero] at hqn
    contradiction
  have hrn : remainder n q ∣ n := by exact Dvd.intro_left (q ^ primeExponent n q) (id (Eq.symm hqn))
  have hcop : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr hpq
  apply Nat.le_antisymm
  · rw [← pow_dvd_iff_le_padicValNat hp.ne_one hr]
    have pdn : p ^ padicValNat p n ∣ n := by exact pow_padicValNat_dvd
    nth_rewrite 2 [hqn] at pdn
    have npdq : Coprime (p ^ padicValNat p n) (q ^ padicValNat q n) := by
      exact pow_gcd_pow_of_gcd_eq_one hcop
    exact Coprime.dvd_of_dvd_mul_left npdq pdn
  · rw [← pow_dvd_iff_le_padicValNat hp.ne_one hn]
    exact dvd_trans pow_padicValNat_dvd hrn

/-!
## Applications of prime factorization

For these exercises we use Mathlib's built-in `Nat.factorization`.  Its
support is the finite set of prime divisors, just like the support of `PExp`
constructed in the lecture.

The greatest common divisor `Nat.gcd n m` is the largest natural number that
divides both `n` and `m`.

The least common multiple `Nat.lcm n m` is the smallest natural number
divisible by both `n` and `m`.
-/

/-
Start by writing down the proofs on paper, and start by formalizing the key mathematical
facts you used in the proof as lemmas.
We will discuss set operations during the exercise class tomorrow!
-/

/- Every prime dividing both `n` and `m` also divides `n + m`. -/
theorem exercise5 (n m : ℕ) :
    (Nat.gcd n m).factorization.support ⊆ (n + m).factorization.support := by
  intro p hp
  rw [support_factorization, mem_primeFactors] at hp
  rcases hp with ⟨hp, pdgcd, hgcd⟩
  rw[support_factorization, mem_primeFactors]
  refine ⟨hp, ?_, ?_⟩
  · have pdnm : p ∣ n ∧ p ∣ m := by exact Nat.dvd_gcd_iff.mp pdgcd
    rcases pdnm with ⟨⟨k, hk⟩ , ⟨l, hl⟩⟩
    have sum : n + m = p * (k + l) := by
      rw[hk, hl]
      exact Eq.symm (Nat.mul_add p k l)
    exact Dvd.intro (k + l) (id (Eq.symm sum))
  · by_contra npm
    apply Nat.add_eq_zero_iff.mp at npm
    apply Nat.gcd_eq_zero_iff.mpr at npm
    contradiction

/- The prime divisors of the least common multiple are exactly the prime
divisors occurring in either number.  The nonzero assumptions exclude the
special case in which `Nat.lcm n m = 0`. -/
theorem exercise6 {n m : ℕ} (hn : n ≠ 0) (hm : m ≠ 0) :
    n.factorization.support ∪ m.factorization.support =
      (Nat.lcm n m).factorization.support := by
    repeat rw [support_factorization]
    ext p -- had to search this up lol
    rw[Finset.mem_union]
    constructor
    · intro hp
      apply mem_primeFactors.mpr
      cases hp with
      | inl pn =>
        refine ⟨prime_of_mem_primeFactors pn, ?_ , lcm_ne_zero hn hm⟩
        have pdn : p ∣ n := by exact dvd_of_mem_primeFactors pn
        exact Nat.dvd_lcm_of_dvd_left pdn m
      | inr pm =>
        refine ⟨prime_of_mem_primeFactors pm, ?_ , lcm_ne_zero hn hm⟩
        have pdm : p ∣ m := by exact dvd_of_mem_primeFactors pm
        exact Nat.dvd_lcm_of_dvd_right pdm n
    · intro hp
      apply mem_primeFactors.mp at hp
      rcases hp with ⟨hp, hplcm, hlcm⟩
      have pdnm : p ∣ n * m := by
        have lcmdprod : n.lcm m ∣ n * m := by exact Nat.lcm_dvd_mul n m
        exact Nat.dvd_trans hplcm lcmdprod
      apply hp.dvd_mul.mp at pdnm
      cases pdnm with
      | inl pn => left; exact Prime.mem_primeFactors hp pn hn
      | inr pm => right; exact Prime.mem_primeFactors hp pm hm

end Sheet3
