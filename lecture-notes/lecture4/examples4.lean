import Mathlib.Data.Nat.Factorization.Defs

import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

import Exercises.Sheet2
import Exercises.Sheet3

--open the namespace 'Nat' to avoid writing Nat. before results about natural numbers
open Nat

variable {α : Type}
variable {n m : ℕ}

-- Define the prime factorization as function from ℕ to ℕ.
def PExp_val (n : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => if (k + 1).Prime then (maxPowDvdDiv (k + 1) n).1 else 0

-- What remains after the largest power of `p` has been removed from `n`.
abbrev remainder (n p : ℕ) : ℕ := (maxPowDvdDiv p n).2

/-
The type of finitely supported functions from α to ℕ is denoted by Finsupp α ℕ.
A term of this type consists of
- a function f : α → ℕ, and
- the support of f, which is a finite set of elements of α (supp : Finset α)
- A proof that f x ≠ 0 if and only if x is in the support of f.
-/

#check Finsupp α ℕ

--The support of the prime factorization is the set of primes smaller than n which divide n.
def PExp_support (n : ℕ) : Finset ℕ :=
  (Finset.range (n + 1)).filter (fun k => k.Prime ∧ k ∣ n)

--Combine the two previous definitions to define the prime factorization as a finitely supported.
def PExp (n : ℕ) : ℕ →₀ ℕ where
  support := PExp_support n
  toFun := PExp_val n
  mem_support_toFun := by
    intro p
    constructor
    · simp only [PExp_support, Finset.mem_filter, Finset.mem_range, Order.lt_add_one_iff, PExp_val, ne_eq]
      intro ⟨hp1,hp2,hp3⟩
      cases p with
      | zero => contradiction
      | succ p' =>
      simp only [fst_maxPowDvdDiv, ite_eq_right_iff, padicValNat.eq_zero_iff,
        Nat.add_eq_right, Classical.not_imp, not_or, Decidable.not_not]
      have hpne : p' ≠ 0 := by
        linarith [Prime.one_lt hp2]
      have hne : n ≠ 0 := by
        exact Nat.ne_zero_of_lt hp1
      exact ⟨hp2, hpne, hne, hp3⟩
    · intro h
      have hnlt : 0 < n := by
        by_contra! hcon
        apply h
        simp only [PExp_val]
        cases p with
        | zero => contradiction
        | succ p' =>
        simp only [fst_maxPowDvdDiv, ite_eq_right_iff, padicValNat.eq_zero_iff, Nat.add_eq_right]
        intro hp
        right
        left
        exact eq_zero_of_le_zero hcon
      simp only [PExp_support, Finset.mem_filter, Finset.mem_range, Order.lt_add_one_iff]
      by_contra hcon
      simp only [not_and_or] at hcon
      rcases hcon with h1 | h2 | h3
      · apply h
        simp only [PExp_val]
        have hgt : (maxPowDvdDiv p n).1 = 0 := by
          simp only [fst_maxPowDvdDiv, padicValNat.eq_zero_iff]
          right
          right
          push Not at h1
          exact not_dvd_of_pos_of_lt hnlt h1
        cases p with
        | zero => contradiction
        | succ p' =>
        simp only [fst_maxPowDvdDiv, padicValNat.eq_zero_iff, Nat.add_eq_right] at hgt
        simp only [fst_maxPowDvdDiv, ite_eq_right_iff, padicValNat.eq_zero_iff, Nat.add_eq_right]
        intro hp
        exact hgt
      · apply h
        simp only [PExp_val]
        cases p with
        | zero => contradiction
        | succ p' =>
        simp only [fst_maxPowDvdDiv, ite_eq_right_iff, padicValNat.eq_zero_iff, Nat.add_eq_right]
        intro hp
        contradiction
      · apply h
        simp only [PExp_val]
        cases p with
        | zero => contradiction
        | succ p' =>
        simp only [fst_maxPowDvdDiv, ite_eq_right_iff, padicValNat.eq_zero_iff, Nat.add_eq_right]
        intro hp
        right
        right
        exact h3

-- you can access the support like this
#check (PExp n).support

/-
Recall from last time that we can sum the values of function defined on a finite set.
Similarly, we can take the product of the values of a function defined on a finite set.
Written \prod.
-/
variable {I : Finset α} {f : α → ℕ}

#check (∏ i ∈ I, f i ) -- The product of the values of f on the finite set I.

/-
These are the key lemmas about the prime factorization that we proved in the lecture.
Optional: use the results from the exercise sheet to prove them.
-/

/-
NEW TACTICS unlocked:
- simp [...] : Much stronger version of rw. It rewrites and simplifies the goal.
Performance reasons: use simp? [] to find a minimal set of lemmas to simplify the goal.
- let : ... := ... : Introduces a local definition. Useful to give a name to a complicated term.
-/

lemma PExp_supp_empty_of_one : (PExp 1).support = ∅ := by
  simp only [PExp, PExp_support, dvd_one, reduceAdd, Finset.filter_eq_empty_iff, Finset.mem_range,
    Order.lt_two_iff, not_and]
  intro n hn hnprime
  exact Nat.Prime.ne_one hnprime

lemma PExp_supp_nempty_of_gt_one {n : ℕ} (hn : n > 1) : Nonempty (PExp n).support := by
  have ⟨p, ⟨hp1,hp2⟩⟩ := exists_prime_and_dvd (Ne.symm (Nat.ne_of_lt hn))
  use p
  simp only [PExp, PExp_support, Finset.mem_filter, Finset.mem_range, Order.lt_add_one_iff]
  constructor
  · by_cases hpn : n = p
    · rw[hpn]
    obtain ⟨k, hk⟩ := hp2
    have hkne : k ≠ 1 := by
      by_contra hk1
      rw[hk1, mul_one] at hk
      contradiction
    rw [mul_comm] at hk
    have hklt := exercise0 (Nat.ne_zero_of_lt hn) (hkne) hk
    exact Nat.le_of_lt hklt
  exact ⟨hp1, hp2⟩

lemma PExp_mul_remainder (n : ℕ) (p : (PExp n).support) :
    n = p ^ PExp n p * remainder n p := by
  sorry

lemma lemma2 {n : ℕ} (q : (PExp n).support) :
    (PExp n).support = insert (q : ℕ) (PExp (remainder n q)).support := by
  sorry

lemma lemma3 {n : ℕ} (q : (PExp n).support) :
    (q : ℕ) ∉ (PExp (remainder n q)).support := by
  sorry

lemma lemma4 {n : ℕ} {q : (PExp n).support} :
    ∀ p ∈ (PExp (remainder n q)).support,
      PExp n p = PExp (remainder n q) p := by
  sorry

private lemma helper {n : ℕ} {k : ℕ} {q : ℕ} (hn : n ≠ 0) (h : n = k * q) : k ≠ 0 := by
  by_contra hk
  rw[hk] at h
  rw [zero_mul] at h
  contradiction

lemma lemma5 {n : ℕ} (q : (PExp n).support) :
  q ^ (PExp n q) > (1 : ℕ) := by
        have hqgt : q > (1 : ℕ) := by
          by_contra! hq1
          have hqneprime : ¬ (Nat.Prime q.val) := by
            intro hqprime
            exact (not_lt_of_ge hq1) hqprime.one_lt
          apply Finsupp.mem_support_iff.mp q.property
          simp only [PExp, Finsupp.coe_mk, PExp_val]
          cases hqval : q.val with
          | zero => simp
          | succ q' =>
          simp only [fst_maxPowDvdDiv, ite_eq_right_iff, padicValNat.eq_zero_iff, Nat.add_eq_right]
          intro hcon
          rw[← hqval] at hcon
          contradiction
        refine one_lt_pow ?_ hqgt
        apply Finsupp.mem_support_iff.mp
        exact q.property

theorem prime_factorization_exist {n : ℕ} (hn : n > 0) :
  n = ∏ p ∈ (PExp n).support, p ^ (PExp n p) := by
  induction n using Nat.case_strong_induction_on with
  | hz => contradiction
  | hi n hind =>
  by_cases hnzero : n = 0
  · simp only [hnzero, zero_add, PExp_supp_empty_of_one, Finset.prod_empty]
  have hngtone : n + 1 > 1 := by
    exact Nat.sub_ne_zero_iff_lt.mp hnzero
  have q : (PExp (n + 1)).support := Classical.choice (PExp_supp_nempty_of_gt_one hngtone)
  let k := remainder (n + 1) q
  have hk : n + 1 = q ^ (PExp (n + 1) q) * k := PExp_mul_remainder (n + 1) q
  calc n + 1 = q ^ (PExp (n + 1) q) * k := hk
  _ = q ^ (PExp (n + 1) q) * ∏ p ∈ (PExp k).support, p ^ (PExp k p) := by
    have hnk : k ≤ n := by
      have hne : q ^ (PExp (n + 1)) q > (1 : ℕ) := by exact lemma5 q
      have hlt := exercise0 (ne_zero_of_lt hngtone) (Nat.ne_of_gt hne) hk
      linarith
    simp only [mul_eq_mul_left_iff, Nat.pow_eq_zero, ne_eq]
    left
    apply hind k hnk
    apply pos_of_ne_zero
    rw[mul_comm] at hk
    exact helper (Nat.succ_ne_zero n) hk
  _ = q ^ (PExp (n + 1) q) * ∏ p ∈ (PExp k).support, p ^ (PExp (n + 1) p) := by
    refine (Nat.mul_right_inj ?_).mpr ?_
    · exact helper (Nat.succ_ne_zero n) hk
    apply Finset.prod_congr rfl
    intro p hp
    rw [lemma4 (q := q)]
    exact hp
  _ = ∏ p ∈ insert (q : ℕ) (PExp k).support, p ^ (PExp (n + 1) p) := by
    refine Eq.symm (Finset.prod_insert ?_)
    exact lemma3 q
  _ = ∏ p ∈ (PExp (n + 1)).support, p ^ (PExp (n + 1) p) := by
    dsimp [k]
    apply Finset.prod_congr (lemma2 q).symm
    intro p hp
    rfl


theorem prime_factorization_unique {n m : ℕ} (hn : n > 0) (hm : m > 0) (h : PExp n = PExp m) :
  n = m := by
  rw [prime_factorization_exist hn, prime_factorization_exist hm]
  rw[h]
