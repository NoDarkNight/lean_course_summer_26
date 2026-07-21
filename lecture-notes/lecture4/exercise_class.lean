import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Data.Nat.Factorization.Defs

/-
How do define functions in lean?
The basic syntax is as follows (this is called lambda natotation):
-/

def f : ℕ → ℕ := fun n => n + 1

/-
For more complicated functions, we can use pattern matching.
This works whenever the input type follows a recursive pattern, like the natural numbers or lists.
-/

def fac : ℕ → ℕ
  | 0 => 1
  | n + 1 => (n + 1) * fac n

def sum : List ℕ → ℕ
  | [] => 0
  | x :: xs => x + sum xs

-- We can match on more cases as long as the matching is exhaustive.
def fib : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => fib (n + 1) + fib n

/-
For even more complicated functions, with conditional statements, we can use if-then-else statements
or so-called ternary operators. The syntax is as follows:
if <condition> then <value if true> else <value if false>
-/
def collatz : ℕ → ℕ := fun n => if Even n then n / 2 else 3 * n + 1


/-
We can evaluate those functions as follows:
-/

variable {n : ℕ}

example (hn : n = 1) : fac n = 1 := by
  rw [hn]
  rfl

/-
We can prove properties of those functions using induction.
Note that rw[fac] only works in the induction step!
-/

lemma fac_pos : fac n > 0 := by
  induction n with
  | zero => rw[fac]
            exact Nat.zero_lt_one
  | succ n ih =>
    rw[fac]
    exact Nat.mul_pos (Nat.succ_pos n) ih

example (hn : n > 1) : fac n > 1 := by
  induction n with
| zero => contradiction
| succ n ih =>
  rw[fac]
  have hpos : fac n > 0 := fac_pos
  exact one_lt_mul_of_lt_of_le' hn hpos

/-
Evaluating ternary operators works similarly. rw[if_pos/if_neg _] helps under suitable assumptions.
-/
example (hn : n = 4) : collatz n = 2 := by
  rw [hn]
  rfl

example (hn : Even n) : collatz n = n / 2 := by
  rw [collatz]
  rw[if_pos hn]

/-
We can prove properties of those functions using case distinction.
-/

example (hn : n > 0) : collatz n > 0 := by
  by_cases h : Even n
  · rw [collatz]
    rw[if_pos h]
    obtain ⟨k, hk⟩ := h
    sorry
  rw [collatz]
  rw[if_neg h]
  simp only [gt_iff_lt, lt_add_iff_pos_left, Order.lt_add_one_iff, zero_le]


/-
Finally, we saw examples of sets/subtypes. This means
Given a type α and a predicate P : α → Prop, we can consider the subtype
{ x : α | P x }. This type is defined by adding the rule P x to the type α.
-/

variable {α : Type} (P Q : α → Prop) {x : α}

def A (P : α → Prop) := { x : α | P x } --subtype of α defined by P

/-
You may notice that the above notation looks very similar to the set builder notation, and in fact,
sets are modelled as subtypes in lean. More precisely, given a set A of type α, we can consider
P : α → Prop, P x := x ∈ A, and then the subtype { x : α | P x } is equivalent to the set A.
In fact, Lean has a built-in type Set α ('sets of type α'),
it is defined as the type of functions α → Prop.
In particular, statements like A ∈ A for some set A don't make sense in this framework!
-/

#check Set α

#check A (P) -- A has type Set α
/-
This means every set A of type α can be uniquely considered as a predicate P : α → Prop, P_A x := x ∈ A.
Therefore, giving an element of a set A is equivalent to giving an term x : α and a proof of P_A x.
-/

--holds by definition
example (x : α) : x ∈ A P ↔ P x := by rfl

-- A (P) is a subtype of α, so we can use the constructor ⟨x, hx⟩ to construct an element of A P.
example (hx : P x) : A P := by
  exact ⟨x, hx⟩

/- given an element of the subtype A P, we can extract its value and a proof of P y -/
example (y : A P) : α := by
  exact y.val

example (y : A P) : P y.val := by
  exact y.prop

-- lean can automatically coerce y : A P to y.val : α.
example (y : A P) : P y := by
  exact y.prop

/-
Sets and subtypes: Consider the set of primes Primes := {p : ℕ | p.Prime}.
There is a difference between x : Primes and x : ℕ, x.Prime.
Namely, results about natural numbers only apply directly to x : ℕ not to x : Primes. For example:
If we want to multiply p and q, then we need to convert them to natural numbers first.
-/

def Primes : Set ℕ := {p : ℕ | p.Prime}

-- Lean does not know how to multiply p and q!
example (p q : Primes) : ¬ (p * q).Prime := by
  sorry

-- so we need to convert them to natural numbers first.
example (p q : Primes) : ¬ (p.val * q.val).Prime := by
  sorry

/-
The following examples are relevant for the last two exercises of the exercise sheet.
These exercises are a bit harder, and we will talk about sets and subtypes in more detail in
the next lecture. Feel free to try them out, but you can also skip them for now.
-/

-- union of two subtypes corresponds to OR
example (x : α) : x ∈ A P ∪ A Q ↔ P x ∨ Q x := by
  exact Eq.to_iff rfl

-- union of two subtypes corresponds to AND
example (x : α) : x ∈ A P ∩ A Q ↔ P x ∧ Q x := by
  exact Eq.to_iff rfl

-- containment of subtypes corresponds to implication
example : A P ⊆ A Q ↔ ∀ x, P x → Q x := by
  exact Eq.to_iff rfl

-- equalities between subtypes can be proved by extensionality
example (h : ∀ x, P x ↔ Q x) : A P = A Q := by
  ext x
  exact h x

-- alternatively, equality can between sets can be proved by proving both containments
example (h : ∀ x, P x ↔ Q x) : A P = A Q := by
  apply Set.Subset.antisymm_iff.mpr
  constructor
  · sorry
  sorry
