import Mathlib.tactic
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.Sub.Unbundled.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Tactic.Monotonicity.Attr

#check PartialOrder

set_option trace.profiler true in
example (x y z k : ℤ)
    (h : 3 ≤ (4 : ℤ))
    (h' : z ≤ y) :
    (x + 3 + k) - y ≤ (k + 4 + x) - z := by
  mono

/-`norm` rules: Should be equalities or iff. -/
/-`safe` rules: Apply rules. A → B -/
/-`unsafe` rules: Apply rules. A → B -/

attribute [aesop safe]
         mul_lt_mul_of_pos_left mul_lt_mul_of_pos_right
         mul_le_mul_of_nonneg_left mul_le_mul_of_nonneg_right
         mul_le_mul_of_nonpos_left mul_le_mul_of_nonpos_right
         tsub_lt_tsub_left_of_le tsub_lt_tsub_right_of_le


attribute [aesop unsafe] tsub_le_tsub mul_le_mul add_le_add_left
attribute [aesop unsafe] add_le_add

attribute [-simp] neg_le_neg_iff tsub_le_iff_right Nat.sub_le_iff_le_add
  zero_le zero_le' Nat.zero_le

set_option trace.profiler true in
example (x y z k : ℤ)
    (_ : 3 ≤ (4 : ℤ))
    (h' : z ≤ y) :
    (k + 3 + x) - y ≤ (k + 4 + x) - z := by
  aesop

--set_option trace.profiler true in
example (x y z a b : ℕ)
    (h : a ≤ (b : ℕ))
    (h' : z ≤ y) :
    (1 + a + x) - y ≤ (1 + b + x) - z := by
  mono

--set_option trace.profiler true in
example (x y z a b : ℕ)
    (h : a ≤ (b : ℕ))
    (h' : z ≤ y) :
    (1 + a + x) - y ≤ (1 + b + x) - z := by
  aesop

set_option trace.profiler true in
example (x y z : ℤ)
   (h : 3 ≤ (4 : ℤ))
   (h' : z ≤ y) : (x + 3 + 1) - y ≤ (1 + 4 + x) - z := by
  mono

example (x y m n : ℕ) : 0 < y - x ↔ x < y := by exact Nat.sub_pos_iff_lt

lemma t1 {α : Type} {x y : α} (h : x = y) : y = x := by
  exact id (Eq.symm h)

lemma t2 {α : Type} [StrictOrderedSemiring α] {x y z : α} (h : x ≤ y) :
    z + x ≤ z + y := by
  exact (add_le_add_iff_left z).mpr h

lemma t3 {α : Type} [StrictOrderedSemiring α] {x y z : α} (h : x ≤ y) :
    x + z ≤ y + z := by
  exact (add_le_add_iff_right z).mpr h

lemma t4 {α : Type} [StrictOrderedSemiring α] {x y z : α} (h : x ≤ y) :
    x + z ≤ z + y := by
  rw [add_comm]; exact t2 h

lemma t5 {α : Type} [StrictOrderedSemiring α] {x y z : α} (h : x ≤ y) :
    z + x ≤ y + z := by
  rw [add_comm]; exact t3 h

lemma t6 {α : Type} [StrictOrderedSemiring α] {x y z a b c : α}
    (h : x + y + z ≤ a + b + c) :
    x + (y + z) ≤ a + (b + c) := by
  simp_rw [← add_assoc]
  assumption

/-
Why is this faster in the new architecture?

Is it because we are only matching `h` and not the variables?
-/

--set_option trace.profiler true in
set_option aesop.dev.statefulForward true in
example (x y m n : ℕ) (h : x ≤ y) :
    m + x + n ≤ y + n + m := by
  abel_nf
  saturate 2 [t1, t2, t3, t4, t5, t6, *]
  assumption
