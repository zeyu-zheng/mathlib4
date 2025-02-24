import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Util.Qq

open Qq Lean Finset

namespace Mathlib.Tactic.Simp
section lemmas
variable {m n : ℕ} {s : Finset ℕ}

private lemma Icc_eq_insert_of_Icc_succ_eq (hmn : m ≤ n) (hs : Icc (m + 1) n = s) :
    Icc m n = insert m s := by rw [← hs, Nat.Icc_insert_succ_left hmn]

end lemmas

/-- Given natural numbers `m` and `n`, returns `(s, ⊢ Finset.Icc m n = s)`. -/
partial def evalFinsetIccNat (m n : ℕ) (em en : Q(ℕ)) :
    MetaM ((s : Q(Finset ℕ)) × Q(.Icc $em $en = $s)) := do
  sorry

end Mathlib.Tactic.Simp

open Mathlib.Tactic.Simp

namespace Finset

/-- Simproc to compute `Finset.Icc a b` when `a b : ℕ`. -/
simproc_decl Icc_nat (Icc _ _) := fun e ↦ do
  sorry

example : Icc 1 0 = ∅ := by simp only [Icc_nat]
example : Icc 1 1 = {1} := by simp only [Icc_nat]
example : Icc 1 2 = {1, 2} := by simp only [Icc_nat]

end Finset
