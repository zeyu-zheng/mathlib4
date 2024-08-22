/-
Copyright (c) 2024 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
import Mathlib.Data.Nat.Bitwise
import Mathlib.SetTheory.Ordinal.CantorNormalForm

/-!
# Ordinal XOR

We define a bitwise XOR on ordinals by taking the pairwise `Nat.Xor` of coefficients in their base ω
Cantor normal forms.

This operation is relevant to game theory, where it describes the Sprague-Grundy value of a sum of
two Nim heaps.
-/

noncomputable section

universe u

namespace Ordinal


/-- The XOR of two ordinals is computed by XOR-ing each pair of corresponding natural coefficients
in the base `ω` Cantor normal form. -/
instance : Xor Ordinal :=
  ⟨fun a b => CNF_omega_eval <| (CNF_omega_coeff a).zipWith _ (Nat.zero_xor 0) (CNF_omega_coeff b)⟩

theorem xor_def (a b : Ordinal) : a ^^^ b =
    CNF_omega_eval ((CNF_omega_coeff a).zipWith _ (Nat.zero_xor 0) (CNF_omega_coeff b)) := by
  rfl

theorem CNF_omega_coeff_xor (a b e : Ordinal) :
    CNF_omega_coeff (a ^^^ b) e = CNF_omega_coeff a e ^^^ CNF_omega_coeff b e :=
  CNF_omega_coeff_CNF_omega_eval_apply _ e

/-! We port the results from Mathlib.Data.Nat.Bitwise in a mostly one to one manner. -/

@[simp]
protected theorem xor_self (a : Ordinal) : a ^^^ a = 0 := by
  rw [← CNF_omega_coeff_inj]
  ext e
  rw [CNF_omega_coeff_xor, Nat.xor_self, CNF_omega_coeff_zero_apply]

protected theorem xor_comm (a b : Ordinal) : a ^^^ b = b ^^^ a := by
  rw [← CNF_omega_coeff_inj]
  ext e
  rw [CNF_omega_coeff_xor, Nat.xor_comm, CNF_omega_coeff_xor]

protected theorem xor_assoc (a b c : Ordinal) : a ^^^ b ^^^ c = a ^^^ (b ^^^ c) := by
  rw [← CNF_omega_coeff_inj]
  ext e
  rw [CNF_omega_coeff_xor, CNF_omega_coeff_xor, Nat.xor_assoc,
    CNF_omega_coeff_xor, CNF_omega_coeff_xor]

@[simp]
protected theorem zero_xor (a : Ordinal) : 0 ^^^ a = a := by
  rw [← CNF_omega_coeff_inj]
  ext e
  rw [CNF_omega_coeff_xor, CNF_omega_coeff_zero_apply, Nat.zero_xor]

@[simp]
protected theorem xor_zero (a : Ordinal) : a ^^^ 0 = a := by
  rw [Ordinal.xor_comm, Ordinal.zero_xor]

protected theorem xor_cancel_right (a b : Ordinal) : b ^^^ a ^^^ a = b := by
  rw [Ordinal.xor_assoc, Ordinal.xor_self, Ordinal.xor_zero]

protected theorem xor_cancel_left (a b : Ordinal) : a ^^^ (a ^^^ b) = b := by
  rw [← Ordinal.xor_assoc, Ordinal.xor_self, Ordinal.zero_xor]

protected theorem xor_right_injective (a : Ordinal) : Function.Injective (a ^^^ ·) := by
  intro b c h
  dsimp at h
  rw [← Ordinal.xor_cancel_left a b, h, Ordinal.xor_cancel_left]

protected theorem xor_left_injective (a : Ordinal) : Function.Injective (· ^^^ a) := by
  intro b c h
  dsimp at h
  rw [← Ordinal.xor_cancel_right a b, h, Ordinal.xor_cancel_right]

@[simp]
protected theorem xor_right_inj {a b c : Ordinal} : a ^^^ b = a ^^^ c ↔ b = c :=
  (Ordinal.xor_right_injective a).eq_iff

@[simp]
protected theorem xor_left_inj {a b c : Ordinal} : b ^^^ a = c ^^^ a ↔ b = c :=
  (Ordinal.xor_left_injective a).eq_iff

@[simp]
protected theorem xor_eq_zero {a b : Ordinal} : a ^^^ b = 0 ↔ a = b := by
  rw [← Ordinal.xor_self b, Ordinal.xor_left_inj]

protected theorem xor_ne_zero {a b : Ordinal} : a ^^^ b ≠ 0 ↔ a ≠ b :=
  Ordinal.xor_eq_zero.not

@[simp]
theorem natCast_xor (m n : ℕ) : (m : Ordinal) ^^^ n = (m ^^^ n : ℕ) := by
  rw [xor_def]
  simp

protected theorem xor_trichotomy {a b c : Ordinal} (h : a ≠ b ^^^ c) :
  b ^^^ c < a ∨ a ^^^ c < b ∨ a ^^^ b < c := sorry

end Ordinal
