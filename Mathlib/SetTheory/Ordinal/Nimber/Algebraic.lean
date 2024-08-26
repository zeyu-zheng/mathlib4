/-
Copyright (c) 2024 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios, Daniel Weber
-/

import Mathlib.SetTheory.Ordinal.Nimber.Basic

universe u v

open Function Order

noncomputable section

namespace Nimber

/-- Add nimbers as ordinals. We introduce the notation `a +∘ b` for this. -/
def ordinalAdd (a b : Nimber) : Nimber := Ordinal.toNimber (toOrdinal a + toOrdinal b)
/-- Multiply nimbers as ordinals. We introduce the notation `a *∘ b` for this. -/
def ordinalMul (a b : Nimber) : Nimber := Ordinal.toNimber (toOrdinal a * toOrdinal b)
/-- Divide nimbers as ordinals. We introduce the notation `a /∘ b` for this. -/
def ordinalDiv (a b : Nimber) : Nimber := Ordinal.toNimber (toOrdinal a / toOrdinal b)
/-- Take moduli of nimbers as ordinals. We introduce the notation `a %∘ b` for this. -/
def ordinalMod (a b : Nimber) : Nimber := Ordinal.toNimber (toOrdinal a % toOrdinal b)

local infixl:65 " +ₒ " => ordinalAdd
local infixl:70 " *ₒ " => ordinalMul
local infixl:70 " /ₒ " => ordinalDiv
local infixl:70 " %ₒ " => ordinalMod

lemma lt_ordinalAdd_iff (a b c : Nimber) : a < b +ₒ c ↔ a < b ∨ ∃ d < c, b +ₒ d = a :=
  Ordinal.lt_add_iff a b c

lemma ordinalDiv_ordinalAdd_ordinalMod (a b : Nimber) :
    b *ₒ (a /ₒ b) +ₒ a %ₒ b = a :=
  Ordinal.div_add_mod _ _

/-- We consider a nimber to be a group when nimbers less than it are closed under addition. Note we
don't actually require `0 < x`. -/
def IsGroup (x : Nimber) : Prop :=
  ∀ y < x, ∀ z < x, y + z < x

/-- We consider a nimber to be a ring when it is a group, and nimbers less than it are closed under
multiplication. -/
def IsRing (x : Nimber) : Prop :=
  IsGroup x ∧ ∀ y < x, ∀ z < x, y * z < x

/-- We consider a nimber to be a field when it is a ring, and nimbers less than it are closed under
inverses. -/
def IsField (x : Nimber) : Prop :=
  IsRing x ∧ ∀ y < x, y⁻¹ < x

/-- The smallest nimber containing all additions of nimbers less than `x`. -/
def addify (x : Nimber.{u}) : Nimber.{u} :=
  Ordinal.blsub₂ (toOrdinal x) (toOrdinal x)
    (fun {a} _ {b} _ ↦ toOrdinal (Ordinal.toNimber a + Ordinal.toNimber b))

lemma mem_addify {x y z : Nimber} (hy : y < x) (hz : z < x) : y + z < x.addify :=
  Ordinal.lt_blsub₂ _ hy hz

/-- The smallest nimber containing all products of nimbers less than `x`. -/
def mulify (x : Nimber.{u}) : Nimber.{u} :=
  Ordinal.blsub₂ (toOrdinal x) (toOrdinal x)
    (fun {a} _ {b} _ ↦ toOrdinal (Ordinal.toNimber a * Ordinal.toNimber b))

lemma mem_mulify {x y z : Nimber} (hy : y < x) (hz : z < x) :
    y * z < x.mulify :=
  Ordinal.lt_blsub₂ _ hy hz

/-- The smallest nimber containing all inverses of nimbers less than `x`. -/
def invify (x : Nimber.{u}) : Nimber.{u} :=
  Ordinal.blsub (toOrdinal x) (fun {a} _ ↦ toOrdinal (Ordinal.toNimber a)⁻¹)

lemma mem_invify {x y : Nimber} (hy : y < x) : y⁻¹ < x.invify :=
  Ordinal.lt_blsub _ _ hy

/-- The smallest nimber containing all sums, products, and inverses of nimbers less than `x`. -/
@[reducible]
def fieldify (x : Nimber) : Nimber :=
  x ⊔ addify x ⊔ mulify x ⊔ invify x

lemma le_fieldify (x : Nimber) : x ≤ fieldify x := by simp

lemma add_mem_fieldify {x y z : Nimber} (hy : y < x) (hz : z < x) : y + z < x.fieldify :=
  (mem_addify hy hz).trans_le (by simp)

lemma mul_mem_fieldify {x y z : Nimber} (hy : y < x) (hz : z < x) : y * z < x.fieldify :=
  (mem_mulify hy hz).trans_le (by simp)

lemma inv_mem_fieldify {x y : Nimber} (hy : y < x) : y⁻¹ < x.fieldify :=
  (mem_invify hy).trans_le (by simp)

lemma monotone_iterate_of_forall_le {α : Type*} [Preorder α] {f : α → α}
    (hf : ∀ x, x ≤ f x) (x : α) :
    Monotone (fun n ↦ f^[n] x) := by
  intro n m hnm
  have : m = (m - n) + n := by omega
  rw [this]
  simp only [iterate_add_apply]
  apply id_le_iterate_of_id_le hf

lemma lemma3 (x : Nimber) :
    ∃ y ≥ x, IsField y := by
  use Ordinal.sup fun (n : ℕ) ↦ fieldify^[n] x
  constructor
  · exact Ordinal.le_sup _ 0
  constructor
  constructor
  repeat {
    intro y hy z hz
    rw [Ordinal.lt_sup] at *
    obtain ⟨yi, hy⟩ := hy
    obtain ⟨zi, hz⟩ := hz
    replace hy : y < fieldify^[max yi zi] x :=
      hy.trans_le (by apply monotone_iterate_of_forall_le le_fieldify; simp)
    replace hz : z < fieldify^[max yi zi] x :=
      hz.trans_le (by apply monotone_iterate_of_forall_le le_fieldify; simp)
    use (max yi zi) + 1
    simp only [iterate_succ', comp_apply]
    try apply add_mem_fieldify hy hz
    try apply mul_mem_fieldify hy hz
  }
  · intro y hy
    rw [Ordinal.lt_sup] at *
    obtain ⟨yi, hy⟩ := hy
    use yi + 1
    simp only [iterate_succ', comp_apply]
    apply inv_mem_fieldify hy

lemma ordinalMul_add_of_isGroup {x : Nimber} (hx : IsGroup x) {y z : Nimber} (hz : z < x) :
    x *ₒ y + z = x *ₒ y +ₒ z := by
  have xne : x ≠ 0 := fun nh ↦ by
    simp [nh, Nimber.not_lt_zero] at hz
  have add_lt_of_lt (w : Nimber) (h : w < x *ₒ y) : w + z < x *ₒ y := by
    have : w = x *ₒ (w /ₒ x) +ₒ w %ₒ x :=
      (ordinalDiv_ordinalAdd_ordinalMod w x).symm
    have _ : w /ₒ x < y := by
      apply (Ordinal.div_lt xne).mpr
      exact h
    have _ : w %ₒ x < x :=
      Ordinal.mod_lt _ xne
    have _ : w %ₒ x + z < x := by
      apply hx <;> assumption
    rw [← ordinalMul_add_of_isGroup hx ‹_›] at this
    · rw [this, add_assoc, ordinalMul_add_of_isGroup hx ‹_›]
      apply lt_of_lt_of_le (b := x *ₒ (w /ₒ x) +ₒ x)
      · unfold ordinalAdd
        simpa only [OrderIso.lt_iff_lt, add_lt_add_iff_left]
      · unfold ordinalAdd ordinalMul
        simp only [Ordinal.toNimber_toOrdinal, map_le_map_iff]
        rw [← Ordinal.mul_succ, Ordinal.mul_le_mul_iff_left]
        · simpa
        · simpa [Ordinal.pos_iff_ne_zero]
  rw [add_def]
  trans sInf {w | w < x *ₒ y +ₒ z}ᶜ
  · congr! with w
    rw [lt_ordinalAdd_iff]
    congr! 3 with d
    · simp_rw [add_eq_iff_eq_add, exists_eq_right]
      constructor
      · convert add_lt_of_lt (w + z)
        rw [add_assoc, add_self, add_zero]
      · apply add_lt_of_lt
    · rw [and_congr_right_iff]
      intro hd
      congr! 1
      apply ordinalMul_add_of_isGroup hx (hd.trans hz)
  · simp [Set.Iio_def]
termination_by (y, z)

end Nimber
