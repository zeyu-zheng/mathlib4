/-
Copyright (c) 2024 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios, Daniel Weber
-/

import Mathlib.Data.Finsupp.WellFounded
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.SetTheory.Ordinal.Nimber.Basic

universe u v

open Function Order Ordinal Polynomial

noncomputable section

namespace Nimber

/-- Add nimbers as ordinals. We introduce the notation `a +∘ b` for this. -/
def ordinalAdd (a b : Nimber) : Nimber := toNimber (toOrdinal a + toOrdinal b)
/-- Multiply nimbers as ordinals. We introduce the notation `a *∘ b` for this. -/
def ordinalMul (a b : Nimber) : Nimber := toNimber (toOrdinal a * toOrdinal b)
/-- Divide nimbers as ordinals. We introduce the notation `a /∘ b` for this. -/
def ordinalDiv (a b : Nimber) : Nimber := toNimber (toOrdinal a / toOrdinal b)
/-- Take moduli of nimbers as ordinals. We introduce the notation `a %∘ b` for this. -/
def ordinalMod (a b : Nimber) : Nimber := toNimber (toOrdinal a % toOrdinal b)

local infixl:65 " +ₒ " => ordinalAdd
local infixl:70 " *ₒ " => ordinalMul
local infixl:70 " /ₒ " => ordinalDiv
local infixl:70 " %ₒ " => ordinalMod

lemma lt_ordinalAdd_iff (a b c : Nimber) : a < b +ₒ c ↔ a < b ∨ ∃ d < c, b +ₒ d = a :=
  lt_add_iff a b c

lemma ordinalDiv_ordinalAdd_ordinalMod (a b : Nimber) : b *ₒ (a /ₒ b) +ₒ a %ₒ b = a :=
  div_add_mod a b

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
  blsub₂ (toOrdinal x) (toOrdinal x)
    (fun {a} _ {b} _ ↦ toOrdinal (toNimber a + toNimber b))

lemma mem_addify {x y z : Nimber} (hy : y < x) (hz : z < x) : y + z < x.addify :=
  lt_blsub₂ _ hy hz

/-- The smallest nimber containing all products of nimbers less than `x`. -/
def mulify (x : Nimber.{u}) : Nimber.{u} :=
  blsub₂ (toOrdinal x) (toOrdinal x)
    (fun {a} _ {b} _ ↦ toOrdinal (toNimber a * toNimber b))

lemma mem_mulify {x y z : Nimber} (hy : y < x) (hz : z < x) :
    y * z < x.mulify :=
  lt_blsub₂ _ hy hz

/-- The smallest nimber containing all inverses of nimbers less than `x`. -/
def invify (x : Nimber.{u}) : Nimber.{u} :=
  blsub (toOrdinal x) (fun {a} _ ↦ toOrdinal (toNimber a)⁻¹)

lemma mem_invify {x y : Nimber} (hy : y < x) : y⁻¹ < x.invify :=
  lt_blsub _ _ hy

/-def max' (s : Finset Nimber) : Nimber :=
  s.max.recOn 0 id

theorem le_max' (s : Finset Nimber) (y : Nimber) : y ≤ s-/

/-- The smallest nimber containing all the roots of polynomials with coefficients less than `x`. -/
def algify (x : Nimber.{u}) : Nimber.{u} :=
  ⨆ p : {p : Polynomial Nimber // ∀ c ∈ p.coeffs, c < x},
    succ (p.1.roots.toFinset.max.recOn 0 id)

open Classical in
/-- Enumerates the polynomials in the definition of `algify x` by a type in the same universe. -/
def algify_enum {x : Nimber.{u}} (hx : x ≠ 0) (f : ℕ → (toOrdinal x).out.α) : Nimber.{u}[X] :=
  let H : Zero (toOrdinal x).out.α := zero_out hx
  have _ : IsWellOrder (toOrdinal x).out.α (· < ·) := inferInstance
  if hf : (Function.support f).Finite then Polynomial.ofFinsupp <| Finsupp.mk
    hf.toFinset
    (fun n => toNimber <| typein (· < ·) (f n))
    (by
      have : toNimber (typein (· < ·) H.zero) = 0 := typein_enum _ _
      rw [← this]
      simp
      intro
      rfl
    )
  else 0

theorem small_aux (x : Nimber.{u}) :
    Small.{u} {p : Polynomial Nimber.{u} // ∀ c ∈ p.coeffs, c < x} := by
  obtain rfl | hx := eq_or_ne x 0
  · simp_rw [Nimber.not_lt_zero, imp_false, ← Finset.eq_empty_iff_forall_not_mem, coeffs_eq_empty]
    exact small_subsingleton _
  · apply small_subset (s := Set.range <| algify_enum hx)
    intro p (hp : ∀ c ∈ p.coeffs, _)
    let H : Zero (toOrdinal x).out.α := zero_out hx
    use Finsupp.mk
      p.support
      (fun n => enum (· < ·) (toOrdinal <| p.coeff n) (by
        rw [type_lt]
        obtain hn | hn := eq_or_ne (p.coeff n) 0
        · rw [hn]
          exact Nimber.pos_iff_ne_zero.2 hx
        · exact hp _ <| coeff_mem_coeffs p n hn
      ))
      (by
        intro a
        change _ ↔ enum (· < ·) _ _ ≠ (zero_out hx).zero
        unfold Zero.zero zero_out
        dsimp
        rw [enum_inj, mem_support_iff]
        rfl
      )
    simp_rw [algify_enum, Finsupp.finite_support]
    simp
    ext
    rfl

/-lemma mem_algify {x y : Nimber} {p : Nimber[X]}
    (hp : ∀ c ∈ p.coeffs, c < x) (hy : y ∈ p.roots) : y < x.algify := by
  rw [← succ_le_iff]
  apply (le_ciSup_iff' _).2
  · sorry
  · apply @bddAbove_of_small _ _
    apply small_subset





#exit-/

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

lemma monotone_iterate_of_id_le {α : Type*} [Preorder α] {f : α → α} (hf : id ≤ f) (x : α) :
    Monotone fun n ↦ f^[n] x :=
  monotone_nat_of_le_succ fun n ↦ iterate_succ' f n ▸ hf _

/-- The nimbers that form fields are a proper class. -/
-- Lemma 3
lemma unbounded_isField : Set.Unbounded (· < ·) {x | IsField x} := by
  intro x
  simp_rw [not_lt, and_comm]
  refine ⟨sup fun n ↦ fieldify^[n] x, le_sup _ 0, ⟨?_, ?_⟩, ?_⟩
  iterate 2 {
    intro y hy z hz
    rw [lt_sup] at *
    obtain ⟨yi, hy⟩ := hy
    obtain ⟨zi, hz⟩ := hz
    replace hy := hy.trans_le (monotone_iterate_of_id_le le_fieldify x <| le_max_left yi zi)
    replace hz := hz.trans_le (monotone_iterate_of_id_le le_fieldify x <| le_max_right yi zi)
    use (max yi zi) + 1
    rw [iterate_succ']
    try exact add_mem_fieldify hy hz
    try exact mul_mem_fieldify hy hz
  }
  intro y hy
  rw [lt_sup] at *
  obtain ⟨yi, hy⟩ := hy
  use yi + 1
  rw [iterate_succ']
  exact inv_mem_fieldify hy

-- Lemma 1
lemma ordinalMul_add_of_isGroup {x z : Nimber} (hx : IsGroup x) (y : Nimber) (hz : z < x) :
    x *ₒ y + z = x *ₒ y +ₒ z := by
  have xne : x ≠ 0 := fun nh ↦ Nimber.not_lt_zero _ <| nh ▸ hz
  have add_lt_of_lt (w : Nimber) (h : w < x *ₒ y) : w + z < x *ₒ y := by
    have h₁ : w /ₒ x < y := (div_lt xne).mpr h
    have h₂ : w %ₒ x < x := mod_lt w xne
    have h₃ : w %ₒ x + z < x := hx _ h₂ z hz
    rw [← ordinalDiv_ordinalAdd_ordinalMod w x, ← ordinalMul_add_of_isGroup hx _ h₂, add_assoc,
      ordinalMul_add_of_isGroup hx _ h₃]
    unfold ordinalAdd ordinalMul
    apply lt_of_lt_of_le
    · rwa [OrderIso.lt_iff_lt, add_lt_add_iff_left, OrderIso.lt_iff_lt]
    · simp only [toNimber_toOrdinal, map_le_map_iff]
      rwa [← mul_succ, mul_le_mul_iff_left, succ_le_iff, OrderIso.lt_iff_lt]
      rwa [Ordinal.pos_iff_ne_zero, ne_eq, toOrdinal_eq_zero]
  rw [add_def]
  trans sInf {w | w < x *ₒ y +ₒ z}ᶜ
  · congr! with w
    rw [lt_ordinalAdd_iff]
    congr! 3 with d
    · simp_rw [add_eq_iff_eq_add, exists_eq_right]
      constructor
      · convert add_lt_of_lt (w + z)
        rw [add_assoc, add_self, add_zero]
      · exact add_lt_of_lt _
    · rw [and_congr_right_iff]
      intro hd
      congr! 1
      exact ordinalMul_add_of_isGroup hx _ (hd.trans hz)
  · simp [Set.Iio_def]
termination_by (y, z)

/-- The lexicographic ordering on polynomials. -/
def polynomial_LT (p q : Nimber[X]) : Prop :=
  Finsupp.Lex (· > ·) (· < ·) p.toFinsupp q.toFinsupp

local infixl:50 " ≺ " => polynomial_LT

theorem wellFounded_polynomial_LT : WellFounded (· ≺ ·) := by
  apply InvImage.wf
  exact Finsupp.Lex.wellFounded' Nimber.not_lt_zero lt_wf Nat.lt_wfRel.wf

/-- For a nimber `x`, the set of non-constant polynomials with coefficients less than `x`, without a
root less than `x`. -/
def poly (x : Nimber) : Set Nimber[X] :=
  {p | 1 ≤ p.degree ∧ (∀ c ∈ p.coeffs, c < x) ∧ ∀ r ∈ p.roots, x ≤ r}

-- Lemma 4
lemma mem_min_roots_of_isField {x : Nimber} (hx : IsField x) (hp : (poly x).Nonempty) :
    x ∈ (wellFounded_polynomial_LT.min _ hp).roots :=
  sorry





/-- The nimbers are algebraically closed. -/
instance : IsAlgClosed Nimber := by
  apply IsAlgClosed.of_exists_root
  intro p _ _
  apply wellFounded_polynomial_LT.induction p
  intro p IH

end Nimber
