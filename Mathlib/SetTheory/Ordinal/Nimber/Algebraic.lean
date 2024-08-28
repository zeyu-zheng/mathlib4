/-
Copyright (c) 2024 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios, Daniel Weber
-/

import Mathlib.Data.Finsupp.WellFounded
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.SetTheory.Ordinal.Nimber.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Algebra.CharP.Subring

universe u v

open Function Order Ordinal Polynomial

noncomputable section

namespace Nimber

instance : CharP Nimber 2 where
  cast_eq_zero_iff' x := by
    sorry


/-- Add nimbers as ordinals. We introduce the notation `a +ₒ b` for this. -/
def ordinalAdd (a b : Nimber) : Nimber := toNimber (toOrdinal a + toOrdinal b)
/-- Multiply nimbers as ordinals. We introduce the notation `a *ₒ b` for this. -/
def ordinalMul (a b : Nimber) : Nimber := toNimber (toOrdinal a * toOrdinal b)
/-- Divide nimbers as ordinals. We introduce the notation `a /ₒ b` for this. -/
def ordinalDiv (a b : Nimber) : Nimber := toNimber (toOrdinal a / toOrdinal b)
/-- Take moduli of nimbers as ordinals. We introduce the notation `a %ₒ b` for this. -/
def ordinalMod (a b : Nimber) : Nimber := toNimber (toOrdinal a % toOrdinal b)
/-- Exponent of nimbers as ordinals. We introduce the notation `a ^ₒ b` for this. -/
def ordinalPow (a : Nimber) (b : ℕ) : Nimber := toNimber (toOrdinal a ^ b)

local infixl:65 " +ₒ " => ordinalAdd
local infixl:70 " *ₒ " => ordinalMul
local infixl:70 " /ₒ " => ordinalDiv
local infixl:70 " %ₒ " => ordinalMod
local infixr:80 " ^ₒ " => ordinalPow

lemma lt_ordinalAdd_iff (a b c : Nimber) : a < b +ₒ c ↔ a < b ∨ ∃ d < c, b +ₒ d = a :=
  lt_add_iff a b c

lemma ordinalDiv_ordinalAdd_ordinalMod (a b : Nimber) : b *ₒ (a /ₒ b) +ₒ a %ₒ b = a :=
  div_add_mod a b

@[simp]
lemma ordinalPow_zero (a : Nimber) : a ^ₒ 0 = 1 := by simp [ordinalPow]

@[simp]
lemma one_ordinalMul (a : Nimber) : 1 *ₒ a = a := by simp [ordinalMul]

@[simp]
lemma ordinalMul_one (a : Nimber) : a *ₒ 1 = a := by simp [ordinalMul]

/-- We consider a nimber to be a group when nimbers less than it are closed under addition. Note we
don't actually require `0 < x`. -/
def IsGroup (x : Nimber) : Prop :=
  ∀ y < x, ∀ z < x, y + z < x

@[simp]
lemma IsGroup_one : IsGroup 1 := by intro _ _ _ _; simp_all [lt_one_iff_zero]

/-- We consider a nimber to be a ring when it is a group, and nimbers less than it are closed under
multiplication. -/
def IsRing (x : Nimber) : Prop :=
  IsGroup x ∧ ∀ y < x, ∀ z < x, y * z < x

/-- We consider a nimber to be a field when it is a ring, and nimbers less than it are closed under
inverses. -/
def IsPrefield (x : Nimber) : Prop :=
  IsRing x ∧ ∀ y < x, y⁻¹ < x

def IsField (x : Nimber) : Prop :=
  IsPrefield x ∧ 1 < x

def IsField.toSubfield {x : Nimber} (hx : IsField x) : Subfield Nimber where
  carrier := Set.Iio x
  mul_mem' {a b} (ha hb) := hx.1.1.2 a ha b hb
  add_mem' {a b} (ha hb) := hx.1.1.1 a ha b hb
  inv_mem' := hx.1.2
  one_mem' := hx.2
  zero_mem' := zero_lt_one.trans hx.2
  neg_mem' := id

@[simp]
lemma algebraMap_subfield {α : Type*} [Field α] {f : Subfield α} (x : f) :
    algebraMap f α x = x :=
  rfl

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
lemma unbounded_isField : Set.Unbounded (· < ·) {x | IsPrefield x} := by
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

lemma Polynomial.degree_erase_lt_of_degree_le  {R : Type u} [Semiring R] (p : Polynomial R) {n : ℕ}
    (hp : p.degree ≤ n) : (p.erase n).degree < n := by
  rcases lt_or_eq_of_le hp with hp | hp
  · exact (degree_erase_le _ _).trans_lt hp
  · rw [← hp, ← natDegree_eq_of_degree_eq_some hp]
    apply Polynomial.degree_erase_lt
    intro nh
    simp [nh] at hp

lemma degree_C_mul_le {R : Type u} [Semiring R] (p : Polynomial R) (x : R) :
    (C x * p).degree ≤ p.degree := calc
  (C x * p).degree ≤ (C x).degree + p.degree := degree_mul_le (C x) p
  _ ≤ 0 + p.degree := by gcongr; exact degree_C_le
  _ = p.degree := zero_add _

lemma two_eq_zero : (2 : Nimber) = 0 := calc
  (2 : Nimber) = Nat.cast 2 := rfl
  _ = Nat.cast 1 + 1 := Nat.cast_add_one 1
  _ = 0 := by simp

count_heartbeats in
private lemma lemma2' {x : Nimber} {n m : ℕ} (hx : IsField x) (hm : m ≤ n)
    (h : ∀ p : Polynomial hx.toSubfield, 0 < p.degree → p.degree ≤ n → ∃ y, p.IsRoot y) :
    (∀ y < x ^ₒ m, ∃ p : Polynomial hx.toSubfield, p.degree < m ∧ aeval x p = y) ∧
    (∀ p : Polynomial hx.toSubfield, p.degree < m → aeval x p < x ^ₒ m) ∧
    (x ^ₒ m).IsGroup ∧
    ∀ y < x, x ^ m * y = x ^ₒ m *ₒ y := by
  have xne : x ≠ 0 := fun nh ↦ absurd hx.2 (by simp [nh])
  induction m with
  | zero => simp [lt_one_iff_zero]
  | succ m hind =>
  obtain ⟨psl1, psl2, pg, pindl⟩ := hind (by omega)
  clear hind
  have sl1 : ∀ y < x ^ₒ (m + 1), ∃ p : Polynomial hx.toSubfield, p.degree < (m + 1) ∧
      aeval x p = y := by
    -- sorry
    intro y hy
    have := ordinalDiv_ordinalAdd_ordinalMod y (x ^ₒ m)
    have b1 : y /ₒ (x ^ₒ m) < x := by
      apply_fun toOrdinal
      simp [ordinalDiv, ordinalPow]
      rw [Ordinal.div_lt, ← pow_succ]
      exact hy
      simp [xne]
    have b2 : y %ₒ (x ^ₒ m) < x ^ₒ m := by
      apply mod_lt
      simp [xne, ordinalPow]
    rw [← ordinalMul_add_of_isGroup pg _ b2, ← pindl _ b1] at this
    obtain ⟨q, hq, h⟩ := psl1 (y %ₒ (x ^ₒ m)) b2
    use X ^ m * C ⟨_, b1⟩ + q, ?_, ?_
    · change _ < Order.succ (m : WithBot ℕ)
      rw [lt_succ_iff]
      apply Polynomial.degree_add_le_of_degree_le
      · rw [mul_comm]
        apply Polynomial.degree_C_mul_X_pow_le
      · exact hq.le
    simp only [map_add, map_mul, aeval_C, map_pow, aeval_X, h]
    conv =>
      rhs; rw [← this]
    simp only [add_left_inj]
    rfl
  use sl1
  have sl2 : ∀ p : Polynomial hx.toSubfield, p.degree < m + 1 → aeval x p < x ^ₒ (m + 1) := by
    -- sorry
    intro p hp
    change _ < Order.succ (m : WithBot ℕ) at hp
    rw [lt_succ_iff] at hp
    rw [← Polynomial.monomial_add_erase p m]
    simp only [map_add, aeval_monomial]
    have : (aeval x) (erase m p) < x ^ₒ m := by
      apply psl2
      apply Polynomial.degree_erase_lt_of_degree_le _ hp
    rw [mul_comm, pindl, ordinalMul_add_of_isGroup pg _ this]
    · apply lt_of_lt_of_le
        (b := x ^ₒ m *ₒ (algebraMap (↥hx.toSubfield) Nimber) (p.coeff m) +ₒ x ^ₒ m)
      · simp only [ordinalAdd, OrderIso.lt_iff_lt, add_lt_add_iff_left, this]
      · simp only [ordinalAdd, ordinalMul, ordinalPow, toNimber_toOrdinal, OrderIso.le_iff_le,
          ← Ordinal.mul_succ, pow_succ]
        rw [Ordinal.mul_le_mul_iff_left]
        · simp only [succ_le_iff, OrderIso.lt_iff_lt]
          exact (p.coeff m).2
        · simp [Ordinal.pos_iff_ne_zero, xne]
    exact (p.coeff m).2
  use sl2
  constructor
  · -- sorry
    intro a ha b hb
    obtain ⟨ap, apd, rfl⟩ := sl1 a ha
    obtain ⟨bp, bpd, rfl⟩ := sl1 b hb
    rw [← map_add]
    apply sl2
    apply Polynomial.degree_add_lt_of_degree_lt apd bpd
  have sl3 : ∀ y < x ^ₒ (m + 1), ∀ a < x, y * a < x ^ₒ (m + 1) := by
    intro y hy a ha
    obtain ⟨p, pd, rfl⟩ := sl1 y hy
    convert_to aeval x (C ⟨a, ha⟩ * p) < _
    · simp [mul_comm]
    apply sl2
    exact (degree_C_mul_le _ _).trans_lt pd
  have sl4 : x ^ₒ (m + 1) = x ^ (m + 1) := by
    have psl4 := pindl 1 hx.2
    simp only [mul_one, ordinalMul_one] at psl4
    rw [pow_succ, mul_def]
    trans sInf (Set.Iio (x ^ₒ (m + 1)))ᶜ
    · simp
    congr
    ext y
    constructor
    · haveI : CharP hx.toSubfield 2 := inferInstance
      intro hy
      rw [Set.mem_Iio] at hy
      obtain ⟨p, pd, rfl⟩ := sl1 y hy
      rw [Set.mem_setOf_eq]
      let f := X ^ (m + 1) + p
      have pf : p = f + X ^ (m + 1) := calc
        p = (C 0) * X ^ (m + 1) + p := by simp
        _ = (C (1 + 1)) * X ^ (m + 1) + p := by
          reduce_mod_char!
        _ = X ^ (m + 1) + X ^ (m + 1) + p := by simp [add_mul]
        _ = (X ^ (m + 1) + p) + X ^ (m + 1) := by ring
        _ = f + X ^ (m + 1) := rfl
      have fdeg : f.degree = m + 1 := by
        rw [Polynomial.degree_add_eq_left_of_degree_lt]
        · simp
        · simp [pd]
      have fmonic : f.Monic := by
        apply Polynomial.Monic.add_of_left
        · simp
        · simp [pd]
      obtain ⟨r, hr⟩ := h f (by simp only [fdeg]; norm_cast; omega)
        (by simp only [fdeg]; exact_mod_cast hm)
      rw [← Polynomial.mul_div_eq_iff_isRoot] at hr
      generalize hg : f / (X - C r) = g at hr
      have gmonic : g.Monic := by
        simp [← hg, Polynomial.Monic.def, Polynomial.leadingCoeff_div
          (show (X - C r).degree ≤ f.degree by simp only [degree_X_sub_C, fdeg]; norm_cast; omega)]
        exact fmonic
      have gdeg : g.degree = m := by
        apply_fun Polynomial.degree at hr
        simp [fdeg] at hr
        rw [add_comm] at hr
        exact WithBot.add_right_cancel (by simp) hr
      use aeval x (g + X ^ m), ?_, r, ?_
      · rw [pf, ← hr]
        simp only [map_add, map_pow, aeval_X, map_mul, map_sub, aeval_C, algebraMap_subfield,
          Nimber.sub_eq]
        ring_nf
        rw [two_eq_zero]
        ring
      · rw [psl4]
        apply psl2
        rw [← gdeg]
        convert Polynomial.degree_eraseLead_lt _ using 2
        · rw [← Polynomial.self_sub_C_mul_X_pow, gmonic]
          simp only [map_one, one_mul]
          reduce_mod_char!
          congr
          rw [eq_comm]
          exact natDegree_eq_of_degree_eq_some gdeg
        · intro nh
          simp [nh] at gmonic
      · exact r.2
    · intro hy
      simp only [Set.mem_setOf_eq] at hy
      rw [Set.mem_Iio]
      obtain ⟨a, ha, b, hb, rfl⟩ := hy
      rw [psl4] at ha
      obtain ⟨p, pdeg, rfl⟩ := psl1 a ha
      convert_to aeval x (p * X + X ^ m * C ⟨b, hb⟩ + p * C ⟨b, hb⟩) < _
      · simp
        rw [mul_comm]
      apply sl2
      change _ < Order.succ (m : WithBot ℕ)
      rw [lt_succ_iff]
      compute_degree
      simp
      constructor
      constructor
      · generalize p.degree = pd at pdeg ⊢
        cases pd
        · simp
        · exact pdeg.succ_le
      · rfl
      · exact pdeg.le
  sorry

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
lemma mem_min_roots_of_isField {x : Nimber} (hx : IsPrefield x) (hp : (poly x).Nonempty) :
    x ∈ (wellFounded_polynomial_LT.min _ hp).roots :=
  sorry





/-- The nimbers are algebraically closed. -/
instance : IsAlgClosed Nimber := by
  apply IsAlgClosed.of_exists_root
  intro p _ _
  apply wellFounded_polynomial_LT.induction p
  intro p IH

end Nimber
