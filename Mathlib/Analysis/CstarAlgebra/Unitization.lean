import Mathlib.Tactic.Have
/-
Copyright (c) 2022 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
import Mathlib.Analysis.CstarAlgebra.Basic
import Mathlib.Analysis.Normed.Algebra.Unitization
/-! # The minimal unitization of a C⋆-algebra

This file shows that when `E` is a C⋆-algebra (over a densely normed field `𝕜`), that the minimal
`Unitization` is as well. In order to ensure that the norm structure is available, we must first
show that every C⋆-algebra is a `RegularNormedAlgebra`.

In addition, we show that in a `RegularNormedAlgebra` which is a `StarRing` for which the
involution is isometric, that multiplication on the right is also an isometry (i.e.,
`Isometry (ContinuousLinearMap.mul 𝕜 E).flip`).
-/

open ContinuousLinearMap

local postfix:max "⋆" => star

variable (𝕜 : Type*) {E : Type*}

namespace ContinuousLinearMap

variable [NontriviallyNormedField 𝕜] [NonUnitalNormedRing E] [StarRing E] [NormedStarGroup E]
variable [NormedSpace 𝕜 E] [IsScalarTower 𝕜 E E] [SMulCommClass 𝕜 E E] [RegularNormedAlgebra 𝕜 E]

lemma opNorm_mul_flip_apply (a : E) : ‖(mul 𝕜 E).flip a‖ = ‖a‖ := by
  refine le_antisymm
    (opNorm_le_bound _ (norm_nonneg _) fun b => by simpa only [mul_comm] using norm_mul_le b a) ?_
  suffices ‖mul 𝕜 E (star a)‖ ≤ ‖(mul 𝕜 E).flip a‖ by simpa using this
  refine opNorm_le_bound _ (norm_nonneg _) fun b => ?_
  calc ‖mul 𝕜 E (star a) b‖ = ‖(mul 𝕜 E).flip a (star b)‖ := by simpa using norm_star (star b * a)
    _ ≤ ‖(mul 𝕜 E).flip a‖ * ‖b‖ := by simpa using le_opNorm ((mul 𝕜 E).flip a) (star b)

@[deprecated (since := "2024-02-02")] alias op_norm_mul_flip_apply := opNorm_mul_flip_apply

lemma opNNNorm_mul_flip_apply (a : E) : ‖(mul 𝕜 E).flip a‖₊ = ‖a‖₊ :=
  Subtype.ext (opNorm_mul_flip_apply 𝕜 a)

@[deprecated (since := "2024-02-02")] alias op_nnnorm_mul_flip_apply := opNNNorm_mul_flip_apply

variable (E)

lemma isometry_mul_flip : Isometry (mul 𝕜 E).flip :=
  AddMonoidHomClass.isometry_of_norm _ (opNorm_mul_flip_apply 𝕜)

end ContinuousLinearMap

variable [DenselyNormedField 𝕜] [NonUnitalNormedRing E] [StarRing E] [CstarRing E]
variable [NormedSpace 𝕜 E] [IsScalarTower 𝕜 E E] [SMulCommClass 𝕜 E E]
variable (E)

/-- A C⋆-algebra over a densely normed field is a regular normed algebra. -/
instance CstarRing.instRegularNormedAlgebra : RegularNormedAlgebra 𝕜 E where
  isometry_mul' := AddMonoidHomClass.isometry_of_norm (mul 𝕜 E) fun a => NNReal.eq_iff.mp <|
    show ‖mul 𝕜 E a‖₊ = ‖a‖₊ by
    rw [← sSup_closed_unit_ball_eq_nnnorm]
    refine csSup_eq_of_forall_le_of_forall_lt_exists_gt ?_ ?_ fun r hr => ?_
    exact (Metric.nonempty_closedBall.mpr zero_le_one).image _
    rintro - ⟨x, hx, rfl⟩
    exact
      ((mul 𝕜 E a).unit_le_opNorm x <| mem_closedBall_zero_iff.mp hx).trans
        (opNorm_mul_apply_le 𝕜 E a)
    have ha : 0 < ‖a‖₊ := zero_le'.trans_lt hr
    rw [← inv_inv ‖a‖₊, NNReal.lt_inv_iff_mul_lt (inv_ne_zero ha.ne')] at hr
    obtain ⟨k, hk₁, hk₂⟩ :=
      NormedField.exists_lt_nnnorm_lt 𝕜 (mul_lt_mul_of_pos_right hr <| inv_pos.2 ha)
    refine ⟨_, ⟨k • star a, ?_, rfl⟩, ?_⟩
    simpa only [mem_closedBall_zero_iff, norm_smul, one_mul, norm_star] using
      (NNReal.le_inv_iff_mul_le ha.ne').1 (one_mul ‖a‖₊⁻¹ ▸ hk₂.le : ‖k‖₊ ≤ ‖a‖₊⁻¹)
    simp only [map_smul, nnnorm_smul, mul_apply', mul_smul_comm, CstarRing.nnnorm_self_mul_star]
    rwa [← NNReal.div_lt_iff (mul_pos ha ha).ne', div_eq_mul_inv, mul_inv, ← mul_assoc]

section CStarProperty

variable [StarRing 𝕜] [CstarRing 𝕜] [StarModule 𝕜 E]
variable {E}

/-- This is the key lemma used to establish the instance `Unitization.instCstarRing`
(i.e., proving that the norm on `Unitization 𝕜 E` satisfies the C⋆-property). We split this one
out so that declaring the `CstarRing` instance doesn't time out. -/
theorem Unitization.norm_splitMul_snd_sq (x : Unitization 𝕜 E) :
    ‖(Unitization.splitMul 𝕜 E x).snd‖ ^ 2 ≤ ‖(Unitization.splitMul 𝕜 E (star x * x)).snd‖ := by
  /- The key idea is that we can use `sSup_closed_unit_ball_eq_norm` to make this about
  applying this linear map to elements of norm at most one. There is a bit of `sqrt` and `sq`
  shuffling that needs to occur, which is primarily just an annoyance. -/
  refine (Real.le_sqrt (norm_nonneg _) (norm_nonneg _)).mp ?_
  simp only [Unitization.splitMul_apply]
  rw [← sSup_closed_unit_ball_eq_norm]
  refine csSup_le ((Metric.nonempty_closedBall.2 zero_le_one).image _) ?_
  rintro - ⟨b, hb, rfl⟩
  simp only
  -- rewrite to a more convenient form; this is where we use the C⋆-property
  rw [← Real.sqrt_sq (norm_nonneg _), Real.sqrt_le_sqrt_iff (norm_nonneg _), sq,
    ← CstarRing.norm_star_mul_self, ContinuousLinearMap.add_apply, star_add, mul_apply',
    Algebra.algebraMap_eq_smul_one, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.one_apply, star_mul, star_smul, add_mul, smul_mul_assoc, ← mul_smul_comm,
    mul_assoc, ← mul_add, ← sSup_closed_unit_ball_eq_norm]
  refine (norm_mul_le _ _).trans ?_
  calc
    _ ≤ ‖star x.fst • (x.fst • b + x.snd * b) + star x.snd * (x.fst • b + x.snd * b)‖ := by
      nth_rewrite 2 [← one_mul ‖_ + _‖]
      gcongr
      exact (norm_star b).symm ▸ mem_closedBall_zero_iff.1 hb
    _ ≤ sSup (_ '' Metric.closedBall 0 1) := le_csSup ?_ ⟨b, hb, ?_⟩
  -- now we just check the side conditions for `le_csSup`. There is nothing of interest here.
  refine ⟨‖(star x * x).fst‖ + ‖(star x * x).snd‖, ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  refine (norm_add_le _ _).trans ?_
  gcongr
  rw [Algebra.algebraMap_eq_smul_one]
  refine (norm_smul _ _).trans_le ?_
  simpa only [mul_one] using
    mul_le_mul_of_nonneg_left (mem_closedBall_zero_iff.1 hy) (norm_nonneg (star x * x).fst)
  exact (unit_le_opNorm _ y <| mem_closedBall_zero_iff.1 hy).trans (opNorm_mul_apply_le _ _ _)
  simp only [ContinuousLinearMap.add_apply, mul_apply', Unitization.snd_star, Unitization.snd_mul,
    Unitization.fst_mul, Unitization.fst_star, Algebra.algebraMap_eq_smul_one, smul_apply,
    one_apply, smul_add, mul_add, add_mul]
  simp only [smul_smul, smul_mul_assoc, ← add_assoc, ← mul_assoc, mul_smul_comm]

variable {𝕜}

/-- The norm on `Unitization 𝕜 E` satisfies the C⋆-property -/
instance Unitization.instCstarRing : CstarRing (Unitization 𝕜 E) where
  norm_mul_self_le x := by
    -- rewrite both sides as a `⊔`
    simp only [Unitization.norm_def, Prod.norm_def, ← sup_eq_max]
    -- Show that `(Unitization.splitMul 𝕜 E x).snd` satisifes the C⋆-property, in two stages:
    have h₁ : ∀ x : Unitization 𝕜 E,
        ‖(Unitization.splitMul 𝕜 E x).snd‖ ≤ ‖(Unitization.splitMul 𝕜 E (star x)).snd‖ := by
      simp only [add_zero, Unitization.splitMul_apply, Unitization.snd_star, Unitization.fst_star]
      intro x
      /- split based on whether the term inside the norm is zero or not. If so, it's trivial.
      If not, then apply `norm_splitMul_snd_sq` and cancel one copy of the norm -/
      by_cases h : algebraMap 𝕜 (E →L[𝕜] E) x.fst + mul 𝕜 E x.snd = 0
      simp only [h, norm_zero, norm_le_zero_iff]
      exact norm_nonneg _
      have : ‖(Unitization.splitMul 𝕜 E x).snd‖ ^ 2 ≤
        ‖(Unitization.splitMul 𝕜 E (star x)).snd‖ * ‖(Unitization.splitMul 𝕜 E x).snd‖ :=
        (norm_splitMul_snd_sq 𝕜 x).trans <| by
          rw [map_mul, Prod.snd_mul]
          exact norm_mul_le _ _
      rw [sq] at this
      rw [← Ne, ← norm_pos_iff] at h
      simp only [add_zero, Unitization.splitMul_apply, Unitization.snd_star,
        Unitization.fst_star, star_star] at this
      exact (mul_le_mul_right h).mp this
    -- in this step we make use of the key lemma `norm_splitMul_snd_sq`
    have h₂ : ‖(Unitization.splitMul 𝕜 E (star x * x)).snd‖
        = ‖(Unitization.splitMul 𝕜 E x).snd‖ ^ 2 := by
      refine le_antisymm ?_ (norm_splitMul_snd_sq 𝕜 x)
      rw [map_mul, Prod.snd_mul]
      exact (norm_mul_le _ _).trans <| by
        rw [sq]
        gcongr
        simpa only [star_star] using h₁ (star x)
    -- Show that `(Unitization.splitMul 𝕜 E x).fst` satisfies the C⋆-property
    have h₃ : ‖(Unitization.splitMul 𝕜 E (star x * x)).fst‖
        = ‖(Unitization.splitMul 𝕜 E x).fst‖ ^ 2 := by
      simp only [Unitization.splitMul_apply, Unitization.fst_mul, Unitization.fst_star, add_zero,
        norm_mul, norm_star, sq]
    rw [h₂, h₃]
    /- use the definition of the norm, and split into cases based on whether the norm in the first
    coordinate is bigger or smaller than the norm in the second coordinate. -/
    by_cases h : ‖(Unitization.splitMul 𝕜 E x).fst‖ ≤ ‖(Unitization.splitMul 𝕜 E x).snd‖
    rw [sq, sq, sup_eq_right.mpr h, sup_eq_right.mpr (mul_self_le_mul_self (norm_nonneg _) h)]
    replace h := (not_le.mp h).le
    rw [sq, sq, sup_eq_left.mpr h, sup_eq_left.mpr (mul_self_le_mul_self (norm_nonneg _) h)]

end CStarProperty
