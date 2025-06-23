import Mathlib.Tactic.Have
/-
Copyright (c) 2022 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Positive operators

In this file we define positive operators in a Hilbert space. We follow Bourbaki's choice
of requiring self adjointness in the definition.

## Main definitions

* `IsPositive` : a continuous linear map is positive if it is self adjoint and
  `∀ x, 0 ≤ re ⟪T x, x⟫`

## Main statements

* `ContinuousLinearMap.IsPositive.conj_adjoint` : if `T : E →L[𝕜] E` is positive,
  then for any `S : E →L[𝕜] F`, `S ∘L T ∘L S†` is also positive.
* `ContinuousLinearMap.isPositive_iff_complex` : in a ***complex*** Hilbert space,
  checking that `⟪T x, x⟫` is a nonnegative real number for all `x` suffices to prove that
  `T` is positive

## References

* [Bourbaki, *Topological Vector Spaces*][bourbaki1987]

## Tags

Positive operator
-/


open InnerProductSpace RCLike ContinuousLinearMap

open scoped InnerProduct ComplexConjugate

namespace ContinuousLinearMap

variable {𝕜 E F : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [NormedAddCommGroup F]
variable [InnerProductSpace 𝕜 E] [InnerProductSpace 𝕜 F]
variable [CompleteSpace E] [CompleteSpace F]

local notation "⟪" x ", " y "⟫" => @inner 𝕜 _ _ x y

/-- A continuous linear endomorphism `T` of a Hilbert space is **positive** if it is self adjoint
  and `∀ x, 0 ≤ re ⟪T x, x⟫`. -/
def IsPositive (T : E →L[𝕜] E) : Prop :=
  IsSelfAdjoint T ∧ ∀ x, 0 ≤ T.reApplyInnerSelf x

theorem IsPositive.isSelfAdjoint {T : E →L[𝕜] E} (hT : IsPositive T) : IsSelfAdjoint T :=
  hT.1

theorem IsPositive.inner_nonneg_left {T : E →L[𝕜] E} (hT : IsPositive T) (x : E) :
    0 ≤ re ⟪T x, x⟫ :=
  hT.2 x

theorem IsPositive.inner_nonneg_right {T : E →L[𝕜] E} (hT : IsPositive T) (x : E) :
    0 ≤ re ⟪x, T x⟫ := by rw [inner_re_symm]; exact hT.inner_nonneg_left x

theorem isPositive_zero : IsPositive (0 : E →L[𝕜] E) := by
  refine ⟨.zero _, fun x => ?_⟩
  change 0 ≤ re ⟪_, _⟫
  rw [zero_apply, inner_zero_left, ZeroHomClass.map_zero]

theorem isPositive_one : IsPositive (1 : E →L[𝕜] E) :=
  ⟨.one _, fun _ => inner_self_nonneg⟩

theorem IsPositive.add {T S : E →L[𝕜] E} (hT : T.IsPositive) (hS : S.IsPositive) :
    (T + S).IsPositive := by
  refine ⟨hT.isSelfAdjoint.add hS.isSelfAdjoint, fun x => ?_⟩
  rw [reApplyInnerSelf, add_apply, inner_add_left, map_add]
  exact add_nonneg (hT.inner_nonneg_left x) (hS.inner_nonneg_left x)

theorem IsPositive.conj_adjoint {T : E →L[𝕜] E} (hT : T.IsPositive) (S : E →L[𝕜] F) :
    (S ∘L T ∘L S†).IsPositive := by
  refine ⟨hT.isSelfAdjoint.conj_adjoint S, fun x => ?_⟩
  rw [reApplyInnerSelf, comp_apply, ← adjoint_inner_right]
  exact hT.inner_nonneg_left _

theorem IsPositive.adjoint_conj {T : E →L[𝕜] E} (hT : T.IsPositive) (S : F →L[𝕜] E) :
    (S† ∘L T ∘L S).IsPositive := by
  convert hT.conj_adjoint (S†)
  rw [adjoint_adjoint]

theorem IsPositive.conj_orthogonalProjection (U : Submodule 𝕜 E) {T : E →L[𝕜] E} (hT : T.IsPositive)
    [CompleteSpace U] :
    (U.subtypeL ∘L
        orthogonalProjection U ∘L T ∘L U.subtypeL ∘L orthogonalProjection U).IsPositive := by
  have := hT.conj_adjoint (U.subtypeL ∘L orthogonalProjection U)
  rwa [(orthogonalProjection_isSelfAdjoint U).adjoint_eq] at this

theorem IsPositive.orthogonalProjection_comp {T : E →L[𝕜] E} (hT : T.IsPositive) (U : Submodule 𝕜 E)
    [CompleteSpace U] : (orthogonalProjection U ∘L T ∘L U.subtypeL).IsPositive := by
  have := hT.conj_adjoint (orthogonalProjection U : E →L[𝕜] U)
  rwa [U.adjoint_orthogonalProjection] at this

section Complex

variable {E' : Type*} [NormedAddCommGroup E'] [InnerProductSpace ℂ E'] [CompleteSpace E']

theorem isPositive_iff_complex (T : E' →L[ℂ] E') :
    IsPositive T ↔ ∀ x, (re ⟪T x, x⟫_ℂ : ℂ) = ⟪T x, x⟫_ℂ ∧ 0 ≤ re ⟪T x, x⟫_ℂ := by
  simp_rw [IsPositive, forall_and, isSelfAdjoint_iff_isSymmetric,
    LinearMap.isSymmetric_iff_inner_map_self_real, conj_eq_iff_re]
  rfl

end Complex

section PartialOrder

/-- The (Loewner) partial order on continuous linear maps on a Hilbert space determined by
`f ≤ g` if and only if `g - f` is a positive linear map (in the sense of
`ContinuousLinearMap.IsPositive`). With this partial order, the continuous linear maps form a
`StarOrderedRing`. -/
instance instLoewnerPartialOrder : PartialOrder (E →L[𝕜] E) where
  le f g := (g - f).IsPositive
  le_refl _ := by simpa using isPositive_zero
  le_trans _ _ _ h₁ h₂ := by simpa using h₁.add h₂
  le_antisymm f₁ f₂ h₁ h₂ := by
    rw [← sub_eq_zero]
    have h_isSymm := isSelfAdjoint_iff_isSymmetric.mp h₂.isSelfAdjoint
    exact_mod_cast h_isSymm.inner_map_self_eq_zero.mp fun x ↦ by
      apply RCLike.ext
      rw [map_zero]
      apply le_antisymm
      rw [← neg_nonneg, ← map_neg, ← inner_neg_left]
      simpa using h₁.inner_nonneg_left _
      exact h₂.inner_nonneg_left _
      rw [coe_sub, LinearMap.sub_apply, coe_coe, coe_coe, map_zero, ← sub_apply,
        ← h_isSymm.coe_reApplyInnerSelf_apply (T := f₁ - f₂) x, RCLike.ofReal_im]

lemma le_def (f g : E →L[𝕜] E) : f ≤ g ↔ (g - f).IsPositive := Iff.rfl

lemma nonneg_iff_isPositive (f : E →L[𝕜] E) : 0 ≤ f ↔ f.IsPositive := by
  simpa using le_def 0 f

end PartialOrder

end ContinuousLinearMap
