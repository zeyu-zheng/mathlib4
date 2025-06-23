import Mathlib.Tactic.Have
/-
Copyright (c) 2022 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
import Mathlib.Topology.Algebra.Module.WeakDual
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.LocallyConvex.WithSeminorms

/-!
# Weak Dual in Topological Vector Spaces

We prove that the weak topology induced by a bilinear form `B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜` is locally
convex and we explicitly give a neighborhood basis in terms of the family of seminorms
`fun x => ‖B x y‖` for `y : F`.

## Main definitions

* `LinearMap.toSeminorm`: turn a linear form `f : E →ₗ[𝕜] 𝕜` into a seminorm `fun x => ‖f x‖`.
* `LinearMap.toSeminormFamily`: turn a bilinear form `B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜` into a map
`F → Seminorm 𝕜 E`.

## Main statements

* `LinearMap.hasBasis_weakBilin`: the seminorm balls of `B.toSeminormFamily` form a
neighborhood basis of `0` in the weak topology.
* `LinearMap.toSeminormFamily.withSeminorms`: the topology of a weak space is induced by the
family of seminorms `B.toSeminormFamily`.
* `WeakBilin.locallyConvexSpace`: a space endowed with a weak topology is locally convex.

## References

* [Bourbaki, *Topological Vector Spaces*][bourbaki1987]

## Tags

weak dual, seminorm
-/


variable {𝕜 E F ι : Type*}

open Topology

section BilinForm

namespace LinearMap

variable [NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E] [AddCommGroup F] [Module 𝕜 F]

/-- Construct a seminorm from a linear form `f : E →ₗ[𝕜] 𝕜` over a normed field `𝕜` by
`fun x => ‖f x‖` -/
def toSeminorm (f : E →ₗ[𝕜] 𝕜) : Seminorm 𝕜 E :=
  (normSeminorm 𝕜 𝕜).comp f

theorem coe_toSeminorm {f : E →ₗ[𝕜] 𝕜} : ⇑f.toSeminorm = fun x => ‖f x‖ :=
  rfl

@[simp]
theorem toSeminorm_apply {f : E →ₗ[𝕜] 𝕜} {x : E} : f.toSeminorm x = ‖f x‖ :=
  rfl

theorem toSeminorm_ball_zero {f : E →ₗ[𝕜] 𝕜} {r : ℝ} :
    Seminorm.ball f.toSeminorm 0 r = { x : E | ‖f x‖ < r } := by
  simp only [Seminorm.ball_zero_eq, toSeminorm_apply]

theorem toSeminorm_comp (f : F →ₗ[𝕜] 𝕜) (g : E →ₗ[𝕜] F) :
    f.toSeminorm.comp g = (f.comp g).toSeminorm := by
  ext
  simp only [Seminorm.comp_apply, toSeminorm_apply, coe_comp, Function.comp_apply]

/-- Construct a family of seminorms from a bilinear form. -/
def toSeminormFamily (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) : SeminormFamily 𝕜 E F := fun y =>
  (B.flip y).toSeminorm

@[simp]
theorem toSeminormFamily_apply {B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜} {x y} : (B.toSeminormFamily y) x = ‖B x y‖ :=
  rfl

end LinearMap

end BilinForm

section Topology

variable [NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E] [AddCommGroup F] [Module 𝕜 F]
variable [Nonempty ι]
variable {B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜}

theorem LinearMap.hasBasis_weakBilin (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) :
    (𝓝 (0 : WeakBilin B)).HasBasis B.toSeminormFamily.basisSets _root_.id := by
  let p := B.toSeminormFamily
  rw [nhds_induced, nhds_pi]
  simp only [map_zero, LinearMap.zero_apply]
  have h := @Metric.nhds_basis_ball 𝕜 _ 0
  have h' := Filter.hasBasis_pi fun _ : F => h
  have h'' := Filter.HasBasis.comap (fun x y => B x y) h'
  refine h''.to_hasBasis ?_ ?_
  rintro (U : Set F × (F → ℝ)) hU
  cases' hU with hU₁ hU₂
  simp only [_root_.id]
  let U' := hU₁.toFinset
  by_cases hU₃ : U.fst.Nonempty
  have hU₃' : U'.Nonempty := hU₁.toFinset_nonempty.mpr hU₃
  refine ⟨(U'.sup p).ball 0 <| U'.inf' hU₃' U.snd, p.basisSets_mem _ <|
    (Finset.lt_inf'_iff _).2 fun y hy => hU₂ y <| hU₁.mem_toFinset.mp hy, fun x hx y hy => ?_⟩
  simp only [Set.mem_preimage, Set.mem_pi, mem_ball_zero_iff]
  rw [Seminorm.mem_ball_zero] at hx
  rw [← LinearMap.toSeminormFamily_apply]
  have hyU' : y ∈ U' := (Set.Finite.mem_toFinset hU₁).mpr hy
  have hp : p y ≤ U'.sup p := Finset.le_sup hyU'
  refine lt_of_le_of_lt (hp x) (lt_of_lt_of_le hx ?_)
  exact Finset.inf'_le _ hyU'
  rw [Set.not_nonempty_iff_eq_empty.mp hU₃]
  simp only [Set.empty_pi, Set.preimage_univ, Set.subset_univ, and_true_iff]
  exact Exists.intro ((p 0).ball 0 1) (p.basisSets_singleton_mem 0 one_pos)
  rintro U (hU : U ∈ p.basisSets)
  rw [SeminormFamily.basisSets_iff] at hU
  rcases hU with ⟨s, r, hr, hU⟩
  rw [hU]
  refine ⟨(s, fun _ => r), ⟨by simp only [s.finite_toSet], fun y _ => hr⟩, fun x hx => ?_⟩
  simp only [Set.mem_preimage, Set.mem_pi, Finset.mem_coe, mem_ball_zero_iff] at hx
  simp only [_root_.id, Seminorm.mem_ball, sub_zero]
  refine Seminorm.finset_sup_apply_lt hr fun y hy => ?_
  rw [LinearMap.toSeminormFamily_apply]
  exact hx y hy

theorem LinearMap.weakBilin_withSeminorms (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) :
    WithSeminorms (LinearMap.toSeminormFamily B : F → Seminorm 𝕜 (WeakBilin B)) :=
  SeminormFamily.withSeminorms_of_hasBasis _ B.hasBasis_weakBilin

end Topology

section LocallyConvex

variable [NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E] [AddCommGroup F] [Module 𝕜 F]
variable [Nonempty ι] [NormedSpace ℝ 𝕜] [Module ℝ E] [IsScalarTower ℝ 𝕜 E]

instance WeakBilin.locallyConvexSpace {B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜} :
    LocallyConvexSpace ℝ (WeakBilin B) :=
  B.weakBilin_withSeminorms.toLocallyConvexSpace

end LocallyConvex
