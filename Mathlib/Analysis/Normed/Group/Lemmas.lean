/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Johannes Hölzl, Yaël Dillies
-/
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Normed.Group.Seminorm
import Mathlib.Order.LiminfLimsup
import Mathlib.Topology.Instances.NNReal
import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.MetricSpace.Algebra
import Mathlib.Topology.MetricSpace.IsometricSMul
import Mathlib.Topology.Sequences

#align_import analysis.normed.group.basic from "leanprover-community/mathlib"@"41bef4ae1254365bc190aee63b947674d2977f01"

/-!
# Normed (semi)groups

In this file we define 10 classes:

* `Norm`, `NNNorm`: auxiliary classes endowing a type `α` with a function `norm : α → ℝ`
  (notation: `‖x‖`) and `nnnorm : α → ℝ≥0` (notation: `‖x‖₊`), respectively;
* `Seminormed...Group`: A seminormed (additive) (commutative) group is an (additive) (commutative)
  group with a norm and a compatible pseudometric space structure:
  `∀ x y, dist x y = ‖x / y‖` or `∀ x y, dist x y = ‖x - y‖`, depending on the group operation.
* `Normed...Group`: A normed (additive) (commutative) group is an (additive) (commutative) group
  with a norm and a compatible metric space structure.

We also prove basic properties of (semi)normed groups and provide some instances.

## TODO
This file is huge; move material into separate files,
such as `Mathlib/Analysis/Normed/Group/Lemmas.lean`.

## Notes

The current convention `dist x y = ‖x - y‖` means that the distance is invariant under right
addition, but actions in mathlib are usually from the left. This means we might want to change it to
`dist x y = ‖-x + y‖`.

The normed group hierarchy would lend itself well to a mixin design (that is, having
`SeminormedGroup` and `SeminormedAddGroup` not extend `Group` and `AddGroup`), but we choose not
to for performance concerns.

## Tags

normed group
-/


variable {𝓕 𝕜 α ι κ E F G : Type*}

open Filter Function Metric Bornology

open ENNReal Filter NNReal Uniformity Pointwise Topology

instance PUnit.normedAddCommGroup : NormedAddCommGroup PUnit where
  norm := Function.const _ 0
  dist_eq _ _ := rfl

@[simp]
theorem PUnit.norm_eq_zero (r : PUnit) : ‖r‖ = 0 :=
  rfl
#align punit.norm_eq_zero PUnit.norm_eq_zero

section SeminormedGroup

variable [SeminormedGroup E] [SeminormedGroup F] [SeminormedGroup G] {s : Set E}
  {a a₁ a₂ b b₁ b₂ : E} {r r₁ r₂ : ℝ}

@[to_additive]
instance NormedGroup.to_isometricSMul_right : IsometricSMul Eᵐᵒᵖ E :=
  ⟨fun a => Isometry.of_dist_eq fun b c => by simp [dist_eq_norm_div]⟩
#align normed_group.to_has_isometric_smul_right NormedGroup.to_isometricSMul_right
#align normed_add_group.to_has_isometric_vadd_right NormedAddGroup.to_isometricVAdd_right

@[to_additive]
theorem Isometry.norm_map_of_map_one {f : E → F} (hi : Isometry f) (h₁ : f 1 = 1) (x : E) :
    ‖f x‖ = ‖x‖ := by rw [← dist_one_right, ← h₁, hi.dist_eq, dist_one_right]
#align isometry.norm_map_of_map_one Isometry.norm_map_of_map_one
#align isometry.norm_map_of_map_zero Isometry.norm_map_of_map_zero

@[to_additive (attr := simp)]
theorem dist_mul_self_right (a b : E) : dist b (a * b) = ‖a‖ := by
  rw [← dist_one_left, ← dist_mul_right 1 a b, one_mul]
#align dist_mul_self_right dist_mul_self_right
#align dist_add_self_right dist_add_self_right

@[to_additive (attr := simp)]
theorem dist_mul_self_left (a b : E) : dist (a * b) b = ‖a‖ := by
  rw [dist_comm, dist_mul_self_right]
#align dist_mul_self_left dist_mul_self_left
#align dist_add_self_left dist_add_self_left

@[to_additive (attr := simp)]
theorem dist_div_eq_dist_mul_left (a b c : E) : dist (a / b) c = dist a (c * b) := by
  rw [← dist_mul_right _ _ b, div_mul_cancel]
#align dist_div_eq_dist_mul_left dist_div_eq_dist_mul_left
#align dist_sub_eq_dist_add_left dist_sub_eq_dist_add_left

@[to_additive (attr := simp)]
theorem dist_div_eq_dist_mul_right (a b c : E) : dist a (b / c) = dist (a * c) b := by
  rw [← dist_mul_right _ _ c, div_mul_cancel]
#align dist_div_eq_dist_mul_right dist_div_eq_dist_mul_right
#align dist_sub_eq_dist_add_right dist_sub_eq_dist_add_right

@[to_additive (attr := simp)]
lemma Filter.inv_cobounded : (cobounded E)⁻¹ = cobounded E := by
  simp only [← comap_norm_atTop', ← Filter.comap_inv, comap_comap, (· ∘ ·), norm_inv']

/-- In a (semi)normed group, inversion `x ↦ x⁻¹` tends to infinity at infinity. -/
@[to_additive "In a (semi)normed group, negation `x ↦ -x` tends to infinity at infinity."]
theorem Filter.tendsto_inv_cobounded : Tendsto Inv.inv (cobounded E) (cobounded E) :=
  inv_cobounded.le
#align filter.tendsto_inv_cobounded Filter.tendsto_inv_cobounded
#align filter.tendsto_neg_cobounded Filter.tendsto_neg_cobounded

open Finset

variable [FunLike 𝓕 E F]

/-- A homomorphism `f` of seminormed groups is Lipschitz, if there exists a constant `C` such that
for all `x`, one has `‖f x‖ ≤ C * ‖x‖`. The analogous condition for a linear map of
(semi)normed spaces is in `Mathlib/Analysis/NormedSpace/OperatorNorm.lean`. -/
@[to_additive "A homomorphism `f` of seminormed groups is Lipschitz, if there exists a constant
`C` such that for all `x`, one has `‖f x‖ ≤ C * ‖x‖`. The analogous condition for a linear map of
(semi)normed spaces is in `Mathlib/Analysis/NormedSpace/OperatorNorm.lean`."]
theorem MonoidHomClass.lipschitz_of_bound [MonoidHomClass 𝓕 E F] (f : 𝓕) (C : ℝ)
    (h : ∀ x, ‖f x‖ ≤ C * ‖x‖) : LipschitzWith (Real.toNNReal C) f :=
  LipschitzWith.of_dist_le' fun x y => by simpa only [dist_eq_norm_div, map_div] using h (x / y)
#align monoid_hom_class.lipschitz_of_bound MonoidHomClass.lipschitz_of_bound
#align add_monoid_hom_class.lipschitz_of_bound AddMonoidHomClass.lipschitz_of_bound

@[to_additive]
theorem lipschitzOnWith_iff_norm_div_le {f : E → F} {C : ℝ≥0} :
    LipschitzOnWith C f s ↔ ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → ‖f x / f y‖ ≤ C * ‖x / y‖ := by
  simp only [lipschitzOnWith_iff_dist_le_mul, dist_eq_norm_div]
#align lipschitz_on_with_iff_norm_div_le lipschitzOnWith_iff_norm_div_le
#align lipschitz_on_with_iff_norm_sub_le lipschitzOnWith_iff_norm_sub_le

alias ⟨LipschitzOnWith.norm_div_le, _⟩ := lipschitzOnWith_iff_norm_div_le
#align lipschitz_on_with.norm_div_le LipschitzOnWith.norm_div_le

attribute [to_additive] LipschitzOnWith.norm_div_le

@[to_additive]
theorem LipschitzOnWith.norm_div_le_of_le {f : E → F} {C : ℝ≥0} (h : LipschitzOnWith C f s)
    (ha : a ∈ s) (hb : b ∈ s) (hr : ‖a / b‖ ≤ r) : ‖f a / f b‖ ≤ C * r :=
  (h.norm_div_le ha hb).trans <| by gcongr
#align lipschitz_on_with.norm_div_le_of_le LipschitzOnWith.norm_div_le_of_le
#align lipschitz_on_with.norm_sub_le_of_le LipschitzOnWith.norm_sub_le_of_le

@[to_additive]
theorem lipschitzWith_iff_norm_div_le {f : E → F} {C : ℝ≥0} :
    LipschitzWith C f ↔ ∀ x y, ‖f x / f y‖ ≤ C * ‖x / y‖ := by
  simp only [lipschitzWith_iff_dist_le_mul, dist_eq_norm_div]
#align lipschitz_with_iff_norm_div_le lipschitzWith_iff_norm_div_le
#align lipschitz_with_iff_norm_sub_le lipschitzWith_iff_norm_sub_le

alias ⟨LipschitzWith.norm_div_le, _⟩ := lipschitzWith_iff_norm_div_le
#align lipschitz_with.norm_div_le LipschitzWith.norm_div_le

attribute [to_additive] LipschitzWith.norm_div_le

@[to_additive]
theorem LipschitzWith.norm_div_le_of_le {f : E → F} {C : ℝ≥0} (h : LipschitzWith C f)
    (hr : ‖a / b‖ ≤ r) : ‖f a / f b‖ ≤ C * r :=
  (h.norm_div_le _ _).trans <| by gcongr
#align lipschitz_with.norm_div_le_of_le LipschitzWith.norm_div_le_of_le
#align lipschitz_with.norm_sub_le_of_le LipschitzWith.norm_sub_le_of_le

/-- A homomorphism `f` of seminormed groups is continuous, if there exists a constant `C` such that
for all `x`, one has `‖f x‖ ≤ C * ‖x‖`. -/
@[to_additive "A homomorphism `f` of seminormed groups is continuous, if there exists a constant `C`
such that for all `x`, one has `‖f x‖ ≤ C * ‖x‖`"]
theorem MonoidHomClass.continuous_of_bound [MonoidHomClass 𝓕 E F] (f : 𝓕) (C : ℝ)
    (h : ∀ x, ‖f x‖ ≤ C * ‖x‖) : Continuous f :=
  (MonoidHomClass.lipschitz_of_bound f C h).continuous
#align monoid_hom_class.continuous_of_bound MonoidHomClass.continuous_of_bound
#align add_monoid_hom_class.continuous_of_bound AddMonoidHomClass.continuous_of_bound

@[to_additive]
theorem MonoidHomClass.uniformContinuous_of_bound [MonoidHomClass 𝓕 E F] (f : 𝓕) (C : ℝ)
    (h : ∀ x, ‖f x‖ ≤ C * ‖x‖) : UniformContinuous f :=
  (MonoidHomClass.lipschitz_of_bound f C h).uniformContinuous
#align monoid_hom_class.uniform_continuous_of_bound MonoidHomClass.uniformContinuous_of_bound
#align add_monoid_hom_class.uniform_continuous_of_bound AddMonoidHomClass.uniformContinuous_of_bound

@[to_additive]
theorem MonoidHomClass.isometry_iff_norm [MonoidHomClass 𝓕 E F] (f : 𝓕) :
    Isometry f ↔ ∀ x, ‖f x‖ = ‖x‖ := by
  simp only [isometry_iff_dist_eq, dist_eq_norm_div, ← map_div]
  refine ⟨fun h x => ?_, fun h x y => h _⟩
  simpa using h x 1
#align monoid_hom_class.isometry_iff_norm MonoidHomClass.isometry_iff_norm
#align add_monoid_hom_class.isometry_iff_norm AddMonoidHomClass.isometry_iff_norm

alias ⟨_, MonoidHomClass.isometry_of_norm⟩ := MonoidHomClass.isometry_iff_norm
#align monoid_hom_class.isometry_of_norm MonoidHomClass.isometry_of_norm

attribute [to_additive] MonoidHomClass.isometry_of_norm

section NNNorm

@[to_additive]
theorem MonoidHomClass.lipschitz_of_bound_nnnorm [MonoidHomClass 𝓕 E F] (f : 𝓕) (C : ℝ≥0)
    (h : ∀ x, ‖f x‖₊ ≤ C * ‖x‖₊) : LipschitzWith C f :=
  @Real.toNNReal_coe C ▸ MonoidHomClass.lipschitz_of_bound f C h
#align monoid_hom_class.lipschitz_of_bound_nnnorm MonoidHomClass.lipschitz_of_bound_nnnorm
#align add_monoid_hom_class.lipschitz_of_bound_nnnorm AddMonoidHomClass.lipschitz_of_bound_nnnorm

@[to_additive]
theorem MonoidHomClass.antilipschitz_of_bound [MonoidHomClass 𝓕 E F] (f : 𝓕) {K : ℝ≥0}
    (h : ∀ x, ‖x‖ ≤ K * ‖f x‖) : AntilipschitzWith K f :=
  AntilipschitzWith.of_le_mul_dist fun x y => by
    simpa only [dist_eq_norm_div, map_div] using h (x / y)
#align monoid_hom_class.antilipschitz_of_bound MonoidHomClass.antilipschitz_of_bound
#align add_monoid_hom_class.antilipschitz_of_bound AddMonoidHomClass.antilipschitz_of_bound

@[to_additive LipschitzWith.norm_le_mul]
theorem LipschitzWith.norm_le_mul' {f : E → F} {K : ℝ≥0} (h : LipschitzWith K f) (hf : f 1 = 1)
    (x) : ‖f x‖ ≤ K * ‖x‖ := by simpa only [dist_one_right, hf] using h.dist_le_mul x 1
#align lipschitz_with.norm_le_mul' LipschitzWith.norm_le_mul'
#align lipschitz_with.norm_le_mul LipschitzWith.norm_le_mul

@[to_additive LipschitzWith.nnorm_le_mul]
theorem LipschitzWith.nnorm_le_mul' {f : E → F} {K : ℝ≥0} (h : LipschitzWith K f) (hf : f 1 = 1)
    (x) : ‖f x‖₊ ≤ K * ‖x‖₊ :=
  h.norm_le_mul' hf x
#align lipschitz_with.nnorm_le_mul' LipschitzWith.nnorm_le_mul'
#align lipschitz_with.nnorm_le_mul LipschitzWith.nnorm_le_mul

@[to_additive AntilipschitzWith.le_mul_norm]
theorem AntilipschitzWith.le_mul_norm' {f : E → F} {K : ℝ≥0} (h : AntilipschitzWith K f)
    (hf : f 1 = 1) (x) : ‖x‖ ≤ K * ‖f x‖ := by
  simpa only [dist_one_right, hf] using h.le_mul_dist x 1
#align antilipschitz_with.le_mul_norm' AntilipschitzWith.le_mul_norm'
#align antilipschitz_with.le_mul_norm AntilipschitzWith.le_mul_norm

@[to_additive AntilipschitzWith.le_mul_nnnorm]
theorem AntilipschitzWith.le_mul_nnnorm' {f : E → F} {K : ℝ≥0} (h : AntilipschitzWith K f)
    (hf : f 1 = 1) (x) : ‖x‖₊ ≤ K * ‖f x‖₊ :=
  h.le_mul_norm' hf x
#align antilipschitz_with.le_mul_nnnorm' AntilipschitzWith.le_mul_nnnorm'
#align antilipschitz_with.le_mul_nnnorm AntilipschitzWith.le_mul_nnnorm

@[to_additive]
theorem OneHomClass.bound_of_antilipschitz [OneHomClass 𝓕 E F] (f : 𝓕) {K : ℝ≥0}
    (h : AntilipschitzWith K f) (x) : ‖x‖ ≤ K * ‖f x‖ :=
  h.le_mul_nnnorm' (map_one f) x
#align one_hom_class.bound_of_antilipschitz OneHomClass.bound_of_antilipschitz
#align zero_hom_class.bound_of_antilipschitz ZeroHomClass.bound_of_antilipschitz

@[to_additive]
theorem Isometry.nnnorm_map_of_map_one {f : E → F} (hi : Isometry f) (h₁ : f 1 = 1) (x : E) :
    ‖f x‖₊ = ‖x‖₊ :=
  Subtype.ext <| hi.norm_map_of_map_one h₁ x

end NNNorm

@[to_additive lipschitzWith_one_norm]
theorem lipschitzWith_one_norm' : LipschitzWith 1 (norm : E → ℝ) := by
  simpa only [dist_one_left] using LipschitzWith.dist_right (1 : E)
#align lipschitz_with_one_norm' lipschitzWith_one_norm'
#align lipschitz_with_one_norm lipschitzWith_one_norm

@[to_additive lipschitzWith_one_nnnorm]
theorem lipschitzWith_one_nnnorm' : LipschitzWith 1 (NNNorm.nnnorm : E → ℝ≥0) :=
  lipschitzWith_one_norm'
#align lipschitz_with_one_nnnorm' lipschitzWith_one_nnnorm'
#align lipschitz_with_one_nnnorm lipschitzWith_one_nnnorm

@[to_additive uniformContinuous_norm]
theorem uniformContinuous_norm' : UniformContinuous (norm : E → ℝ) :=
  lipschitzWith_one_norm'.uniformContinuous
#align uniform_continuous_norm' uniformContinuous_norm'
#align uniform_continuous_norm uniformContinuous_norm

@[to_additive uniformContinuous_nnnorm]
theorem uniformContinuous_nnnorm' : UniformContinuous fun a : E => ‖a‖₊ :=
  uniformContinuous_norm'.subtype_mk _
#align uniform_continuous_nnnorm' uniformContinuous_nnnorm'
#align uniform_continuous_nnnorm uniformContinuous_nnnorm

/-- A helper lemma used to prove that the (scalar or usual) product of a function that tends to one
and a bounded function tends to one. This lemma is formulated for any binary operation
`op : E → F → G` with an estimate `‖op x y‖ ≤ A * ‖x‖ * ‖y‖` for some constant A instead of
multiplication so that it can be applied to `(*)`, `flip (*)`, `(•)`, and `flip (•)`. -/
@[to_additive "A helper lemma used to prove that the (scalar or usual) product of a function that
tends to zero and a bounded function tends to zero. This lemma is formulated for any binary
operation `op : E → F → G` with an estimate `‖op x y‖ ≤ A * ‖x‖ * ‖y‖` for some constant A instead
of multiplication so that it can be applied to `(*)`, `flip (*)`, `(•)`, and `flip (•)`."]
theorem Filter.Tendsto.op_one_isBoundedUnder_le' {f : α → E} {g : α → F} {l : Filter α}
    (hf : Tendsto f l (𝓝 1)) (hg : IsBoundedUnder (· ≤ ·) l (Norm.norm ∘ g)) (op : E → F → G)
    (h_op : ∃ A, ∀ x y, ‖op x y‖ ≤ A * ‖x‖ * ‖y‖) : Tendsto (fun x => op (f x) (g x)) l (𝓝 1) := by
  cases' h_op with A h_op
  rcases hg with ⟨C, hC⟩; rw [eventually_map] at hC
  rw [NormedCommGroup.tendsto_nhds_one] at hf ⊢
  intro ε ε₀
  rcases exists_pos_mul_lt ε₀ (A * C) with ⟨δ, δ₀, hδ⟩
  filter_upwards [hf δ δ₀, hC] with i hf hg
  refine (h_op _ _).trans_lt ?_
  rcases le_total A 0 with hA | hA
  · exact (mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hA <| norm_nonneg' _) <|
      norm_nonneg' _).trans_lt ε₀
  calc
    A * ‖f i‖ * ‖g i‖ ≤ A * δ * C := by gcongr; exact hg
    _ = A * C * δ := mul_right_comm _ _ _
    _ < ε := hδ
#align filter.tendsto.op_one_is_bounded_under_le' Filter.Tendsto.op_one_isBoundedUnder_le'
#align filter.tendsto.op_zero_is_bounded_under_le' Filter.Tendsto.op_zero_isBoundedUnder_le'

/-- A helper lemma used to prove that the (scalar or usual) product of a function that tends to one
and a bounded function tends to one. This lemma is formulated for any binary operation
`op : E → F → G` with an estimate `‖op x y‖ ≤ ‖x‖ * ‖y‖` instead of multiplication so that it
can be applied to `(*)`, `flip (*)`, `(•)`, and `flip (•)`. -/
@[to_additive "A helper lemma used to prove that the (scalar or usual) product of a function that
tends to zero and a bounded function tends to zero. This lemma is formulated for any binary
operation `op : E → F → G` with an estimate `‖op x y‖ ≤ ‖x‖ * ‖y‖` instead of multiplication so
that it can be applied to `(*)`, `flip (*)`, `(•)`, and `flip (•)`."]
theorem Filter.Tendsto.op_one_isBoundedUnder_le {f : α → E} {g : α → F} {l : Filter α}
    (hf : Tendsto f l (𝓝 1)) (hg : IsBoundedUnder (· ≤ ·) l (Norm.norm ∘ g)) (op : E → F → G)
    (h_op : ∀ x y, ‖op x y‖ ≤ ‖x‖ * ‖y‖) : Tendsto (fun x => op (f x) (g x)) l (𝓝 1) :=
  hf.op_one_isBoundedUnder_le' hg op ⟨1, fun x y => (one_mul ‖x‖).symm ▸ h_op x y⟩
#align filter.tendsto.op_one_is_bounded_under_le Filter.Tendsto.op_one_isBoundedUnder_le
#align filter.tendsto.op_zero_is_bounded_under_le Filter.Tendsto.op_zero_isBoundedUnder_le

end SeminormedGroup

section SeminormedCommGroup

variable [SeminormedCommGroup E] [SeminormedCommGroup F] {a a₁ a₂ b b₁ b₂ : E} {r r₁ r₂ : ℝ}

@[to_additive]
instance NormedGroup.to_isometricSMul_left : IsometricSMul E E :=
  ⟨fun a => Isometry.of_dist_eq fun b c => by simp [dist_eq_norm_div]⟩
#align normed_group.to_has_isometric_smul_left NormedGroup.to_isometricSMul_left
#align normed_add_group.to_has_isometric_vadd_left NormedAddGroup.to_isometricVAdd_left

@[to_additive (attr := simp)]
theorem dist_self_mul_right (a b : E) : dist a (a * b) = ‖b‖ := by
  rw [← dist_one_left, ← dist_mul_left a 1 b, mul_one]
#align dist_self_mul_right dist_self_mul_right
#align dist_self_add_right dist_self_add_right

@[to_additive (attr := simp)]
theorem dist_self_mul_left (a b : E) : dist (a * b) a = ‖b‖ := by
  rw [dist_comm, dist_self_mul_right]
#align dist_self_mul_left dist_self_mul_left
#align dist_self_add_left dist_self_add_left

@[to_additive (attr := simp 1001)]
-- porting note (#10618): increase priority because `simp` can prove this
theorem dist_self_div_right (a b : E) : dist a (a / b) = ‖b‖ := by
  rw [div_eq_mul_inv, dist_self_mul_right, norm_inv']
#align dist_self_div_right dist_self_div_right
#align dist_self_sub_right dist_self_sub_right

@[to_additive (attr := simp 1001)]
-- porting note (#10618): increase priority because `simp` can prove this
theorem dist_self_div_left (a b : E) : dist (a / b) a = ‖b‖ := by
  rw [dist_comm, dist_self_div_right]
#align dist_self_div_left dist_self_div_left
#align dist_self_sub_left dist_self_sub_left

@[to_additive]
theorem dist_mul_mul_le (a₁ a₂ b₁ b₂ : E) : dist (a₁ * a₂) (b₁ * b₂) ≤ dist a₁ b₁ + dist a₂ b₂ := by
  simpa only [dist_mul_left, dist_mul_right] using dist_triangle (a₁ * a₂) (b₁ * a₂) (b₁ * b₂)
#align dist_mul_mul_le dist_mul_mul_le
#align dist_add_add_le dist_add_add_le

@[to_additive]
theorem dist_mul_mul_le_of_le (h₁ : dist a₁ b₁ ≤ r₁) (h₂ : dist a₂ b₂ ≤ r₂) :
    dist (a₁ * a₂) (b₁ * b₂) ≤ r₁ + r₂ :=
  (dist_mul_mul_le a₁ a₂ b₁ b₂).trans <| add_le_add h₁ h₂
#align dist_mul_mul_le_of_le dist_mul_mul_le_of_le
#align dist_add_add_le_of_le dist_add_add_le_of_le

@[to_additive]
theorem dist_div_div_le (a₁ a₂ b₁ b₂ : E) : dist (a₁ / a₂) (b₁ / b₂) ≤ dist a₁ b₁ + dist a₂ b₂ := by
  simpa only [div_eq_mul_inv, dist_inv_inv] using dist_mul_mul_le a₁ a₂⁻¹ b₁ b₂⁻¹
#align dist_div_div_le dist_div_div_le
#align dist_sub_sub_le dist_sub_sub_le

@[to_additive]
theorem dist_div_div_le_of_le (h₁ : dist a₁ b₁ ≤ r₁) (h₂ : dist a₂ b₂ ≤ r₂) :
    dist (a₁ / a₂) (b₁ / b₂) ≤ r₁ + r₂ :=
  (dist_div_div_le a₁ a₂ b₁ b₂).trans <| add_le_add h₁ h₂
#align dist_div_div_le_of_le dist_div_div_le_of_le
#align dist_sub_sub_le_of_le dist_sub_sub_le_of_le

@[to_additive]
theorem abs_dist_sub_le_dist_mul_mul (a₁ a₂ b₁ b₂ : E) :
    |dist a₁ b₁ - dist a₂ b₂| ≤ dist (a₁ * a₂) (b₁ * b₂) := by
  simpa only [dist_mul_left, dist_mul_right, dist_comm b₂] using
    abs_dist_sub_le (a₁ * a₂) (b₁ * b₂) (b₁ * a₂)
#align abs_dist_sub_le_dist_mul_mul abs_dist_sub_le_dist_mul_mul
#align abs_dist_sub_le_dist_add_add abs_dist_sub_le_dist_add_add

open Finset

@[to_additive]
theorem controlled_prod_of_mem_closure {s : Subgroup E} (hg : a ∈ closure (s : Set E)) {b : ℕ → ℝ}
    (b_pos : ∀ n, 0 < b n) :
    ∃ v : ℕ → E,
      Tendsto (fun n => ∏ i ∈ range (n + 1), v i) atTop (𝓝 a) ∧
        (∀ n, v n ∈ s) ∧ ‖v 0 / a‖ < b 0 ∧ ∀ n, 0 < n → ‖v n‖ < b n := by
  obtain ⟨u : ℕ → E, u_in : ∀ n, u n ∈ s, lim_u : Tendsto u atTop (𝓝 a)⟩ :=
    mem_closure_iff_seq_limit.mp hg
  obtain ⟨n₀, hn₀⟩ : ∃ n₀, ∀ n ≥ n₀, ‖u n / a‖ < b 0 :=
    haveI : { x | ‖x / a‖ < b 0 } ∈ 𝓝 a := by
      simp_rw [← dist_eq_norm_div]
      exact Metric.ball_mem_nhds _ (b_pos _)
    Filter.tendsto_atTop'.mp lim_u _ this
  set z : ℕ → E := fun n => u (n + n₀)
  have lim_z : Tendsto z atTop (𝓝 a) := lim_u.comp (tendsto_add_atTop_nat n₀)
  have mem_𝓤 : ∀ n, { p : E × E | ‖p.1 / p.2‖ < b (n + 1) } ∈ 𝓤 E := fun n => by
    simpa [← dist_eq_norm_div] using Metric.dist_mem_uniformity (b_pos <| n + 1)
  obtain ⟨φ : ℕ → ℕ, φ_extr : StrictMono φ, hφ : ∀ n, ‖z (φ <| n + 1) / z (φ n)‖ < b (n + 1)⟩ :=
    lim_z.cauchySeq.subseq_mem mem_𝓤
  set w : ℕ → E := z ∘ φ
  have hw : Tendsto w atTop (𝓝 a) := lim_z.comp φ_extr.tendsto_atTop
  set v : ℕ → E := fun i => if i = 0 then w 0 else w i / w (i - 1)
  refine ⟨v, Tendsto.congr (Finset.eq_prod_range_div' w) hw, ?_, hn₀ _ (n₀.le_add_left _), ?_⟩
  · rintro ⟨⟩
    · change w 0 ∈ s
      apply u_in
    · apply s.div_mem <;> apply u_in
  · intro l hl
    obtain ⟨k, rfl⟩ : ∃ k, l = k + 1 := Nat.exists_eq_succ_of_ne_zero hl.ne'
    apply hφ
#align controlled_prod_of_mem_closure controlled_prod_of_mem_closure
#align controlled_sum_of_mem_closure controlled_sum_of_mem_closure

@[to_additive]
theorem controlled_prod_of_mem_closure_range {j : E →* F} {b : F}
    (hb : b ∈ closure (j.range : Set F)) {f : ℕ → ℝ} (b_pos : ∀ n, 0 < f n) :
    ∃ a : ℕ → E,
      Tendsto (fun n => ∏ i ∈ range (n + 1), j (a i)) atTop (𝓝 b) ∧
        ‖j (a 0) / b‖ < f 0 ∧ ∀ n, 0 < n → ‖j (a n)‖ < f n := by
  obtain ⟨v, sum_v, v_in, hv₀, hv_pos⟩ := controlled_prod_of_mem_closure hb b_pos
  choose g hg using v_in
  exact
    ⟨g, by simpa [← hg] using sum_v, by simpa [hg 0] using hv₀,
      fun n hn => by simpa [hg] using hv_pos n hn⟩
#align controlled_prod_of_mem_closure_range controlled_prod_of_mem_closure_range
#align controlled_sum_of_mem_closure_range controlled_sum_of_mem_closure_range

@[to_additive]
theorem nndist_mul_mul_le (a₁ a₂ b₁ b₂ : E) :
    nndist (a₁ * a₂) (b₁ * b₂) ≤ nndist a₁ b₁ + nndist a₂ b₂ :=
  NNReal.coe_le_coe.1 <| dist_mul_mul_le a₁ a₂ b₁ b₂
#align nndist_mul_mul_le nndist_mul_mul_le
#align nndist_add_add_le nndist_add_add_le

@[to_additive]
theorem edist_mul_mul_le (a₁ a₂ b₁ b₂ : E) :
    edist (a₁ * a₂) (b₁ * b₂) ≤ edist a₁ b₁ + edist a₂ b₂ := by
  simp only [edist_nndist]
  norm_cast
  apply nndist_mul_mul_le
#align edist_mul_mul_le edist_mul_mul_le
#align edist_add_add_le edist_add_add_le

namespace Int

instance instNormedAddCommGroup : NormedAddCommGroup ℤ where
  norm n := ‖(n : ℝ)‖
  dist_eq m n := by simp only [Int.dist_eq, norm, Int.cast_sub]

@[norm_cast]
theorem norm_cast_real (m : ℤ) : ‖(m : ℝ)‖ = ‖m‖ :=
  rfl
#align int.norm_cast_real Int.norm_cast_real

theorem norm_eq_abs (n : ℤ) : ‖n‖ = |(n : ℝ)| :=
  rfl
#align int.norm_eq_abs Int.norm_eq_abs

@[simp]
theorem norm_natCast (n : ℕ) : ‖(n : ℤ)‖ = n := by simp [Int.norm_eq_abs]
#align int.norm_coe_nat Int.norm_natCast

@[deprecated (since := "2024-04-05")] alias norm_coe_nat := norm_natCast

theorem _root_.NNReal.natCast_natAbs (n : ℤ) : (n.natAbs : ℝ≥0) = ‖n‖₊ :=
  NNReal.eq <|
    calc
      ((n.natAbs : ℝ≥0) : ℝ) = (n.natAbs : ℤ) := by simp only [Int.cast_natCast, NNReal.coe_natCast]
      _ = |(n : ℝ)| := by simp only [Int.natCast_natAbs, Int.cast_abs]
      _ = ‖n‖ := (norm_eq_abs n).symm
#align nnreal.coe_nat_abs NNReal.natCast_natAbs

theorem abs_le_floor_nnreal_iff (z : ℤ) (c : ℝ≥0) : |z| ≤ ⌊c⌋₊ ↔ ‖z‖₊ ≤ c := by
  rw [Int.abs_eq_natAbs, Int.ofNat_le, Nat.le_floor_iff (zero_le c), NNReal.natCast_natAbs z]
#align int.abs_le_floor_nnreal_iff Int.abs_le_floor_nnreal_iff

end Int

namespace Rat

instance instNormedAddCommGroup : NormedAddCommGroup ℚ where
  norm r := ‖(r : ℝ)‖
  dist_eq r₁ r₂ := by simp only [Rat.dist_eq, norm, Rat.cast_sub]

@[norm_cast, simp 1001]
-- Porting note: increase priority to prevent the left-hand side from simplifying
theorem norm_cast_real (r : ℚ) : ‖(r : ℝ)‖ = ‖r‖ :=
  rfl
#align rat.norm_cast_real Rat.norm_cast_real

@[norm_cast, simp]
theorem _root_.Int.norm_cast_rat (m : ℤ) : ‖(m : ℚ)‖ = ‖m‖ := by
  rw [← Rat.norm_cast_real, ← Int.norm_cast_real]; congr 1
#align int.norm_cast_rat Int.norm_cast_rat

end Rat

-- Now that we've installed the norm on `ℤ`,
-- we can state some lemmas about `zsmul`.
section

variable [SeminormedCommGroup α]

@[to_additive norm_zsmul_le]
theorem norm_zpow_le_mul_norm (n : ℤ) (a : α) : ‖a ^ n‖ ≤ ‖n‖ * ‖a‖ := by
  rcases n.eq_nat_or_neg with ⟨n, rfl | rfl⟩ <;> simpa using norm_pow_le_mul_norm n a
#align norm_zpow_le_mul_norm norm_zpow_le_mul_norm
#align norm_zsmul_le norm_zsmul_le

@[to_additive nnnorm_zsmul_le]
theorem nnnorm_zpow_le_mul_norm (n : ℤ) (a : α) : ‖a ^ n‖₊ ≤ ‖n‖₊ * ‖a‖₊ := by
  simpa only [← NNReal.coe_le_coe, NNReal.coe_mul] using norm_zpow_le_mul_norm n a
#align nnnorm_zpow_le_mul_norm nnnorm_zpow_le_mul_norm
#align nnnorm_zsmul_le nnnorm_zsmul_le

end

namespace LipschitzWith

variable [PseudoEMetricSpace α] {K Kf Kg : ℝ≥0} {f g : α → E}

@[to_additive]
theorem inv (hf : LipschitzWith K f) : LipschitzWith K fun x => (f x)⁻¹ := fun x y =>
  (edist_inv_inv _ _).trans_le <| hf x y
#align lipschitz_with.inv LipschitzWith.inv
#align lipschitz_with.neg LipschitzWith.neg

@[to_additive add]
theorem mul' (hf : LipschitzWith Kf f) (hg : LipschitzWith Kg g) :
    LipschitzWith (Kf + Kg) fun x => f x * g x := fun x y =>
  calc
    edist (f x * g x) (f y * g y) ≤ edist (f x) (f y) + edist (g x) (g y) :=
      edist_mul_mul_le _ _ _ _
    _ ≤ Kf * edist x y + Kg * edist x y := add_le_add (hf x y) (hg x y)
    _ = (Kf + Kg) * edist x y := (add_mul _ _ _).symm
#align lipschitz_with.mul' LipschitzWith.mul'
#align lipschitz_with.add LipschitzWith.add

@[to_additive]
theorem div (hf : LipschitzWith Kf f) (hg : LipschitzWith Kg g) :
    LipschitzWith (Kf + Kg) fun x => f x / g x := by
  simpa only [div_eq_mul_inv] using hf.mul' hg.inv
#align lipschitz_with.div LipschitzWith.div
#align lipschitz_with.sub LipschitzWith.sub

end LipschitzWith

namespace AntilipschitzWith

variable [PseudoEMetricSpace α] {K Kf Kg : ℝ≥0} {f g : α → E}

@[to_additive]
theorem mul_lipschitzWith (hf : AntilipschitzWith Kf f) (hg : LipschitzWith Kg g) (hK : Kg < Kf⁻¹) :
    AntilipschitzWith (Kf⁻¹ - Kg)⁻¹ fun x => f x * g x := by
  letI : PseudoMetricSpace α := PseudoEMetricSpace.toPseudoMetricSpace hf.edist_ne_top
  refine AntilipschitzWith.of_le_mul_dist fun x y => ?_
  rw [NNReal.coe_inv, ← _root_.div_eq_inv_mul]
  rw [le_div_iff (NNReal.coe_pos.2 <| tsub_pos_iff_lt.2 hK)]
  rw [mul_comm, NNReal.coe_sub hK.le, _root_.sub_mul]
  -- Porting note: `ENNReal.sub_mul` should be `protected`?
  calc
    ↑Kf⁻¹ * dist x y - Kg * dist x y ≤ dist (f x) (f y) - dist (g x) (g y) :=
      sub_le_sub (hf.mul_le_dist x y) (hg.dist_le_mul x y)
    _ ≤ _ := le_trans (le_abs_self _) (abs_dist_sub_le_dist_mul_mul _ _ _ _)
#align antilipschitz_with.mul_lipschitz_with AntilipschitzWith.mul_lipschitzWith
#align antilipschitz_with.add_lipschitz_with AntilipschitzWith.add_lipschitzWith

@[to_additive]
theorem mul_div_lipschitzWith (hf : AntilipschitzWith Kf f) (hg : LipschitzWith Kg (g / f))
    (hK : Kg < Kf⁻¹) : AntilipschitzWith (Kf⁻¹ - Kg)⁻¹ g := by
  simpa only [Pi.div_apply, mul_div_cancel] using hf.mul_lipschitzWith hg hK
#align antilipschitz_with.mul_div_lipschitz_with AntilipschitzWith.mul_div_lipschitzWith
#align antilipschitz_with.add_sub_lipschitz_with AntilipschitzWith.add_sub_lipschitzWith

@[to_additive le_mul_norm_sub]
theorem le_mul_norm_div {f : E → F} (hf : AntilipschitzWith K f) (x y : E) :
    ‖x / y‖ ≤ K * ‖f x / f y‖ := by simp [← dist_eq_norm_div, hf.le_mul_dist x y]
#align antilipschitz_with.le_mul_norm_div AntilipschitzWith.le_mul_norm_div
#align antilipschitz_with.le_mul_norm_sub AntilipschitzWith.le_mul_norm_sub

end AntilipschitzWith

-- See note [lower instance priority]
@[to_additive]
instance (priority := 100) SeminormedCommGroup.to_lipschitzMul : LipschitzMul E :=
  ⟨⟨1 + 1, LipschitzWith.prod_fst.mul' LipschitzWith.prod_snd⟩⟩
#align seminormed_comm_group.to_has_lipschitz_mul SeminormedCommGroup.to_lipschitzMul
#align seminormed_add_comm_group.to_has_lipschitz_add SeminormedAddCommGroup.to_lipschitzAdd

-- See note [lower instance priority]
/-- A seminormed group is a uniform group, i.e., multiplication and division are uniformly
continuous. -/
@[to_additive "A seminormed group is a uniform additive group, i.e., addition and subtraction are
uniformly continuous."]
instance (priority := 100) SeminormedCommGroup.to_uniformGroup : UniformGroup E :=
  ⟨(LipschitzWith.prod_fst.div LipschitzWith.prod_snd).uniformContinuous⟩
#align seminormed_comm_group.to_uniform_group SeminormedCommGroup.to_uniformGroup
#align seminormed_add_comm_group.to_uniform_add_group SeminormedAddCommGroup.to_uniformAddGroup

-- short-circuit type class inference
-- See note [lower instance priority]
@[to_additive]
instance (priority := 100) SeminormedCommGroup.toTopologicalGroup : TopologicalGroup E :=
  inferInstance
#align seminormed_comm_group.to_topological_group SeminormedCommGroup.toTopologicalGroup
#align seminormed_add_comm_group.to_topological_add_group SeminormedAddCommGroup.toTopologicalAddGroup

@[to_additive]
theorem cauchySeq_prod_of_eventually_eq {u v : ℕ → E} {N : ℕ} (huv : ∀ n ≥ N, u n = v n)
    (hv : CauchySeq fun n => ∏ k ∈ range (n + 1), v k) :
    CauchySeq fun n => ∏ k ∈ range (n + 1), u k := by
  let d : ℕ → E := fun n => ∏ k ∈ range (n + 1), u k / v k
  rw [show (fun n => ∏ k ∈ range (n + 1), u k) = d * fun n => ∏ k ∈ range (n + 1), v k
      by ext n; simp [d]]
  suffices ∀ n ≥ N, d n = d N from (tendsto_atTop_of_eventually_const this).cauchySeq.mul hv
  intro n hn
  dsimp [d]
  rw [eventually_constant_prod _ (add_le_add_right hn 1)]
  intro m hm
  simp [huv m (le_of_lt hm)]
#align cauchy_seq_prod_of_eventually_eq cauchySeq_prod_of_eventually_eq
#align cauchy_seq_sum_of_eventually_eq cauchySeq_sum_of_eventually_eq

end SeminormedCommGroup

/-! ### `ULift` -/


namespace ULift

@[to_additive]
instance seminormedGroup [SeminormedGroup E] : SeminormedGroup (ULift E) :=
  SeminormedGroup.induced _ _
  { toFun := ULift.down,
    map_one' := rfl,
    map_mul' := fun _ _ => rfl : ULift E →* E }
#align ulift.seminormed_group ULift.seminormedGroup
#align ulift.seminormed_add_group ULift.seminormedAddGroup

@[to_additive]
instance seminormedCommGroup [SeminormedCommGroup E] : SeminormedCommGroup (ULift E) :=
  SeminormedCommGroup.induced _ _
  { toFun := ULift.down,
    map_one' := rfl,
    map_mul' := fun _ _ => rfl : ULift E →* E }
#align ulift.seminormed_comm_group ULift.seminormedCommGroup
#align ulift.seminormed_add_comm_group ULift.seminormedAddCommGroup

@[to_additive]
instance normedGroup [NormedGroup E] : NormedGroup (ULift E) :=
  NormedGroup.induced _ _
  { toFun := ULift.down,
    map_one' := rfl,
    map_mul' := fun _ _ => rfl : ULift E →* E }
  down_injective
#align ulift.normed_group ULift.normedGroup
#align ulift.normed_add_group ULift.normedAddGroup

@[to_additive]
instance normedCommGroup [NormedCommGroup E] : NormedCommGroup (ULift E) :=
  NormedCommGroup.induced _ _
  { toFun := ULift.down,
    map_one' := rfl,
    map_mul' := fun _ _ => rfl : ULift E →* E }
  down_injective
#align ulift.normed_comm_group ULift.normedCommGroup
#align ulift.normed_add_comm_group ULift.normedAddCommGroup

end ULift

/-! ### Subgroups of normed groups -/


namespace Subgroup

section SeminormedGroup

variable [SeminormedGroup E] {s : Subgroup E}

/-- A subgroup of a seminormed group is also a seminormed group,
with the restriction of the norm. -/
@[to_additive "A subgroup of a seminormed group is also a seminormed group, with the restriction of
the norm."]
instance seminormedGroup : SeminormedGroup s :=
  SeminormedGroup.induced _ _ s.subtype
#align subgroup.seminormed_group Subgroup.seminormedGroup
#align add_subgroup.seminormed_add_group AddSubgroup.seminormedAddGroup

/-- If `x` is an element of a subgroup `s` of a seminormed group `E`, its norm in `s` is equal to
its norm in `E`. -/
@[to_additive (attr := simp) "If `x` is an element of a subgroup `s` of a seminormed group `E`, its
norm in `s` is equal to its norm in `E`."]
theorem coe_norm (x : s) : ‖x‖ = ‖(x : E)‖ :=
  rfl
#align subgroup.coe_norm Subgroup.coe_norm
#align add_subgroup.coe_norm AddSubgroup.coe_norm

/-- If `x` is an element of a subgroup `s` of a seminormed group `E`, its norm in `s` is equal to
its norm in `E`.

This is a reversed version of the `simp` lemma `Subgroup.coe_norm` for use by `norm_cast`. -/
@[to_additive (attr := norm_cast) "If `x` is an element of a subgroup `s` of a seminormed group `E`,
its norm in `s` is equal to its norm in `E`.

This is a reversed version of the `simp` lemma `AddSubgroup.coe_norm` for use by `norm_cast`."]
theorem norm_coe {s : Subgroup E} (x : s) : ‖(x : E)‖ = ‖x‖ :=
  rfl
#align subgroup.norm_coe Subgroup.norm_coe
#align add_subgroup.norm_coe AddSubgroup.norm_coe

end SeminormedGroup

@[to_additive]
instance seminormedCommGroup [SeminormedCommGroup E] {s : Subgroup E} : SeminormedCommGroup s :=
  SeminormedCommGroup.induced _ _ s.subtype
#align subgroup.seminormed_comm_group Subgroup.seminormedCommGroup
#align add_subgroup.seminormed_add_comm_group AddSubgroup.seminormedAddCommGroup

@[to_additive]
instance normedGroup [NormedGroup E] {s : Subgroup E} : NormedGroup s :=
  NormedGroup.induced _ _ s.subtype Subtype.coe_injective
#align subgroup.normed_group Subgroup.normedGroup
#align add_subgroup.normed_add_group AddSubgroup.normedAddGroup

@[to_additive]
instance normedCommGroup [NormedCommGroup E] {s : Subgroup E} : NormedCommGroup s :=
  NormedCommGroup.induced _ _ s.subtype Subtype.coe_injective
#align subgroup.normed_comm_group Subgroup.normedCommGroup
#align add_subgroup.normed_add_comm_group AddSubgroup.normedAddCommGroup

end Subgroup

/-! ### Submodules of normed groups -/


namespace Submodule

-- See note [implicit instance arguments]
/-- A submodule of a seminormed group is also a seminormed group, with the restriction of the norm.
-/
instance seminormedAddCommGroup [Ring 𝕜] [SeminormedAddCommGroup E] [Module 𝕜 E]
    (s : Submodule 𝕜 E) : SeminormedAddCommGroup s :=
  SeminormedAddCommGroup.induced _ _ s.subtype.toAddMonoidHom
#align submodule.seminormed_add_comm_group Submodule.seminormedAddCommGroup

-- See note [implicit instance arguments].
/-- If `x` is an element of a submodule `s` of a normed group `E`, its norm in `s` is equal to its
norm in `E`. -/
@[simp]
theorem coe_norm [Ring 𝕜] [SeminormedAddCommGroup E] [Module 𝕜 E] {s : Submodule 𝕜 E}
    (x : s) : ‖x‖ = ‖(x : E)‖ :=
  rfl
#align submodule.coe_norm Submodule.coe_norm

-- See note [implicit instance arguments].
/-- If `x` is an element of a submodule `s` of a normed group `E`, its norm in `E` is equal to its
norm in `s`.

This is a reversed version of the `simp` lemma `Submodule.coe_norm` for use by `norm_cast`. -/
@[norm_cast]
theorem norm_coe [Ring 𝕜] [SeminormedAddCommGroup E] [Module 𝕜 E] {s : Submodule 𝕜 E}
    (x : s) : ‖(x : E)‖ = ‖x‖ :=
  rfl
#align submodule.norm_coe Submodule.norm_coe

-- See note [implicit instance arguments].
/-- A submodule of a normed group is also a normed group, with the restriction of the norm. -/
instance normedAddCommGroup [Ring 𝕜] [NormedAddCommGroup E] [Module 𝕜 E]
    (s : Submodule 𝕜 E) : NormedAddCommGroup s :=
  { Submodule.seminormedAddCommGroup s with
    eq_of_dist_eq_zero := eq_of_dist_eq_zero }

end Submodule

section NNReal

variable [SeminormedAddCommGroup E]

theorem eventually_nnnorm_sub_lt (x₀ : E) {ε : ℝ≥0} (ε_pos : 0 < ε) :
    ∀ᶠ x in 𝓝 x₀, ‖x - x₀‖₊ < ε :=
  (continuousAt_id.sub continuousAt_const).nnnorm (gt_mem_nhds <| by simpa)

theorem eventually_norm_sub_lt (x₀ : E) {ε : ℝ} (ε_pos : 0 < ε) :
    ∀ᶠ x in 𝓝 x₀, ‖x - x₀‖ < ε :=
  (continuousAt_id.sub continuousAt_const).norm (gt_mem_nhds <| by simpa)

end NNReal
