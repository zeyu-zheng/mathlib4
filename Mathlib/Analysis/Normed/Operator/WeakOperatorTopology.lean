import Mathlib.Tactic.Have
/-
Copyright (c) 2024 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/

import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Analysis.Normed.Module.Dual

/-!
# The weak operator topology

This file defines a type copy of `E →L[𝕜] F` (where `F` is a normed space) which is
endowed with the weak operator topology (WOT) rather than the topology induced by the operator norm.
The WOT is defined as the coarsest topology such that the functional `fun A => y (A x)` is
continuous for any `x : E` and `y : NormedSpace.Dual 𝕜 F`. Equivalently, a function `f` tends to
`A : E →WOT[𝕜] F` along filter `l` iff `y (f a x)` tends to `y (A x)` along the same filter.

Basic non-topological properties of `E →L[𝕜] F` (such as the module structure) are copied over to
the type copy.

We also prove that the WOT is induced by the family of seminorms `‖y (A x)‖` for `x : E` and
`y : NormedSpace.Dual 𝕜 F`.

## Main declarations

* `ContinuousLinearMapWOT 𝕜 E F`: The type copy of `E →L[𝕜] F` endowed with the weak operator
  topology.
* `ContinuousLinearMapWOT.tendsto_iff_forall_dual_apply_tendsto`: a function `f` tends to
  `A : E →WOT[𝕜] F` along filter `l` iff `y ((f a) x)` tends to `y (A x)` along the same filter.
* `ContinuousLinearMap.toWOT`: the inclusion map from `E →L[𝕜] F` to the type copy
* `ContinuousLinearMap.continuous_toWOT`: the inclusion map is continuous, i.e. the WOT is coarser
  than the norm topology.
* `ContinuousLinearMapWOT.withSeminorms`: the WOT is induced by the family of seminorms
  `‖y (A x)‖` for `x : E` and `y : NormedSpace.Dual 𝕜 F`.

## Notation

* The type copy of `E →L[𝕜] F` endowed with the weak operator topology is denoted by
  `E →WOT[𝕜] F`.
* We locally use the notation `F⋆` for `NormedSpace.Dual 𝕜 F`.

## Implementation notes

In the literature, the WOT is only defined on maps between Banach spaces. Here, we generalize this
a bit to `E →L[𝕜] F` where `F` is an normed space, and `E` actually only needs to be a vector
space with some topology for most results in this file.
-/

open scoped Topology

/-- The type copy of `E →L[𝕜] F` endowed with the weak operator topology, denoted as
`E →WOT[𝕜] F`. -/
@[irreducible]
def ContinuousLinearMapWOT (𝕜 : Type*) (E : Type*) (F : Type*) [Semiring 𝕜] [AddCommGroup E]
    [TopologicalSpace E] [Module 𝕜 E] [AddCommGroup F] [TopologicalSpace F] [Module 𝕜 F] :=
  E →L[𝕜] F

@[inherit_doc]
notation:25 E " →WOT[" 𝕜 "]" F => ContinuousLinearMapWOT 𝕜 E F

namespace ContinuousLinearMapWOT

variable {𝕜 : Type*} {E : Type*} {F : Type*} [RCLike 𝕜] [AddCommGroup E] [TopologicalSpace E]
  [Module 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]

local postfix:max "⋆" => NormedSpace.Dual 𝕜

/-!
### Basic properties common with `E →L[𝕜] F`

The section copies basic non-topological properties of `E →L[𝕜] F` over to `E →WOT[𝕜] F`, such as
the module structure, `FunLike`, etc.
-/
section Basic

unseal ContinuousLinearMapWOT in
instance instAddCommGroup : AddCommGroup (E →WOT[𝕜] F) :=
  inferInstanceAs <| AddCommGroup (E →L[𝕜] F)

unseal ContinuousLinearMapWOT in
instance instModule : Module 𝕜 (E →WOT[𝕜] F) := inferInstanceAs <| Module 𝕜 (E →L[𝕜] F)

variable (𝕜) (E) (F)

unseal ContinuousLinearMapWOT in
/-- The linear equivalence that sends a continuous linear map to the type copy endowed with the
weak operator topology.  -/
def _root_.ContinuousLinearMap.toWOT : (E →L[𝕜] F) ≃ₗ[𝕜] (E →WOT[𝕜] F) := LinearEquiv.refl 𝕜 _

variable {𝕜} {E} {F}

instance instFunLike : FunLike (E →WOT[𝕜] F) E F where
  coe f :=  ((ContinuousLinearMap.toWOT 𝕜 E F).symm f : E → F)
  coe_injective' := by intro; simp

instance instContinuousLinearMapClass : ContinuousLinearMapClass (E →WOT[𝕜] F) 𝕜 E F where
  map_add f x y := by simp only [DFunLike.coe]; simp
  map_smulₛₗ f r x := by simp only [DFunLike.coe]; simp
  map_continuous f := ContinuousLinearMap.continuous ((ContinuousLinearMap.toWOT 𝕜 E F).symm f)

lemma _root_.ContinuousLinearMap.toWOT_apply {A : E →L[𝕜] F} {x : E} :
    ((ContinuousLinearMap.toWOT 𝕜 E F) A) x = A x := rfl

unseal ContinuousLinearMapWOT in
lemma ext {A B : E →WOT[𝕜] F} (h : ∀ x, A x = B x) : A = B := ContinuousLinearMap.ext h

unseal ContinuousLinearMapWOT in
lemma ext_iff {A B : E →WOT[𝕜] F} : A = B ↔ ∀ x, A x = B x := ContinuousLinearMap.ext_iff

-- This `ext` lemma is set at a lower priority than the default of 1000, so that the
-- version with an inner product (`ContinuousLinearMapWOT.ext_inner`) takes precedence
-- in the case of Hilbert spaces.
@[ext 900]
lemma ext_dual {A B : E →WOT[𝕜] F} (h : ∀ x (y : F⋆), y (A x) = y (B x)) : A = B := by
  rw [ext_iff]
  intro x
  specialize h x
  rwa [← NormedSpace.eq_iff_forall_dual_eq 𝕜] at h

lemma ext_dual_iff {A B : E →WOT[𝕜] F} :
    A = B ↔ ∀ x (y : F⋆), y (A x) = y (B x) :=
  ⟨fun h _ _ => by simp [h], ext_dual⟩

@[simp] lemma zero_apply (x : E) : (0 : E →WOT[𝕜] F) x = 0 := by simp only [DFunLike.coe]; rfl

unseal ContinuousLinearMapWOT in
@[simp] lemma add_apply {f g : E →WOT[𝕜] F} (x : E) : (f + g) x = f x + g x := by
  simp only [DFunLike.coe]; rfl

unseal ContinuousLinearMapWOT in
@[simp] lemma sub_apply {f g : E →WOT[𝕜] F} (x : E) : (f - g) x = f x - g x := by
  simp only [DFunLike.coe]; rfl

unseal ContinuousLinearMapWOT in
@[simp] lemma neg_apply {f : E →WOT[𝕜] F} (x : E) : (-f) x = -(f x) := by
  simp only [DFunLike.coe]; rfl

unseal ContinuousLinearMapWOT in
@[simp] lemma smul_apply {f : E →WOT[𝕜] F} (c : 𝕜) (x : E) : (c • f) x = c • (f x) := by
  simp only [DFunLike.coe]; rfl

end Basic

/-!
### The topology of `E →WOT[𝕜] F`

The section endows `E →WOT[𝕜] F` with the weak operator topology and shows the basic properties
of this topology. In particular, we show that it is a topological vector space.
-/
section Topology

variable (𝕜) (E) (F) in
/-- The function that induces the topology on `E →WOT[𝕜] F`, namely the function that takes
an `A` and maps it to `fun ⟨x, y⟩ => y (A x)` in `E × F⋆ → 𝕜`, bundled as a linear map to make
it easier to prove that it is a TVS. -/
def inducingFn : (E →WOT[𝕜] F) →ₗ[𝕜] (E × F⋆ → 𝕜) where
  toFun := fun A ⟨x, y⟩ => y (A x)
  map_add' := fun x y => by ext; simp
  map_smul' := fun x y => by ext; simp

/-- The weak operator topology is the coarsest topology such that `fun A => y (A x)` is
continuous for all `x, y`. -/
instance instTopologicalSpace : TopologicalSpace (E →WOT[𝕜] F) :=
  .induced (inducingFn _ _ _) Pi.topologicalSpace

@[fun_prop]
lemma continuous_inducingFn : Continuous (inducingFn 𝕜 E F) :=
  continuous_induced_dom

lemma continuous_dual_apply (x : E) (y : F⋆) : Continuous fun (A : E →WOT[𝕜] F) => y (A x) := by
  refine (continuous_pi_iff.mp continuous_inducingFn) ⟨x, y⟩

@[fun_prop]
lemma continuous_of_dual_apply_continuous {α : Type*} [TopologicalSpace α] {g : α → E →WOT[𝕜] F}
    (h : ∀ x (y : F⋆), Continuous fun a => y (g a x)) : Continuous g :=
  continuous_induced_rng.2 (continuous_pi_iff.mpr fun p => h p.1 p.2)

lemma embedding_inducingFn : Embedding (inducingFn 𝕜 E F) := by
  refine Function.Injective.embedding_induced fun A B hAB => ?_
  rw [ext_dual_iff]
  simpa [Function.funext_iff] using hAB

open Filter in
/-- The defining property of the weak operator topology: a function `f` tends to
`A : E →WOT[𝕜] F` along filter `l` iff `y (f a x)` tends to `y (A x)` along the same filter. -/
lemma tendsto_iff_forall_dual_apply_tendsto {α : Type*} {l : Filter α} {f : α → E →WOT[𝕜] F}
    {A : E →WOT[𝕜] F} :
    Tendsto f l (𝓝 A) ↔ ∀ x (y : F⋆), Tendsto (fun a => y (f a x)) l (𝓝 (y (A x))) := by
  have hmain : (∀ x (y : F⋆), Tendsto (fun a => y (f a x)) l (𝓝 (y (A x))))
      ↔ ∀ (p : E × F⋆), Tendsto (fun a => p.2 (f a p.1)) l (𝓝 (p.2 (A p.1))) :=
    ⟨fun h p => h p.1 p.2, fun h x y => h ⟨x, y⟩⟩
  rw [hmain, ← tendsto_pi_nhds, Embedding.tendsto_nhds_iff embedding_inducingFn]
  rfl

lemma le_nhds_iff_forall_dual_apply_le_nhds {l : Filter (E →WOT[𝕜] F)} {A : E →WOT[𝕜] F} :
    l ≤ 𝓝 A ↔ ∀ x (y : F⋆), l.map (fun T => y (T x)) ≤ 𝓝 (y (A x)) :=
  tendsto_iff_forall_dual_apply_tendsto (f := id)

instance instT3Space : T3Space (E →WOT[𝕜] F) := embedding_inducingFn.t3Space

instance instContinuousAdd : ContinuousAdd (E →WOT[𝕜] F) := .induced (inducingFn 𝕜 E F)
instance instContinuousNeg : ContinuousNeg (E →WOT[𝕜] F) := .induced (inducingFn 𝕜 E F)
instance instContinuousSMul : ContinuousSMul 𝕜 (E →WOT[𝕜] F) := .induced (inducingFn 𝕜 E F)

instance instTopologicalAddGroup : TopologicalAddGroup (E →WOT[𝕜] F) where

instance instUniformSpace : UniformSpace (E →WOT[𝕜] F) := .comap (inducingFn 𝕜 E F) inferInstance

instance instUniformAddGroup : UniformAddGroup (E →WOT[𝕜] F) := .comap (inducingFn 𝕜 E F)

end Topology

/-! ### The WOT is induced by a family of seminorms -/
section Seminorms

/-- The family of seminorms that induce the weak operator topology, namely `‖y (A x)‖` for
all `x` and `y`.  -/
def seminorm (x : E) (y : F⋆) : Seminorm 𝕜 (E →WOT[𝕜] F) where
  toFun A := ‖y (A x)‖
  map_zero' := by simp
  add_le' A B := by simpa using norm_add_le _ _
  neg' A := by simp
  smul' r A := by simp

variable (𝕜) (E) (F) in
/-- The family of seminorms that induce the weak operator topology, namely `‖y (A x)‖` for
all `x` and `y`.  -/
def seminormFamily : SeminormFamily 𝕜 (E →WOT[𝕜] F) (E × F⋆) :=
  fun ⟨x, y⟩ => seminorm x y

lemma hasBasis_seminorms : (𝓝 (0 : E →WOT[𝕜] F)).HasBasis (seminormFamily 𝕜 E F).basisSets id := by
  let p := seminormFamily 𝕜 E F
  rw [nhds_induced, nhds_pi]
  simp only [map_zero, Pi.zero_apply]
  have h := Filter.hasBasis_pi (fun _ : (E × F⋆) ↦ Metric.nhds_basis_ball (x := 0)) |>.comap
    (inducingFn 𝕜 E F)
  refine h.to_hasBasis' ?_ ?_
  rintro ⟨s, U₂⟩ ⟨hs, hU₂⟩
  lift s to Finset (E × F⋆) using hs
  by_cases hU₃ : s.Nonempty
  refine ⟨(s.sup p).ball 0 <| s.inf' hU₃ U₂, p.basisSets_mem _ <| (Finset.lt_inf'_iff _).2 hU₂,
    fun x hx y hy => ?_⟩
  simp only [Set.mem_preimage, Set.mem_pi, mem_ball_zero_iff]
  rw [id, Seminorm.mem_ball_zero] at hx
  have hp : p y ≤ s.sup p := Finset.le_sup hy
  refine lt_of_le_of_lt (hp x) (lt_of_lt_of_le hx ?_)
  exact Finset.inf'_le _ hy
  rw [Finset.not_nonempty_iff_eq_empty.mp hU₃]
  exact ⟨(p 0).ball 0 1, p.basisSets_singleton_mem 0 one_pos, by simp⟩
  suffices ∀ U ∈ p.basisSets, U ∈ 𝓝 (0 : E →WOT[𝕜] F) by simpa [nhds_induced, nhds_pi]
  exact p.basisSets_mem_nhds fun ⟨x, y⟩ ↦ continuous_dual_apply x y |>.norm

lemma withSeminorms : WithSeminorms (seminormFamily 𝕜 E F) :=
  SeminormFamily.withSeminorms_of_hasBasis _ hasBasis_seminorms

instance instLocallyConvexSpace [Module ℝ (E →WOT[𝕜] F)] [IsScalarTower ℝ 𝕜 (E →WOT[𝕜] F)] :
    LocallyConvexSpace ℝ (E →WOT[𝕜] F) :=
  withSeminorms.toLocallyConvexSpace

end Seminorms

end ContinuousLinearMapWOT

section NormedSpace

variable {𝕜 : Type*} {E : Type*} {F : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- The weak operator topology is coarser than the norm topology, i.e. the inclusion map is
continuous. -/
@[continuity, fun_prop]
lemma ContinuousLinearMap.continuous_toWOT :
    Continuous (ContinuousLinearMap.toWOT 𝕜 E F) := by
  refine ContinuousLinearMapWOT.continuous_of_dual_apply_continuous fun x y => ?_
  simp_rw [ContinuousLinearMap.toWOT_apply]
  change Continuous fun a => y <| (ContinuousLinearMap.id 𝕜 (E →L[𝕜] F)).flip x a
  fun_prop

/-- The inclusion map from `E →[𝕜] F` to `E →WOT[𝕜] F`, bundled as a continuous linear map. -/
def ContinuousLinearMap.toWOTCLM : (E →L[𝕜] F) →L[𝕜] (E →WOT[𝕜] F) :=
  ⟨LinearEquiv.toLinearMap (ContinuousLinearMap.toWOT 𝕜 E F), ContinuousLinearMap.continuous_toWOT⟩

end NormedSpace
