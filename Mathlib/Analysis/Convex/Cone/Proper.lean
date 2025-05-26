/-
Copyright (c) 2022 Apurva Nakade. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Apurva Nakade, Yaël Dillies
-/
import Mathlib.Analysis.Convex.Cone.Closure
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Topology.Algebra.Module.ClosedSubmodule
import Mathlib.Topology.Algebra.Order.Module

/-!
# Proper cones

We define a *proper cone* as a closed, pointed cone. Proper cones are used in defining conic
programs which generalize linear programs. A linear program is a conic program for the positive
cone. We then prove Farkas' lemma for conic programs following the proof in the reference below.
Farkas' lemma is equivalent to strong duality. So, once we have the definitions of conic and
linear programs, the results from this file can be used to prove duality theorems.

## TODO

The next steps are:
- Add convex_cone_class that extends set_like and replace the below instance
- Define primal and dual cone programs and prove weak duality.
- Prove regular and strong duality for cone programs using Farkas' lemma (see reference).
- Define linear programs and prove LP duality as a special case of cone duality.
- Find a better reference (textbook instead of lecture notes).

## References

- [B. Gartner and J. Matousek, Cone Programming][gartnerMatousek]

-/

open ContinuousLinearMap Filter Function Set

variable {R E F G : Type*} [Semiring R] [PartialOrder R] [IsOrderedRing R]
variable [AddCommMonoid E] [TopologicalSpace E] [Module R E]
variable [AddCommMonoid F] [TopologicalSpace F] [Module R F]
variable [AddCommMonoid G] [TopologicalSpace G] [Module R G]

local notation "R≥0" => {r : R // 0 ≤ r}

variable (R E) in
/-- A proper cone is a pointed cone `C` that is closed. Proper cones have the nice property that
they are equal to their double dual, see `ProperCone.dual_dual`.
This makes them useful for defining cone programs and proving duality theorems. -/
abbrev ProperCone := ClosedSubmodule R≥0 E

namespace ProperCone
section Module
variable {C C₁ C₂ : ProperCone R E} {r : R} {x : E}

/-- Alias of `ClosedSubmodule.toSubmodule` for convenience and discoverability. -/
@[coe] abbrev toPointedCone (C : ProperCone R E) : PointedCone R E := C.toSubmodule

instance : Coe (ProperCone R E) (PointedCone R E) := ⟨toPointedCone⟩

lemma toPointedCone_injective : Injective ((↑) : ProperCone R E → PointedCone R E) :=
  ClosedSubmodule.toSubmodule_injective

-- TODO: add `ConvexConeClass` that extends `SetLike` and replace the below instance
instance : SetLike (ProperCone R E) E where
  coe C := C.carrier
  coe_injective' _ _ h := ProperCone.toPointedCone_injective <| SetLike.coe_injective h

@[ext] lemma ext (h : ∀ x, x ∈ C₁ ↔ x ∈ C₂) : C₁ = C₂ := SetLike.ext h

@[simp] lemma mem_toPointedCone : x ∈ C.toPointedCone ↔ x ∈ C := .rfl

protected lemma pointed_toConvexCone (C : ProperCone R E) : (C : ConvexCone R E).Pointed :=
  C.toPointedCone.pointed_toConvexCone

protected lemma nonempty (C : ProperCone R E) : (C : Set E).Nonempty := C.toSubmodule.nonempty
protected lemma isClosed (C : ProperCone R E) : IsClosed (C : Set E) := C.isClosed'

protected nonrec lemma smul_mem (C : ProperCone R E) (hx : x ∈ C) (hr : 0 ≤ r) : r • x ∈ C :=
  C.smul_mem ⟨r, hr⟩ hx

section T1Space
variable [T1Space E]

lemma mem_bot : x ∈ (⊥ : ProperCone R E) ↔ x = 0 := .rfl

@[simp, norm_cast] lemma toPointedCone_bot : (⊥ : ProperCone R E).toPointedCone = ⊥ := rfl

end T1Space

/-- The closure of image of a proper cone under a `ℝ`-linear map is a proper cone. We
use continuous maps here so that the comap of f is also a map between proper cones. -/
abbrev comap (f : E →L[R] F) (C : ProperCone R F) : ProperCone R E :=
  ClosedSubmodule.comap (f.restrictScalars R≥0) C

@[simp] lemma comap_id (C : ProperCone R F) : C.comap (.id _ _) = C := rfl

@[simp] lemma coe_comap (f : E →L[R] F) (C : ProperCone R F) : (C.comap f : Set E) = f ⁻¹' C := rfl

lemma comap_comap (g : F →L[R] G) (f : E →L[R] F) (C : ProperCone R G) :
    (C.comap g).comap f = C.comap (g.comp f) := rfl

lemma mem_comap {C : ProperCone R F} {f : E →L[R] F} : x ∈ C.comap f ↔ f x ∈ C := .rfl

variable [ContinuousAdd F] [ContinuousConstSMul R F]

/-- The closure of image of a proper cone under a linear map is a proper cone.

We use continuous maps here to match `ProperCone.comap`. -/
abbrev map (f : E →L[R] F) (C : ProperCone R E) : ProperCone R F :=
  ClosedSubmodule.map (f.restrictScalars R≥0) C

@[simp] lemma map_id (C : ProperCone R F) : C.map (.id _ _) = C := ClosedSubmodule.map_id _

@[simp, norm_cast]
lemma coe_map (f : E →L[R] F) (C : ProperCone R E) :
    C.map f = (C.toPointedCone.map (f : E →ₗ[R] F)).closure := rfl

@[simp]
lemma mem_map {f : E →L[R] F} {K : ProperCone R E} {y : F} :
    y ∈ K.map f ↔ y ∈ (PointedCone.map (f : E →ₗ[R] F) ↑K).closure := .rfl

end Module

section PositiveCone
variable {E : Type*} [AddCommGroup E] [TopologicalSpace E] [Module R E] [PartialOrder E]
  [IsOrderedAddMonoid E] [OrderedSMul R E] [OrderClosedTopology E] {x : E}

variable (R E) in
/-- The positive cone is the proper cone formed by the set of nonnegative elements in an ordered
module. -/
@[simps!]
def positive : ProperCone R E where
  toSubmodule := PointedCone.positive R E
  isClosed' := isClosed_Ici

@[simp] lemma mem_positive : x ∈ positive R E ↔ 0 ≤ x := .rfl

end PositiveCone

section Module

variable {𝕜 : Type*} [Semiring 𝕜] [PartialOrder 𝕜] [IsOrderedRing 𝕜]
variable {E : Type*} [AddCommMonoid E] [TopologicalSpace E] [T1Space E] [Module 𝕜 E]

instance : Zero (ProperCone 𝕜 E) :=
  ⟨{ toSubmodule := 0
     isClosed' := isClosed_singleton }⟩

instance : Inhabited (ProperCone 𝕜 E) :=
  ⟨0⟩

@[simp]
theorem mem_zero (x : E) : x ∈ (0 : ProperCone 𝕜 E) ↔ x = 0 :=
  Iff.rfl

@[simp, norm_cast]
theorem coe_zero : ↑(0 : ProperCone 𝕜 E) = (0 : ConvexCone 𝕜 E) :=
  rfl

theorem pointed_zero : ((0 : ProperCone 𝕜 E) : ConvexCone 𝕜 E).Pointed := by
  simp [ConvexCone.pointed_zero]

end Module

section InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
variable {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G]

protected theorem pointed (K : ProperCone ℝ E) : (K : ConvexCone ℝ E).Pointed :=
  (K : ConvexCone ℝ E).pointed_of_nonempty_of_isClosed K.nonempty K.isClosed

/-- The inner dual cone of a proper cone is a proper cone. -/
def dual (K : ProperCone ℝ E) : ProperCone ℝ E where
  toSubmodule := PointedCone.dual (K : PointedCone ℝ E)
  isClosed' := isClosed_innerDualCone _

@[simp, norm_cast]
theorem coe_dual (K : ProperCone ℝ E) : K.dual = (K : Set E).innerDualCone :=
  rfl

open scoped InnerProductSpace in
@[simp]
theorem mem_dual {K : ProperCone ℝ E} {y : E} : y ∈ dual K ↔ ∀ ⦃x⦄, x ∈ K → 0 ≤ ⟪x, y⟫_ℝ := by
  aesop

end InnerProductSpace

section CompleteSpace

open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- The dual of the dual of a proper cone is itself. -/
@[simp]
theorem dual_dual (K : ProperCone ℝ E) : K.dual.dual = K :=
  ProperCone.toPointedCone_injective <| PointedCone.toConvexCone_injective <|
    (K : ConvexCone ℝ E).innerDualCone_of_innerDualCone_eq_self K.nonempty K.isClosed

/-- This is a relative version of
`ConvexCone.hyperplane_separation_of_nonempty_of_isClosed_of_notMem`, which we recover by setting
`f` to be the identity map. This is also a geometric interpretation of the Farkas' lemma
stated using proper cones. -/
theorem hyperplane_separation (K : ProperCone ℝ E) {f : E →L[ℝ] F} {b : F} :
    b ∈ K.map f ↔ ∀ y : F, adjoint f y ∈ K.dual → 0 ≤ ⟪y, b⟫_ℝ :=
  Iff.intro
    (by
      -- suppose `b ∈ K.map f`
      simp_rw [mem_map, PointedCone.mem_closure, PointedCone.coe_map, coe_coe,
        mem_closure_iff_seq_limit, mem_image, SetLike.mem_coe, mem_dual,
        adjoint_inner_right, forall_exists_index, and_imp]

      -- there is a sequence `seq : ℕ → F` in the image of `f` that converges to `b`
      rintro seq hmem htends y hinner
      suffices h : ∀ n, 0 ≤ ⟪y, seq n⟫_ℝ from
        ge_of_tendsto'
          (Continuous.seqContinuous (Continuous.inner (@continuous_const _ _ _ _ y) continuous_id)
            htends)
          h
      intro n
      obtain ⟨_, h, hseq⟩ := hmem n
      simpa only [← hseq, real_inner_comm] using hinner h)
    (by
      -- proof by contradiction
      -- suppose `b ∉ K.map f`
      intro h
      contrapose! h

      -- as `b ∉ K.map f`, there is a hyperplane `y` separating `b` from `K.map f`
      let C := PointedCone.toConvexCone (𝕜 := ℝ) (E := F) (K.map f)
      obtain ⟨y, hxy, hyb⟩ :=
        @ConvexCone.hyperplane_separation_of_nonempty_of_isClosed_of_notMem
        _ _ _ _ C (K.map f).nonempty (K.map f).isClosed b h

      -- the rest of the proof is a straightforward algebraic manipulation
      refine ⟨y, ?_, hyb⟩
      simp_rw [ProperCone.mem_dual, adjoint_inner_right]
      intro x hxK
      apply hxy (f x)
      simp_rw [C, coe_map]
      apply subset_closure
      simp_rw [PointedCone.toConvexCone_map, ConvexCone.coe_map, coe_coe, mem_image,
        SetLike.mem_coe]
      exact ⟨x, hxK, rfl⟩)

theorem hyperplane_separation_of_notMem (K : ProperCone ℝ E) {f : E →L[ℝ] F} {b : F}
    (disj : b ∉ K.map f) : ∃ y : F, adjoint f y ∈ K.dual ∧ ⟪y, b⟫_ℝ < 0 := by
  contrapose! disj; rwa [K.hyperplane_separation]

@[deprecated (since := "2025-05-24")]
alias hyperplane_separation_of_nmem := hyperplane_separation_of_notMem

end CompleteSpace

end ProperCone
