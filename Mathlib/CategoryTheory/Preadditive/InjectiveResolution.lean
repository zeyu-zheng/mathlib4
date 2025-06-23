import Mathlib.Tactic.Have
/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Scott Morrison, Joël Riou
-/
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Homology.SingleHomology
import Mathlib.CategoryTheory.Preadditive.Injective

/-!
# Injective resolutions

An injective resolution `I : InjectiveResolution Z` of an object `Z : C` consists of
an `ℕ`-indexed cochain complex `I.cocomplex` of injective objects,
along with a quasi-isomorphism `I.ι` from the cochain complex consisting just of `Z`
in degree zero to `I.cocomplex`.
```
Z ----> 0 ----> ... ----> 0 ----> ...
|       |                 |
|       |                 |
v       v                 v
I⁰ ---> I¹ ---> ... ----> Iⁿ ---> ...
```
-/


noncomputable section

universe v u

namespace CategoryTheory

open Limits HomologicalComplex CochainComplex

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasZeroMorphisms C]
/--
An `InjectiveResolution Z` consists of a bundled `ℕ`-indexed cochain complex of injective objects,
along with a quasi-isomorphism from the complex consisting of just `Z` supported in degree `0`.
-/
-- Porting note(#5171): this linter isn't ported yet.
-- @[nolint has_nonempty_instance]
structure InjectiveResolution (Z : C) where
  /-- the cochain complex involved in the resolution -/
  cocomplex : CochainComplex C ℕ
  /-- the cochain complex must be degreewise injective -/
  injective : ∀ n, Injective (cocomplex.X n) := by infer_instance
  /-- the cochain complex must have homology -/
  [hasHomology : ∀ i, cocomplex.HasHomology i]
  /-- the morphism from the single cochain complex with `Z` in degree `0` -/
  ι : (single₀ C).obj Z ⟶ cocomplex
  /-- the morphism from the single cochain complex with `Z` in degree `0` is a quasi-isomorphism -/
  quasiIso : QuasiIso ι := by infer_instance

open InjectiveResolution in
attribute [instance] injective hasHomology InjectiveResolution.quasiIso

/-- An object admits an injective resolution. -/
class HasInjectiveResolution (Z : C) : Prop where
  out : Nonempty (InjectiveResolution Z)

attribute [inherit_doc HasInjectiveResolution] HasInjectiveResolution.out

section

variable (C)

/-- You will rarely use this typeclass directly: it is implied by the combination
`[EnoughInjectives C]` and `[Abelian C]`. -/
class HasInjectiveResolutions : Prop where
  out : ∀ Z : C, HasInjectiveResolution Z

attribute [instance 100] HasInjectiveResolutions.out

end

namespace InjectiveResolution

variable {Z : C} (I : InjectiveResolution Z)

lemma cocomplex_exactAt_succ (n : ℕ) :
    I.cocomplex.ExactAt (n + 1) := by
  rw [← quasiIsoAt_iff_exactAt I.ι (n + 1) (exactAt_succ_single_obj _ _)]
  infer_instance

lemma exact_succ (n : ℕ) :
    (ShortComplex.mk _ _ (I.cocomplex.d_comp_d n (n + 1) (n + 2))).Exact :=
  (HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 2) (by simp)
    (by simp only [CochainComplex.next]; rfl)).1 (I.cocomplex_exactAt_succ n)

@[simp]
theorem ι_f_succ (n : ℕ) : I.ι.f (n + 1) = 0 :=
  (isZero_single_obj_X _ _ _ _ (by simp)).eq_of_src _ _

-- Porting note (#10618): removed @[simp] simp can prove this
@[reassoc]
theorem ι_f_zero_comp_complex_d :
    I.ι.f 0 ≫ I.cocomplex.d 0 1 = 0 := by
  simp

-- Porting note (#10618): removed @[simp] simp can prove this
theorem complex_d_comp (n : ℕ) :
    I.cocomplex.d n (n + 1) ≫ I.cocomplex.d (n + 1) (n + 2) = 0 := by
  simp

/-- The (limit) kernel fork given by the composition
`Z ⟶ I.cocomplex.X 0 ⟶ I.cocomplex.X 1` when `I : InjectiveResolution Z`. -/
@[simp]
def kernelFork : KernelFork (I.cocomplex.d 0 1) :=
  KernelFork.ofι _ I.ι_f_zero_comp_complex_d

/-- `Z` is the kernel of `I.cocomplex.X 0 ⟶ I.cocomplex.X 1` when `I : InjectiveResolution Z`. -/
def isLimitKernelFork : IsLimit (I.kernelFork) := by
  refine IsLimit.ofIsoLimit (I.cocomplex.cyclesIsKernel 0 1 (by simp)) (Iso.symm ?_)
  refine Fork.ext ((singleObjHomologySelfIso _ _ _).symm ≪≫
    isoOfQuasiIsoAt I.ι 0 ≪≫ I.cocomplex.isoHomologyπ₀.symm) ?_
  rw [← cancel_epi (singleObjHomologySelfIso (ComplexShape.up ℕ) _ _).hom,
    ← cancel_epi (isoHomologyπ₀ _).hom,
    ← cancel_epi (singleObjCyclesSelfIso (ComplexShape.up ℕ) _ _).inv]
  simp

instance (n : ℕ) : Mono (I.ι.f n) := by
  cases n
  exact mono_of_isLimit_fork I.isLimitKernelFork
  rw [ι_f_succ]; infer_instance

variable (Z)

/-- An injective object admits a trivial injective resolution: itself in degree 0. -/
@[simps]
def self [Injective Z] : InjectiveResolution Z where
  cocomplex := (CochainComplex.single₀ C).obj Z
  ι := 𝟙 ((CochainComplex.single₀ C).obj Z)
  injective n := by
    cases n
    · simpa
    · apply IsZero.injective
      apply HomologicalComplex.isZero_single_obj_X
      simp

end InjectiveResolution

end CategoryTheory
