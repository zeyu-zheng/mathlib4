/-
Copyright (c) 2024 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/

import Mathlib.NumberTheory.Padics.MahlerBasis
import Mathlib.Topology.UniformSpace.CoveringProfinite

/-!
# Abstract measures on topological spaces

We define an "abstract measure" on `X`, with values in a normed ring `R`, to be an `R`-linear
functional on continuous maps `X → R`. This is an important construction in p-adic analysis (where
the Iwasawa algebra is defined as the space of abstract measures on `ℤ_[p]` with values in `ℚ_[p]`).
-/

open ContinuousMap

variable
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {R : Type*} [NormedCommRing R]
    {E : Type*} [NormedAddCommGroup E] [Module R E] [ContinuousSMul R E]

attribute [local ext] DFunLike.ext -- why is this not set by default?

section Preliminaries

open scoped TensorProduct

/-- Pullback via a continuous map, as a continuous linear map on continuous functions. -/
@[simps apply]
def ContinuousMap.comapCLM (f : C(X, Y)) : C(Y, E) →L[R] C(X, E) where
  toFun g := g.comp f
  map_add' _ _ := add_comp _ _ f
  map_smul' _ _ := smul_comp _ _ f

/-- The natural bilinear map sending `f, g` to the function `(x, y) ↦ f x * g y` on `X × Y`. -/
def ContinuousMap.prodMul : C(X, R) →ₗ[R] C(Y, R) →ₗ[R] C(X × Y, R) :=
  LinearMap.mk₂ R (fun f g ↦ (f.comp .fst) * (g.comp .snd))
    (fun f f' g ↦ by ext; simp [add_mul])
    (fun r f g ↦ by ext; simp [mul_assoc])
    (fun f g g' ↦ by ext; simp [mul_add])
    (fun r f g ↦ by ext; simp [mul_left_comm])

lemma ContinuousMap.prodMul_apply (f : C(X, R)) (g : C(Y, R)) (p : X × Y) :
    f.prodMul g p  = f p.1 * g p.2 := rfl

/-- Tensor product version of `ContinuousMap.prodMul`. -/
noncomputable def ContinuousMap.tensorHom : C(X, R) ⊗[R] C(Y, R) → C(X × Y, R) :=
  TensorProduct.lift ContinuousMap.prodMul

/-- Composition of continuous linear maps, as a linear map. Compare `LinearMap.lcomp`. -/
@[simps]
def ContinuousLinearMap.lcomp {U V : Type*} (W : Type*)
    [AddCommMonoid U] [Module R U] [TopologicalSpace U]
    [AddCommMonoid V] [Module R V] [TopologicalSpace V]
    [AddCommGroup W] [Module R W] [TopologicalSpace W]
    [IsTopologicalAddGroup W] [ContinuousSMul R W]
    (f : U →L[R] V) : (V →L[R] W) →ₗ[R] (U →L[R] W) where
  toFun l := l.comp f
  map_add' _ _ := by simp
  map_smul' _ _ := by simp

/-- Composition of continuous linear maps, as a bilinear map. Compare `LinearMap.llcomp`. -/
@[simps]
def ContinuousLinearMap.llcomp (U V W : Type*)
    [AddCommGroup U] [Module R U] [TopologicalSpace U]
    [AddCommGroup V] [Module R V] [TopologicalSpace V]
    [IsTopologicalAddGroup V] [ContinuousSMul R V]
    [AddCommGroup W] [Module R W] [TopologicalSpace W]
    [IsTopologicalAddGroup W] [ContinuousSMul R W] :
    (U →L[R] V) →ₗ[R] (V →L[R] W) →ₗ[R] (U →L[R] W) where
  toFun l := l.lcomp W
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

end Preliminaries

section Defs

/-!
### Basic definitions
-/

variable (X R E) in
/--
The space of `E`-valued measures on `X`, i.e. continuous linear maps `C(X, R) → E`. (The case
`R = E` is the most important case.)

This is a type synonym for `C(X, R) →L[R] E`, but we do not want it to inherit the default
(norm) topology.
-/
def AbstractMeasure := C(X, R) →L[R] E

scoped [AbstractMeasure] notation "D(" X ", " R ")" => AbstractMeasure X R R

end Defs

namespace AbstractMeasure

/-- Inherit `FunLike` structure from `C(G, R) →L[R] E`. -/
instance : FunLike (AbstractMeasure X R E) C(X, R) E :=
  inferInstanceAs (FunLike (C(X, R) →L[R] E) C(X, R) E)

/-- Inherit `ContinuousLinearMapClass` structure from `C(X, R) →L[R] E`. -/
instance : ContinuousLinearMapClass (AbstractMeasure X R E) R C(X, R) E :=
  inferInstanceAs (ContinuousLinearMapClass (C(X, R) →L[R] E) R C(X, R) E)

/-- Inherit `AddCommGroup` structure from `C(G, R) →L[R] E`. -/
instance : AddCommGroup (AbstractMeasure X R E) :=
  inferInstanceAs (AddCommGroup (C(X, R) →L[R] E))

/-- Inherit `R`-module structure from `C(G, R) →L[R] E`. -/
instance : Module R (AbstractMeasure X R E) :=
  inferInstanceAs (Module R (C(X, R) →L[R] E))

variable (R) in
/-- The Dirac measure, "evaluation at `x`". -/
def dirac (x : X) : D(X, R) :=
  ContinuousMap.evalCLM R x

@[simp] lemma dirac_apply (x : X) (f : C(X, R)) : dirac R x f = f x := rfl

@[simp]
lemma smul_apply (r : R) (μ : AbstractMeasure X R E) (f : C(X, R)) : (r • μ) f = r • μ f :=
  rfl

omit [ContinuousSMul R E] in
@[simp]
lemma add_apply (μ ν : AbstractMeasure X R E) (f : C(X, R)) : (μ + ν) f = μ f + ν f :=
  rfl

/-- Measures can be pushed forward (R-linearly) along continuous maps. -/
def map (f : C(X, Y)) : AbstractMeasure X R E →ₗ[R] AbstractMeasure Y R E where
  toFun μ := μ ∘L comapCLM f
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] lemma map_apply (f : C(X, Y)) (μ : AbstractMeasure X R E) (g : C(Y, R)) :
    map f μ g = μ (g.comp f) :=
  rfl

lemma map_dirac (f : C(X, Y)) (x : X) : map f (dirac R x) = dirac R (f x) := rfl

section Prod

/-!
### Product structure
-/

-- note we define `contractSnd` first, because `f.curry` only works one way round

/-- Integrate a measure on `Y` against a function on `X × Y`, giving a function on `X`. -/
def contractSnd : D(Y, R) →ₗ[R] C(X × Y, R) →ₗ[R] C(X, R) :=
  LinearMap.mk₂ R (fun ν f ↦ comp ν f.curry)
    (fun ν ν' f ↦ by
      ext x
      simp only [comp_apply, ContinuousMap.coe_coe, add_apply, ContinuousMap.add_apply])
    (fun r ν f ↦ by
      ext x
      simp only [comp_apply, ContinuousMap.coe_coe, smul_apply, smul_eq_mul, coe_smul, coe_comp,
        Pi.smul_apply, Function.comp_apply])
    (fun ν f f' ↦ by
      ext x
      simp only [comp_apply, ContinuousMap.coe_coe, ContinuousMap.add_apply, ← map_add]
      rfl)
    (fun ν r f ↦ by
      ext x
      simp only [comp_apply, ContinuousMap.coe_coe, ContinuousMap.smul_apply, ← map_smul]
      rfl)

/-- Integrate a measure on `X` against a function on `X × Y`, giving a function on `Y`. -/
def contractFst : D(X, R) →ₗ[R] C(X × Y, R) →ₗ[R] C(Y, R) :=
  (prodSwap.comapCLM.toLinearMap.lcomp R _).comp contractSnd

variable (μ : D(X, R)) (ν : D(Y, R))

@[simp]
lemma contractFst_apply (f : C(X × Y, R)) (y : Y) :
    contractFst μ f y = μ ⟨fun x ↦ f (x, y), by continuity⟩ :=
  rfl

@[simp]
lemma contractSnd_apply (f : C(X × Y, R)) (x : X) :
    contractSnd ν f x = ν ⟨fun y ↦ f (x, y), by continuity⟩ :=
  rfl

lemma contractFst_dirac (x : X) (y : Y) (f : C(X × Y, R)) :
    contractFst (dirac R x) f y = f (x, y) :=
  rfl

lemma contractSnd_dirac (x : X) (y : Y) (f : C(X × Y, R)) :
    contractSnd (dirac R y) f x = f (x, y) :=
  rfl

section LocallyCompact

variable [LocallyCompactSpace X] [LocallyCompactSpace Y]

/-- `AbstractMeasure.contractSnd` bundled with continuity in the function argument. -/
def contractSndCLM : D(Y, R) →ₗ[R] C(X × Y, R) →L[R] C(X, R) where
  toFun ν := ⟨contractSnd ν, by
    refine continuous_of_continuous_uncurry _ (ν.continuous.comp ?_)
    apply continuous_of_continuous_uncurry
    rw [← (Homeomorph.prodAssoc C(X × Y, R) X Y).symm.comp_continuous_iff']
    exact ContinuousEval.continuous_eval⟩
  map_add' _ _ := ContinuousLinearMap.coe_injective.eq_iff.mp <| contractSnd.map_add _ _
  map_smul' _ _ := ContinuousLinearMap.coe_injective.eq_iff.mp <| contractSnd.map_smul _ _

lemma contractSndCLM_apply (f : C(X × Y, R)) (x : X) :
    contractSndCLM ν f x = ν ⟨fun y ↦ f (x, y), by continuity⟩ := rfl

/-- `AbstractMeasure.contractFst` bundled with continuity in the function argument. -/
def contractFstCLM : D(X, R) →ₗ[R] C(X × Y, R) →L[R] C(Y, R) :=
  (ContinuousMap.prodSwap.comapCLM.lcomp _).comp contractSndCLM

lemma contractFstCLM_apply (f : C(X × Y, R)) (y : Y) :
    contractFstCLM μ f y = μ ⟨fun x ↦ f (x, y), by continuity⟩ := rfl

/-- "Left-handed" version of the natural product map on distributions (acting on functions
as first integrating along `X`, and then integrating the result along `Y`). -/
def prodMk : D(X, R) →ₗ[R] D(Y, R) →ₗ[R] D(X × Y, R) :=
  (ContinuousLinearMap.llcomp _ _ R).comp contractFstCLM

@[simp] lemma prodMk_apply (f : C(X × Y, R)) :
  prodMk μ ν f = ν (μ.contractFst f) := rfl

/-- On functions of the form `(x, y) ↦ f x * g y`, the measure `prodMk μ ν` agrees with the
algebraic tensor product of `μ` and `ν`. -/
lemma prodMk_prod_apply (f : C(X, R)) (g : C(Y, R)) :
    prodMk μ ν ((f.comp .fst) * (g.comp .snd)) = μ f * ν g := by
  simp only [← smul_eq_mul, prodMk_apply, ← map_smul]
  congr 1 with y
  simp_rw [contractFst_apply, ContinuousMap.smul_apply, smul_eq_mul, mul_comm (μ f) (g y),
    ← smul_eq_mul, ← map_smul]
  congr 1 with x
  simp_rw [ContinuousMap.smul_apply, smul_eq_mul, mul_comm (g y) (f x)]
  rfl

/-- "Right-handed" version of the natural product map on distributions (acting on functions
as first integrating along `Y`, and then integrating the result along `X`). -/
def prodMk' : D(X, R) →ₗ[R] D(Y, R) →ₗ[R] D(X × Y, R) :=
  ((ContinuousLinearMap.llcomp _ _ R).comp contractSndCLM).flip

lemma prodMk'_apply (f : C(X × Y, R)) : (μ.prodMk' ν) f = μ (ν.contractSnd f) := rfl

lemma prodMk'_flip (f : C(X × Y, R)) :
    (μ.prodMk' ν) f = (ν.prodMk μ) (f.comp ContinuousMap.prodSwap) := rfl

lemma prodMk'_prod_apply (f : C(X, R)) (g : C(Y, R)) :
    prodMk' μ ν ((f.comp .fst) * (g.comp .snd)) = μ f * ν g := by
  simp only [prodMk'_apply, mul_comm (μ f) (ν g), ← smul_eq_mul, ← map_smul]
  congr 1 with x
  simp_rw [ContinuousMap.smul_apply, smul_eq_mul, mul_comm (ν g) (f x), contractSnd_apply,
    ← smul_eq_mul, ← map_smul]
  rfl

end LocallyCompact

section Profinite

variable [CompactSpace X] [CompactSpace Y] [T2Space X] [T2Space Y] [TotallyDisconnectedSpace X]

/-- For profinite spaces, the two product structures on distributions agree. -/
lemma prodMk_eq_prodMk' : prodMk μ ν = prodMk' μ ν := by
  ext f
  rw [← sub_eq_zero, ← norm_le_zero_iff]
  refine le_of_forall_lt' (fun ε hε ↦ ?_)
  have hε2 : 0 < ε / 2 := div_pos hε zero_lt_two
  have := (Metric.continuousAt_iff.mp <| (μ.prodMk ν).continuous.continuousAt (x := f)) _ hε2
  rcases this with ⟨δ, hδ, hhδ⟩
  have := (Metric.continuousAt_iff.mp <| (μ.prodMk' ν).continuous.continuousAt (x := f)) _ hε2
  rcases this with ⟨δ', hδ', hhδ'⟩
  simp only [dist_eq_norm_sub'] at hhδ hhδ'
  obtain ⟨n, G, H, hh⟩ := exists_sum_mul_approx f (Metric.dist_mem_uniformity <| lt_min hδ hδ')
  let T : C(X × Y, R) := ∑ i, (G i).comp .fst * (H i).comp snd
  replace hh : ‖f - T‖ < δ ⊓ δ' := by
    simpa [ContinuousMap.norm_lt_iff _ <| lt_min hδ hδ', T, dist_eq_norm_sub] using hh
  calc
  _ = ‖(prodMk μ ν f - prodMk μ ν T) + (prodMk μ ν T - prodMk' μ ν f)‖ := by abel_nf
  _ ≤ ‖prodMk μ ν f - prodMk μ ν T‖ + ‖prodMk μ ν T - prodMk' μ ν f‖ := norm_add_le _ _
  _ = ‖prodMk μ ν f - prodMk μ ν T‖ + ‖prodMk' μ ν f - prodMk μ ν T‖ := by
    congr 1; rw [norm_sub_rev]
  _ = ‖prodMk μ ν f - prodMk μ ν T‖ + ‖prodMk' μ ν f - prodMk' μ ν T‖ := by
    congr 3
    simp only [T, map_sum]
    congr 1 with i
    rw [prodMk_prod_apply, prodMk'_prod_apply]
  _ < ε := by linarith [hhδ' <| hh.trans_le <| min_le_right δ δ',
                hhδ <| hh.trans_le <| min_le_left δ δ']

end Profinite

end Prod

section Topology

open Topology

section Weak

/--
The weak topology on `AbstractMeasure G R E` (the weakest topology such that `μ ↦ μ f` is
continuous for all `f`).
-/
def WeakTopology : TopologicalSpace (AbstractMeasure X R E) :=
  .induced (fun μ f ↦ μ f) inferInstance

scoped [AbstractMeasure.WeakTopology] attribute [instance] WeakTopology

end Weak

variable [CompactSpace X]

variable -- redeclare instances depending on `R`, because it needs to be *nontrivially* normed now
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

noncomputable instance : Norm (AbstractMeasure X 𝕜 E) :=
  inferInstanceAs (Norm (C(X, 𝕜) →L[𝕜] E))

/-- The strong topology on `AbstractMeasure G 𝕜 E` (the topology induced by the norm). -/
def StrongTopology : TopologicalSpace (AbstractMeasure X 𝕜 E) :=
  inferInstanceAs (TopologicalSpace (C(X, 𝕜) →L[𝕜] E))

end Topology

end AbstractMeasure
