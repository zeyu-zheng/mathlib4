import Mathlib.Tactic.Have
/-
Copyright (c) 2024 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
import Mathlib.Analysis.CstarAlgebra.ContinuousFunctionalCalculus.Restrict
import Mathlib.Analysis.CstarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CstarAlgebra.Spectrum
import Mathlib.Analysis.CstarAlgebra.Unitization
import Mathlib.Analysis.CstarAlgebra.ContinuousFunctionalCalculus.Unique

/-! # Instances of the continuous functional calculus

## Main theorems

* `IsStarNormal.instContinuousFunctionalCalculus`: the continuous functional calculus for normal
  elements in a unital C⋆-algebra over `ℂ`.
* `IsSelfAdjoint.instContinuousFunctionalCalculus`: the continuous functional calculus for
  selfadjoint elements in a `ℂ`-algebra with a continuous functional calculus for normal elements
  and where every element has compact spectrum. In particular, this includes unital C⋆-algebras
  over `ℂ`.
* `Nonneg.instContinuousFunctionalCalculus`: the continuous functional calculus for nonnegative
  elements in an `ℝ`-algebra with a continuous functional calculus for selfadjoint elements,
  where every element has compact spectrum, and where nonnegative elements have nonnegative
  spectrum. In particular, this includes unital C⋆-algebras over `ℝ`.
* `CstarRing.instNonnegSpectrumClass`: In a unital C⋆-algebra over `ℂ` which is also a
  `StarOrderedRing`, the spectrum of a nonnegative element is nonnegative.

## Tags

continuous functional calculus, normal, selfadjoint
-/

noncomputable section

local notation "σₙ" => quasispectrum
local notation "σ" => spectrum

/-!
### Pull back a non-unital instance from a unital one on the unitization
-/

section RCLike

variable {𝕜 A : Type*} [RCLike 𝕜] [NonUnitalNormedRing A] [StarRing A] [CstarRing A]
variable [CompleteSpace A] [NormedSpace 𝕜 A] [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A]
variable [StarModule 𝕜 A] {p : A → Prop} {p₁ : Unitization 𝕜 A → Prop}

local postfix:max "⁺¹" => Unitization 𝕜

variable (hp₁ : ∀ {x : A}, p₁ x ↔ p x) (a : A) (ha : p a)
variable [ContinuousFunctionalCalculus 𝕜 p₁]

open scoped ContinuousMapZero


open Unitization in
/--
This is an auxiliary definition used for constructing an instance of the non-unital continuous
functional calculus given a instance of the unital one on the unitization.

This is the natural non-unital star homomorphism obtained from the chain
```lean
calc
  C(σₙ 𝕜 a, 𝕜)₀ →⋆ₙₐ[𝕜] C(σₙ 𝕜 a, 𝕜) := ContinuousMapZero.toContinuousMapHom
  _             ≃⋆[𝕜] C(σ 𝕜 (↑a : A⁺¹), 𝕜) := Homeomorph.compStarAlgEquiv'
  _             →⋆ₐ[𝕜] A⁺¹ := cfcHom
```
This range of this map is contained in the range of `(↑) : A → A⁺¹` (see `cfcₙAux_mem_range_inr`),
and so we may restrict it to `A` to get the necessary homomorphism for the non-unital continuous
functional calculus.
-/
noncomputable def cfcₙAux : C(σₙ 𝕜 a, 𝕜)₀ →⋆ₙₐ[𝕜] A⁺¹ :=
  (cfcHom (R := 𝕜) (hp₁.mpr ha) : C(σ 𝕜 (a : A⁺¹), 𝕜) →⋆ₙₐ[𝕜] A⁺¹) |>.comp
    (Homeomorph.compStarAlgEquiv' 𝕜 𝕜 <| .setCongr <| (quasispectrum_eq_spectrum_inr' 𝕜 𝕜 a).symm)
    |>.comp ContinuousMapZero.toContinuousMapHom

lemma cfcₙAux_id : cfcₙAux hp₁ a ha (ContinuousMapZero.id rfl) = a := cfcHom_id (hp₁.mpr ha)

open Unitization in
lemma closedEmbedding_cfcₙAux : ClosedEmbedding (cfcₙAux hp₁ a ha) := by
  simp only [cfcₙAux, NonUnitalStarAlgHom.coe_comp]
  refine ((cfcHom_closedEmbedding (hp₁.mpr ha)).comp ?_).comp
    ContinuousMapZero.closedEmbedding_toContinuousMap
  let e : C(σₙ 𝕜 a, 𝕜) ≃ₜ C(σ 𝕜 (a : A⁺¹), 𝕜) :=
    { (Homeomorph.compStarAlgEquiv' 𝕜 𝕜 <| .setCongr <|
        (quasispectrum_eq_spectrum_inr' 𝕜 𝕜 a).symm) with
      continuous_toFun := ContinuousMap.continuous_comp_left _
      continuous_invFun := ContinuousMap.continuous_comp_left _ }
  exact e.closedEmbedding

lemma spec_cfcₙAux (f : C(σₙ 𝕜 a, 𝕜)₀) : σ 𝕜 (cfcₙAux hp₁ a ha f) = Set.range f := by
  rw [cfcₙAux, NonUnitalStarAlgHom.comp_assoc, NonUnitalStarAlgHom.comp_apply]
  simp only [NonUnitalStarAlgHom.comp_apply, NonUnitalStarAlgHom.coe_coe]
  rw [cfcHom_map_spectrum (hp₁.mpr ha) (R := 𝕜) _]
  ext x
  constructor
  all_goals rintro ⟨x, rfl⟩
  exact ⟨⟨x, (Unitization.quasispectrum_eq_spectrum_inr' 𝕜 𝕜 a).symm ▸ x.property⟩, rfl⟩
  exact ⟨⟨x, Unitization.quasispectrum_eq_spectrum_inr' 𝕜 𝕜 a ▸ x.property⟩, rfl⟩

lemma cfcₙAux_mem_range_inr (f : C(σₙ 𝕜 a, 𝕜)₀) :
    cfcₙAux hp₁ a ha f ∈ NonUnitalStarAlgHom.range (Unitization.inrNonUnitalStarAlgHom 𝕜 A) := by
  have h₁ := (closedEmbedding_cfcₙAux hp₁ a ha).continuous.range_subset_closure_image_dense
    (ContinuousMapZero.adjoin_id_dense (s := σₙ 𝕜 a) rfl) ⟨f, rfl⟩
  rw [← SetLike.mem_coe]
  refine closure_minimal ?_ ?_ h₁
  rw [← NonUnitalStarSubalgebra.coe_map, SetLike.coe_subset_coe, NonUnitalStarSubalgebra.map_le]
  apply NonUnitalStarAlgebra.adjoin_le
  apply Set.singleton_subset_iff.mpr
  rw [SetLike.mem_coe, NonUnitalStarSubalgebra.mem_comap, cfcₙAux_id hp₁ a ha]
  exact ⟨a, rfl⟩
  have : Continuous (Unitization.fst (R := 𝕜) (A := A)) :=
    Unitization.uniformEquivProd.continuous.fst
  simp only [NonUnitalStarAlgHom.coe_range]
  convert IsClosed.preimage this (isClosed_singleton (x := 0))
  aesop

open Unitization NonUnitalStarAlgHom in
theorem RCLike.nonUnitalContinuousFunctionalCalculus :
    NonUnitalContinuousFunctionalCalculus 𝕜 (p : A → Prop) where
  predicate_zero := by
    rw [← hp₁, Unitization.inr_zero 𝕜]
    exact cfc_predicate_zero 𝕜
  exists_cfc_of_predicate a ha := by
    let ψ : C(σₙ 𝕜 a, 𝕜)₀ →⋆ₙₐ[𝕜] A := comp (inrRangeEquiv 𝕜 A).symm <|
      codRestrict (cfcₙAux hp₁ a ha) _ (cfcₙAux_mem_range_inr hp₁ a ha)
    have coe_ψ (f : C(σₙ 𝕜 a, 𝕜)₀) : ψ f = cfcₙAux hp₁ a ha f :=
      congr_arg Subtype.val <| (inrRangeEquiv 𝕜 A).apply_symm_apply
        ⟨cfcₙAux hp₁ a ha f, cfcₙAux_mem_range_inr hp₁ a ha f⟩
    refine ⟨ψ, ?closedEmbedding, ?map_id, fun f ↦ ?map_spec, fun f ↦ ?isStarNormal⟩
    case closedEmbedding =>
      apply isometry_inr (𝕜 := 𝕜) (A := A) |>.closedEmbedding |>.of_comp_iff.mp
      have : inr ∘ ψ = cfcₙAux hp₁ a ha := by ext1; rw [Function.comp_apply, coe_ψ]
      exact this ▸ closedEmbedding_cfcₙAux hp₁ a ha
    case map_id => exact inr_injective (R := 𝕜) <| coe_ψ _ ▸ cfcₙAux_id hp₁ a ha
    case map_spec =>
      exact quasispectrum_eq_spectrum_inr' 𝕜 𝕜 (ψ f) ▸ coe_ψ _ ▸ spec_cfcₙAux hp₁ a ha f
    case isStarNormal => exact hp₁.mp <| coe_ψ _ ▸ cfcHom_predicate (R := 𝕜) (hp₁.mpr ha) _

end RCLike

/-!
### Continuous functional calculus for normal elements
-/

section Normal

instance IsStarNormal.instContinuousFunctionalCalculus {A : Type*} [NormedRing A] [StarRing A]
    [CstarRing A] [CompleteSpace A] [NormedAlgebra ℂ A] [StarModule ℂ A] :
    ContinuousFunctionalCalculus ℂ (IsStarNormal : A → Prop) where
  predicate_zero := isStarNormal_zero
  exists_cfc_of_predicate a ha := by
    refine ⟨(elementalStarAlgebra ℂ a).subtype.comp <| continuousFunctionalCalculus a,
      ?hom_closedEmbedding, ?hom_id, ?hom_map_spectrum, ?predicate_hom⟩
    case hom_closedEmbedding => exact Isometry.closedEmbedding <|
      isometry_subtype_coe.comp <| StarAlgEquiv.isometry (continuousFunctionalCalculus a)
    case hom_id => exact congr_arg Subtype.val <| continuousFunctionalCalculus_map_id a
    case hom_map_spectrum =>
      intro f
      simp only [StarAlgHom.comp_apply, StarAlgHom.coe_coe, StarSubalgebra.coe_subtype]
      rw [← StarSubalgebra.spectrum_eq (elementalStarAlgebra.isClosed ℂ a),
        AlgEquiv.spectrum_eq (continuousFunctionalCalculus a), ContinuousMap.spectrum_eq_range]
    case predicate_hom => exact fun f ↦ ⟨by rw [← map_star]; exact Commute.all (star f) f |>.map _⟩

instance IsStarNormal.instNonUnitalContinuousFunctionalCalculus {A : Type*} [NonUnitalNormedRing A]
    [StarRing A] [CstarRing A] [CompleteSpace A] [NormedSpace ℂ A] [IsScalarTower ℂ A A]
    [SMulCommClass ℂ A A] [StarModule ℂ A] :
    NonUnitalContinuousFunctionalCalculus ℂ (IsStarNormal : A → Prop) :=
  RCLike.nonUnitalContinuousFunctionalCalculus Unitization.isStarNormal_inr

instance IsStarNormal.cfcₙ_map {R A : Type*} {p : A → Prop} [CommSemiring R] [StarRing R]
    [MetricSpace R] [TopologicalSemiring R] [ContinuousStar R] [Nontrivial R] [TopologicalSpace A]
    [NonUnitalRing A] [StarRing A] [Module R A] [IsScalarTower R A A] [SMulCommClass R A A]
    [NonUnitalContinuousFunctionalCalculus R p] (a : A) (f : R → R) :
    IsStarNormal (cfcₙ f a) where
  star_comm_self := by
    refine cfcₙ_cases (fun x ↦ Commute (star x) x) _ _ (Commute.zero_right _) fun _ _ _ ↦ ?_
    simp only [Commute, SemiconjBy]
    rw [← cfcₙ_apply f a, ← cfcₙ_star, ← cfcₙ_mul .., ← cfcₙ_mul ..]
    congr! 2
    exact mul_comm _ _

instance IsStarNormal.cfc_map {R A : Type*} {p : A → Prop} [CommSemiring R] [StarRing R]
    [MetricSpace R] [TopologicalSemiring R] [ContinuousStar R] [TopologicalSpace A] [Ring A]
    [StarRing A] [Algebra R A] [ContinuousFunctionalCalculus R p] (a : A) (f : R → R) :
    IsStarNormal (cfc f a) where
  star_comm_self := by
    rw [Commute, SemiconjBy]
    by_cases h : ContinuousOn f (spectrum R a)
    rw [← cfc_star, ← cfc_mul .., ← cfc_mul ..]
    congr! 2
    exact mul_comm _ _
    simp [cfc_apply_of_not_continuousOn a h]
end Normal

/-!
### Continuous functional calculus for selfadjoint elements
-/

section SelfAdjointNonUnital

variable {A : Type*} [TopologicalSpace A] [NonUnitalRing A] [StarRing A] [Module ℂ A]
  [IsScalarTower ℂ A A] [SMulCommClass ℂ A A] [StarModule ℂ A]
  [NonUnitalContinuousFunctionalCalculus ℂ (IsStarNormal : A → Prop)]

/-- An element in a non-unital C⋆-algebra is selfadjoint if and only if it is normal and its
quasispectrum is contained in `ℝ`. -/
lemma isSelfAdjoint_iff_isStarNormal_and_quasispectrumRestricts {a : A} :
    IsSelfAdjoint a ↔ IsStarNormal a ∧ QuasispectrumRestricts a Complex.reCLM := by
  refine ⟨fun ha ↦ ⟨ha.isStarNormal, ⟨fun x hx ↦ ?_, Complex.ofReal_re⟩⟩, ?_⟩
  have := eqOn_of_cfcₙ_eq_cfcₙ <|
    (cfcₙ_star (id : ℂ → ℂ) a).symm ▸ (cfcₙ_id ℂ a).symm ▸ ha.star_eq
  exact Complex.conj_eq_iff_re.mp (by simpa using this hx)
  rintro ⟨ha₁, ha₂⟩
  rw [isSelfAdjoint_iff]
  nth_rw 2 [← cfcₙ_id ℂ a]
  rw [← cfcₙ_star_id a (R := ℂ)]
  refine cfcₙ_congr fun x hx ↦ ?_
  obtain ⟨x, -, rfl⟩ := ha₂.algebraMap_image.symm ▸ hx
  exact Complex.conj_ofReal _

alias ⟨IsSelfAdjoint.quasispectrumRestricts, _⟩ :=
  isSelfAdjoint_iff_isStarNormal_and_quasispectrumRestricts

/-- A normal element whose `ℂ`-quasispectrum is contained in `ℝ` is selfadjoint. -/
lemma QuasispectrumRestricts.isSelfAdjoint (a : A) (ha : QuasispectrumRestricts a Complex.reCLM)
    [IsStarNormal a] : IsSelfAdjoint a :=
  isSelfAdjoint_iff_isStarNormal_and_quasispectrumRestricts.mpr ⟨‹_›, ha⟩

instance IsSelfAdjoint.instNonUnitalContinuousFunctionalCalculus
    [∀ x : A, CompactSpace (σₙ ℂ x)] :
    NonUnitalContinuousFunctionalCalculus ℝ (IsSelfAdjoint : A → Prop) :=
  QuasispectrumRestricts.cfc (q := IsStarNormal) (p := IsSelfAdjoint) Complex.reCLM
    Complex.isometry_ofReal.uniformEmbedding (.zero _)
    (fun _ ↦ isSelfAdjoint_iff_isStarNormal_and_quasispectrumRestricts)
    (fun _ _ ↦ inferInstance)

end SelfAdjointNonUnital

section SelfAdjointUnital


variable {A : Type*} [TopologicalSpace A] [Ring A] [StarRing A] [Algebra ℂ A]
  [StarModule ℂ A] [ContinuousFunctionalCalculus ℂ (IsStarNormal : A → Prop)]

/-
TODO: REMOVE
this is a duplicate of `isSelfAdjoint_iff_isStarNormal_and_quasispectrumRestricts`, because of
`abbrev SpectrumRestricts := QuasispectrumRestricts` but we first need unital-to-non-unital
instance)
-/
/-- An element in a C⋆-algebra is selfadjoint if and only if it is normal and its spectrum is
contained in `ℝ`. -/
lemma isSelfAdjoint_iff_isStarNormal_and_spectrumRestricts {a : A} :
    IsSelfAdjoint a ↔ IsStarNormal a ∧ SpectrumRestricts a Complex.reCLM := by
  refine ⟨fun ha ↦ ⟨ha.isStarNormal, .of_rightInvOn Complex.ofReal_re fun x hx ↦ ?_⟩, ?_⟩
  have := eqOn_of_cfc_eq_cfc <| (cfc_star (id : ℂ → ℂ) a).symm ▸ (cfc_id ℂ a).symm ▸ ha.star_eq
  exact Complex.conj_eq_iff_re.mp (by simpa using this hx)
  rintro ⟨ha₁, ha₂⟩
  rw [isSelfAdjoint_iff]
  nth_rw 2 [← cfc_id ℂ a]
  rw [← cfc_star_id a (R := ℂ)]
  refine cfc_congr fun x hx ↦ ?_
  obtain ⟨x, -, rfl⟩ := ha₂.algebraMap_image.symm ▸ hx
  exact Complex.conj_ofReal _

-- TODO: REMOVE (duplicate; see comment on `isSelfAdjoint_iff_isStarNormal_and_spectrumRestricts`)
lemma IsSelfAdjoint.spectrumRestricts {a : A} (ha : IsSelfAdjoint a) :
    SpectrumRestricts a Complex.reCLM :=
  isSelfAdjoint_iff_isStarNormal_and_spectrumRestricts.mp ha |>.right

-- TODO: REMOVE (duplicate; see comment on `isSelfAdjoint_iff_isStarNormal_and_spectrumRestricts`)
/-- A normal element whose `ℂ`-spectrum is contained in `ℝ` is selfadjoint. -/
lemma SpectrumRestricts.isSelfAdjoint (a : A) (ha : SpectrumRestricts a Complex.reCLM)
    [IsStarNormal a] : IsSelfAdjoint a :=
  isSelfAdjoint_iff_isStarNormal_and_spectrumRestricts.mpr ⟨‹_›, ha⟩

instance IsSelfAdjoint.instContinuousFunctionalCalculus [∀ x : A, CompactSpace (spectrum ℂ x)] :
    ContinuousFunctionalCalculus ℝ (IsSelfAdjoint : A → Prop) :=
  SpectrumRestricts.cfc (q := IsStarNormal) (p := IsSelfAdjoint) Complex.reCLM
    Complex.isometry_ofReal.uniformEmbedding (.zero _)
    (fun _ ↦ isSelfAdjoint_iff_isStarNormal_and_spectrumRestricts)
    (fun _ _ ↦ inferInstance)

end SelfAdjointUnital

/-!
### Continuous functional calculus for nonnegative elements
-/

section Nonneg

lemma CFC.exists_sqrt_of_isSelfAdjoint_of_quasispectrumRestricts {A : Type*} [NonUnitalRing A]
    [StarRing A] [TopologicalSpace A] [Module ℝ A] [IsScalarTower ℝ A A] [SMulCommClass ℝ A A ]
    [NonUnitalContinuousFunctionalCalculus ℝ (IsSelfAdjoint : A → Prop)]
    {a : A} (ha₁ : IsSelfAdjoint a) (ha₂ : QuasispectrumRestricts a ContinuousMap.realToNNReal) :
    ∃ x : A, IsSelfAdjoint x ∧ QuasispectrumRestricts x ContinuousMap.realToNNReal ∧ x * x = a := by
  use cfcₙ Real.sqrt a, cfcₙ_predicate Real.sqrt a
  constructor
  simpa only [QuasispectrumRestricts.nnreal_iff, cfcₙ_map_quasispectrum Real.sqrt a,
    Set.mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
      using fun x _ ↦ Real.sqrt_nonneg x
  rw [← cfcₙ_mul ..]
  nth_rw 2 [← cfcₙ_id ℝ a]
  apply cfcₙ_congr fun x hx ↦ ?_
  rw [QuasispectrumRestricts.nnreal_iff] at ha₂
  apply ha₂ x at hx
  simp [← sq, Real.sq_sqrt hx]

variable {A : Type*} [NonUnitalRing A] [PartialOrder A] [StarRing A] [StarOrderedRing A]
variable [TopologicalSpace A] [Module ℝ A] [IsScalarTower ℝ A A] [SMulCommClass ℝ A A]
variable [NonUnitalContinuousFunctionalCalculus ℝ (IsSelfAdjoint : A → Prop)]
variable [NonnegSpectrumClass ℝ A] [UniqueNonUnitalContinuousFunctionalCalculus ℝ A]

lemma nonneg_iff_isSelfAdjoint_and_quasispectrumRestricts {a : A} :
    0 ≤ a ↔ IsSelfAdjoint a ∧ QuasispectrumRestricts a ContinuousMap.realToNNReal := by
  refine ⟨fun ha ↦ ⟨.of_nonneg ha, .nnreal_of_nonneg ha⟩, ?_⟩
  rintro ⟨ha₁, ha₂⟩
  obtain ⟨x, hx, -, rfl⟩ := CFC.exists_sqrt_of_isSelfAdjoint_of_quasispectrumRestricts ha₁ ha₂
  simpa [sq, hx.star_eq] using star_mul_self_nonneg x

open NNReal in
instance Nonneg.instNonUnitalContinuousFunctionalCalculus [∀ a : A, CompactSpace (σₙ ℝ a)] :
    NonUnitalContinuousFunctionalCalculus ℝ≥0 (fun x : A ↦ 0 ≤ x) :=
  QuasispectrumRestricts.cfc (q := IsSelfAdjoint) ContinuousMap.realToNNReal
    uniformEmbedding_subtype_val le_rfl
    (fun _ ↦ nonneg_iff_isSelfAdjoint_and_quasispectrumRestricts)
    (fun _ _ ↦ inferInstance)

end Nonneg


section Nonneg

-- TODO: REMOVE (duplicate; see comment on `isSelfAdjoint_iff_isStarNormal_and_spectrumRestricts`)
lemma CFC.exists_sqrt_of_isSelfAdjoint_of_spectrumRestricts {A : Type*} [Ring A] [StarRing A]
    [TopologicalSpace A] [Algebra ℝ A] [ContinuousFunctionalCalculus ℝ (IsSelfAdjoint : A → Prop)]
    {a : A} (ha₁ : IsSelfAdjoint a) (ha₂ : SpectrumRestricts a ContinuousMap.realToNNReal) :
    ∃ x : A, IsSelfAdjoint x ∧ SpectrumRestricts x ContinuousMap.realToNNReal ∧ x ^ 2 = a := by
  use cfc Real.sqrt a, cfc_predicate Real.sqrt a
  constructor
  simpa only [SpectrumRestricts.nnreal_iff, cfc_map_spectrum Real.sqrt a, Set.mem_image,
    forall_exists_index, and_imp, forall_apply_eq_imp_iff₂] using fun x _ ↦ Real.sqrt_nonneg x
  rw [← cfc_pow ..]
  nth_rw 2 [← cfc_id ℝ a]
  apply cfc_congr fun x hx ↦ ?_
  rw [SpectrumRestricts.nnreal_iff] at ha₂
  apply ha₂ x at hx
  simp [Real.sq_sqrt hx]

variable {A : Type*} [Ring A] [PartialOrder A] [StarRing A] [StarOrderedRing A] [TopologicalSpace A]
variable [Algebra ℝ A] [ContinuousFunctionalCalculus ℝ (IsSelfAdjoint : A → Prop)]
variable [NonnegSpectrumClass ℝ A] [UniqueContinuousFunctionalCalculus ℝ A]

-- TODO: REMOVE (duplicate; see comment on `isSelfAdjoint_iff_isStarNormal_and_spectrumRestricts`)
lemma nonneg_iff_isSelfAdjoint_and_spectrumRestricts {a : A} :
    0 ≤ a ↔ IsSelfAdjoint a ∧ SpectrumRestricts a ContinuousMap.realToNNReal := by
  refine ⟨fun ha ↦ ⟨.of_nonneg ha, .nnreal_of_nonneg ha⟩, ?_⟩
  rintro ⟨ha₁, ha₂⟩
  obtain ⟨x, hx, -, rfl⟩ := CFC.exists_sqrt_of_isSelfAdjoint_of_spectrumRestricts ha₁ ha₂
  simpa [sq, hx.star_eq] using star_mul_self_nonneg x

open NNReal in
instance Nonneg.instContinuousFunctionalCalculus [∀ a : A, CompactSpace (spectrum ℝ a)] :
    ContinuousFunctionalCalculus ℝ≥0 (fun x : A ↦ 0 ≤ x) :=
  SpectrumRestricts.cfc (q := IsSelfAdjoint) ContinuousMap.realToNNReal
    uniformEmbedding_subtype_val le_rfl (fun _ ↦ nonneg_iff_isSelfAdjoint_and_spectrumRestricts)
    (fun _ _ ↦ inferInstance)

end Nonneg

/-!
### The spectrum of a nonnegative element is nonnegative
-/

section SpectrumRestricts

open NNReal ENNReal

variable {A : Type*} [NormedRing A] [StarRing A] [CstarRing A] [CompleteSpace A]
variable [NormedAlgebra ℂ A] [StarModule ℂ A]

lemma SpectrumRestricts.nnreal_iff_nnnorm {a : A} {t : ℝ≥0} (ha : IsSelfAdjoint a) (ht : ‖a‖₊ ≤ t) :
    SpectrumRestricts a ContinuousMap.realToNNReal ↔ ‖algebraMap ℝ A t - a‖₊ ≤ t := by
  have : IsSelfAdjoint (algebraMap ℝ A t - a) := IsSelfAdjoint.algebraMap A (.all (t : ℝ)) |>.sub ha
  rw [← ENNReal.coe_le_coe, ← IsSelfAdjoint.spectralRadius_eq_nnnorm,
    ← SpectrumRestricts.spectralRadius_eq (f := Complex.reCLM)] at ht ⊢
  exact SpectrumRestricts.nnreal_iff_spectralRadius_le ht
  all_goals
    try apply IsSelfAdjoint.spectrumRestricts
    assumption

lemma SpectrumRestricts.nnreal_add {a b : A} (ha₁ : IsSelfAdjoint a)
    (hb₁ : IsSelfAdjoint b) (ha₂ : SpectrumRestricts a ContinuousMap.realToNNReal)
    (hb₂ : SpectrumRestricts b ContinuousMap.realToNNReal) :
    SpectrumRestricts (a + b) ContinuousMap.realToNNReal := by
  rw [SpectrumRestricts.nnreal_iff_nnnorm (ha₁.add hb₁) (nnnorm_add_le a b), NNReal.coe_add,
    map_add, add_sub_add_comm]
  refine nnnorm_add_le _ _ |>.trans ?_
  gcongr
  all_goals rw [← SpectrumRestricts.nnreal_iff_nnnorm] <;> first | rfl | assumption

lemma IsSelfAdjoint.sq_spectrumRestricts {a : A} (ha : IsSelfAdjoint a) :
    SpectrumRestricts (a ^ 2) ContinuousMap.realToNNReal := by
  rw [SpectrumRestricts.nnreal_iff, ← cfc_id (R := ℝ) a, ← cfc_pow .., cfc_map_spectrum ..]
  rintro - ⟨x, -, rfl⟩
  exact sq_nonneg x

open ComplexStarModule

lemma SpectrumRestricts.eq_zero_of_neg {a : A} (ha : IsSelfAdjoint a)
    (ha₁ : SpectrumRestricts a ContinuousMap.realToNNReal)
    (ha₂ : SpectrumRestricts (-a) ContinuousMap.realToNNReal) :
    a = 0 := by
  nontriviality A
  rw [SpectrumRestricts.nnreal_iff] at ha₁ ha₂
  apply CFC.eq_zero_of_spectrum_subset_zero (R := ℝ) a
  rw [Set.subset_singleton_iff]
  simp only [← spectrum.neg_eq, Set.mem_neg] at ha₂
  peel ha₁ with x hx _
  linarith [ha₂ (-x) ((neg_neg x).symm ▸ hx)]

lemma SpectrumRestricts.smul_of_nonneg {A : Type*} [Ring A] [Algebra ℝ A] {a : A}
    (ha : SpectrumRestricts a ContinuousMap.realToNNReal) {r : ℝ} (hr : 0 ≤ r) :
    SpectrumRestricts (r • a) ContinuousMap.realToNNReal := by
  rw [SpectrumRestricts.nnreal_iff] at ha ⊢
  nontriviality A
  intro x hx
  by_cases hr' : r = 0
  simp [hr'] at hx ⊢
  exact hx.symm.le
  lift r to ℝˣ using IsUnit.mk0 r hr'
  rw [← Units.smul_def, spectrum.unit_smul_eq_smul, Set.mem_smul_set_iff_inv_smul_mem] at hx
  refine le_of_smul_le_smul_left ?_ (inv_pos.mpr <| lt_of_le_of_ne hr <| ne_comm.mpr hr')
  simpa [Units.smul_def] using ha _ hx

lemma spectrum_star_mul_self_nonneg {b : A} : ∀ x ∈ spectrum ℝ (star b * b), 0 ≤ x := by
  set a := star b * b
  have a_def : a = star b * b := rfl
  let a_neg : A := cfc (fun x ↦ (- ContinuousMap.id ℝ ⊔ 0) x) a
  set c := b * a_neg
  have h_eq_a_neg : - (star c * c) = a_neg ^ 3 := by
    simp only [c, a_neg, star_mul]
    rw [← mul_assoc, mul_assoc _ _ b, ← cfc_star, ← cfc_id' ℝ (star b * b), a_def, ← neg_mul]
    rw [← cfc_mul _ _ (star b * b) (by simp; fun_prop), neg_mul]
    simp only [ContinuousMap.coe_neg, ContinuousMap.coe_id, Pi.sup_apply, Pi.neg_apply,
      star_trivial]
    rw [← cfc_mul .., ← cfc_neg .., ← cfc_pow ..]
    congr
    ext x
    by_cases hx : x ≤ 0
    · rw [← neg_nonneg] at hx
      simp [sup_eq_left.mpr hx, pow_succ]
    · rw [not_le, ← neg_neg_iff_pos] at hx
      simp [sup_eq_right.mpr hx.le]
  have h_c_spec₀ : SpectrumRestricts (- (star c * c)) (ContinuousMap.realToNNReal ·) := by
    simp only [SpectrumRestricts.nnreal_iff, h_eq_a_neg]
    rw [← cfc_pow _ _ (ha := .star_mul_self b)]
    simp only [cfc_map_spectrum (R := ℝ) (fun x => (-ContinuousMap.id ℝ ⊔ 0) x ^ 3) (star b * b)]
    rintro - ⟨x, -, rfl⟩
    simp
  have c_eq := star_mul_self_add_self_mul_star c
  rw [← eq_sub_iff_add_eq', sub_eq_add_neg, ← sq, ← sq] at c_eq
  have h_c_spec₁ : SpectrumRestricts (c * star c) ContinuousMap.realToNNReal := by
    rw [c_eq]
    refine SpectrumRestricts.nnreal_add ?_ ?_ ?_ h_c_spec₀
    · exact IsSelfAdjoint.smul (by rfl) <| ((ℜ c).prop.pow 2).add ((ℑ c).prop.pow 2)
    · exact (IsSelfAdjoint.star_mul_self c).neg
    · rw [← Nat.cast_smul_eq_nsmul ℝ]
      refine (ℜ c).2.sq_spectrumRestricts.nnreal_add ((ℜ c).2.pow 2) ((ℑ c).2.pow 2)
        (ℑ c).2.sq_spectrumRestricts |>.smul_of_nonneg <| by norm_num
  have h_c_spec₂ : SpectrumRestricts (star c * c) ContinuousMap.realToNNReal := by
    rw [SpectrumRestricts.nnreal_iff] at h_c_spec₁ ⊢
    intro x hx
    replace hx := Set.subset_diff_union _ {(0 : ℝ)} hx
    rw [spectrum.nonzero_mul_eq_swap_mul, Set.diff_union_self, Set.union_singleton,
      Set.mem_insert_iff] at hx
    obtain (rfl | hx) := hx
    exacts [le_rfl, h_c_spec₁ x hx]
  rw [h_c_spec₂.eq_zero_of_neg (.star_mul_self c) h_c_spec₀, neg_zero] at h_eq_a_neg
  simp only [a_neg] at h_eq_a_neg
  rw [← cfc_pow _ _ (ha := .star_mul_self b), ← cfc_zero a (R := ℝ)] at h_eq_a_neg
  intro x hx
  by_contra! hx'
  rw [← neg_pos] at hx'
  apply (pow_pos hx' 3).ne
  have h_eqOn := eqOn_of_cfc_eq_cfc (ha := IsSelfAdjoint.star_mul_self b) h_eq_a_neg
  simpa [sup_eq_left.mpr hx'.le] using h_eqOn hx

lemma IsSelfAdjoint.coe_mem_spectrum_complex {A : Type*} [TopologicalSpace A] [Ring A]
    [StarRing A] [Algebra ℂ A] [ContinuousFunctionalCalculus ℂ (IsStarNormal : A → Prop)]
    {a : A} {x : ℝ} (ha : IsSelfAdjoint a := by cfc_tac) :
    (x : ℂ) ∈ spectrum ℂ a ↔ x ∈ spectrum ℝ a := by
  simp [← ha.spectrumRestricts.algebraMap_image]

end SpectrumRestricts

section NonnegSpectrumClass

variable {A : Type*} [NormedRing A] [CompleteSpace A]
variable [PartialOrder A] [StarRing A] [StarOrderedRing A] [CstarRing A]
variable [NormedAlgebra ℂ A] [StarModule ℂ A]

instance CstarRing.instNonnegSpectrumClass : NonnegSpectrumClass ℝ A :=
  .of_spectrum_nonneg fun a ha ↦ by
    rw [StarOrderedRing.nonneg_iff] at ha
    induction ha using AddSubmonoid.closure_induction' with
    | mem x hx =>
      obtain ⟨b, rfl⟩ := hx
      exact spectrum_star_mul_self_nonneg
    | one =>
      nontriviality A
      simp
    | mul x x_mem y y_mem hx hy =>
      rw [← SpectrumRestricts.nnreal_iff] at hx hy ⊢
      rw [← StarOrderedRing.nonneg_iff] at x_mem y_mem
      exact hx.nnreal_add (.of_nonneg x_mem) (.of_nonneg y_mem) hy

open ComplexOrder in
instance CstarRing.instNonnegSpectrumClassComplexUnital : NonnegSpectrumClass ℂ A where
  quasispectrum_nonneg_of_nonneg a ha x := by
    rw [mem_quasispectrum_iff]
    refine (Or.elim · ge_of_eq fun hx ↦ ?_)
    obtain ⟨y, hy, rfl⟩ := (IsSelfAdjoint.of_nonneg ha).spectrumRestricts.algebraMap_image ▸ hx
    simpa using spectrum_nonneg_of_nonneg ha hy

end NonnegSpectrumClass

section SpectralOrder

variable (A : Type*) [NormedRing A] [CompleteSpace A] [StarRing A] [CstarRing A]
variable [NormedAlgebra ℂ A] [StarModule ℂ A]

/-- The partial order on a unital C⋆-algebra defined by `x ≤ y` if and only if `y - x` is
selfadjoint and has nonnegative spectrum.

This is not declared as an instance because one may already have a partial order with better
definitional properties. However, it can be useful to invoke this as an instance in proofs. -/
@[reducible]
def CstarRing.spectralOrder : PartialOrder A where
  le x y := IsSelfAdjoint (y - x) ∧ SpectrumRestricts (y - x) ContinuousMap.realToNNReal
  le_refl := by
    simp only [sub_self, IsSelfAdjoint.zero, true_and, forall_const]
    rw [SpectrumRestricts.nnreal_iff]
    nontriviality A
    simp
  le_antisymm x y hxy hyx := by
    rw [← sub_eq_zero]
    exact hyx.2.eq_zero_of_neg hyx.1 (neg_sub x y ▸ hxy.2)
  le_trans x y z hxy hyz :=
    ⟨by simpa using hyz.1.add hxy.1, by simpa using hyz.2.nnreal_add hyz.1 hxy.1 hxy.2⟩

/-- The `CstarRing.spectralOrder` on a unital C⋆-algebra is a `StarOrderedRing`. -/
lemma CstarRing.spectralOrderedRing : @StarOrderedRing A _ (CstarRing.spectralOrder A) _ :=
  let _ := CstarRing.spectralOrder A
  { le_iff := by
      intro x y
      constructor
      intro h
      obtain ⟨s, hs₁, _, hs₂⟩ := CFC.exists_sqrt_of_isSelfAdjoint_of_spectrumRestricts h.1 h.2
      refine ⟨s ^ 2, ?_, by rwa [eq_sub_iff_add_eq', eq_comm] at hs₂⟩
      exact AddSubmonoid.subset_closure ⟨s, by simp [hs₁.star_eq, sq]⟩
      rintro ⟨p, hp, rfl⟩
      suffices IsSelfAdjoint p ∧ SpectrumRestricts p ContinuousMap.realToNNReal from
        ⟨by simpa using this.1, by simpa using this.2⟩
      induction hp using AddSubmonoid.closure_induction' with
      | mem x hx =>
        obtain ⟨s, rfl⟩ := hx
        refine ⟨IsSelfAdjoint.star_mul_self s, ?_⟩
        rw [SpectrumRestricts.nnreal_iff]
        exact spectrum_star_mul_self_nonneg
      | one =>
        rw [SpectrumRestricts.nnreal_iff]
        nontriviality A
        simp
      | mul x _ y _ hx hy =>
        exact ⟨hx.1.add hy.1, hx.2.nnreal_add hx.1 hy.1 hy.2⟩ }

end SpectralOrder

section NonnegSpectrumClass

variable {A : Type*} [NonUnitalNormedRing A] [CompleteSpace A]
variable [PartialOrder A] [StarRing A] [StarOrderedRing A] [CstarRing A]
variable [NormedSpace ℂ A] [IsScalarTower ℂ A A] [SMulCommClass ℂ A A] [StarModule ℂ A]

instance CstarRing.instNonnegSpectrumClass' : NonnegSpectrumClass ℝ A where
  quasispectrum_nonneg_of_nonneg a ha := by
    rw [Unitization.quasispectrum_eq_spectrum_inr' _ ℂ]
    -- should this actually be an instance on the `Unitization`? (probably scoped)
    let _ := CstarRing.spectralOrder (Unitization ℂ A)
    have := CstarRing.spectralOrderedRing (Unitization ℂ A)
    apply spectrum_nonneg_of_nonneg
    rw [StarOrderedRing.nonneg_iff] at ha ⊢
    have := AddSubmonoid.mem_map_of_mem (Unitization.inrNonUnitalStarAlgHom ℂ A) ha
    rw [AddMonoidHom.map_mclosure, ← Set.range_comp] at this
    apply AddSubmonoid.closure_mono ?_ this
    rintro _ ⟨s, rfl⟩
    exact ⟨s, by simp⟩

end NonnegSpectrumClass

/-!
### The restriction of a continuous functional calculus is equal to the original one
-/
section RealEqComplex

variable {A : Type*} [TopologicalSpace A] [Ring A] [StarRing A] [Algebra ℂ A]
  [StarModule ℂ A] [ContinuousFunctionalCalculus ℂ (IsStarNormal : A → Prop)]
  [ContinuousFunctionalCalculus ℝ (IsSelfAdjoint : A → Prop)]
  [UniqueContinuousFunctionalCalculus ℝ A]
  [UniqueContinuousFunctionalCalculus ℂ A]

lemma cfcHom_real_eq_restrict {a : A} (ha : IsSelfAdjoint a) :
    cfcHom ha = ha.spectrumRestricts.starAlgHom (cfcHom ha.isStarNormal) (f := Complex.reCLM) :=
  have := UniqueContinuousFunctionalCalculus.compactSpace_spectrum a (R := ℂ)
  ha.spectrumRestricts.cfcHom_eq_restrict Complex.isometry_ofReal.uniformEmbedding
    ha ha.isStarNormal

lemma cfc_real_eq_complex {a : A} (f : ℝ → ℝ) (ha : IsSelfAdjoint a := by cfc_tac)  :
    cfc f a = cfc (fun x ↦ f x.re : ℂ → ℂ) a := by
  have := UniqueContinuousFunctionalCalculus.compactSpace_spectrum a (R := ℂ)
  replace ha : IsSelfAdjoint a := ha -- hack to avoid issues caused by autoParam
  exact ha.spectrumRestricts.cfc_eq_restrict (f := Complex.reCLM)
    Complex.isometry_ofReal.uniformEmbedding ha ha.isStarNormal f

end RealEqComplex

section NNRealEqReal

open NNReal

variable {A : Type*} [TopologicalSpace A] [Ring A] [PartialOrder A] [StarRing A]
  [StarOrderedRing A] [Algebra ℝ A] [TopologicalRing A] [ContinuousStar A] [StarModule ℝ A]
  [ContinuousFunctionalCalculus ℝ (IsSelfAdjoint : A → Prop)]
  [ContinuousFunctionalCalculus ℝ≥0 ((0 : A) ≤ ·)] [UniqueContinuousFunctionalCalculus ℝ A]
  [NonnegSpectrumClass ℝ A]

lemma cfcHom_nnreal_eq_restrict {a : A} (ha : 0 ≤ a) :
    cfcHom ha = (SpectrumRestricts.nnreal_of_nonneg ha).starAlgHom
      (cfcHom (IsSelfAdjoint.of_nonneg ha)) := by
  have := UniqueContinuousFunctionalCalculus.compactSpace_spectrum a (R := ℝ)
  apply (SpectrumRestricts.nnreal_of_nonneg ha).cfcHom_eq_restrict uniformEmbedding_subtype_val

lemma cfc_nnreal_eq_real {a : A} (f : ℝ≥0 → ℝ≥0) (ha : 0 ≤ a := by cfc_tac)  :
    cfc f a = cfc (fun x ↦ f x.toNNReal : ℝ → ℝ) a := by
  have := UniqueContinuousFunctionalCalculus.compactSpace_spectrum a (R := ℝ)
  replace ha : 0 ≤ a := ha -- hack to avoid issues caused by autoParam
  apply (SpectrumRestricts.nnreal_of_nonneg ha).cfc_eq_restrict
    uniformEmbedding_subtype_val ha (.of_nonneg ha)

end NNRealEqReal

end
