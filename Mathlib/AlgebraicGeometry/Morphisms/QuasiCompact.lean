import Mathlib.Tactic.Have
/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.AlgebraicGeometry.Morphisms.Basic
import Mathlib.Topology.Spectral.Hom
import Mathlib.AlgebraicGeometry.Limits

/-!
# Quasi-compact morphisms

A morphism of schemes is quasi-compact if the preimages of quasi-compact open sets are
quasi-compact.

It suffices to check that preimages of affine open sets are compact
(`quasiCompact_iff_forall_affine`).

-/


noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

open scoped AlgebraicGeometry

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/--
A morphism is "quasi-compact" if the underlying map of topological spaces is, i.e. if the preimages
of quasi-compact open sets are quasi-compact.
-/
@[mk_iff]
class QuasiCompact (f : X ⟶ Y) : Prop where
  /-- Preimage of compact open set under a quasi-compact morphism between schemes is compact. -/
  isCompact_preimage : ∀ U : Set Y, IsOpen U → IsCompact U → IsCompact (f.1.base ⁻¹' U)

theorem quasiCompact_iff_spectral : QuasiCompact f ↔ IsSpectralMap f.1.base :=
  ⟨fun ⟨h⟩ => ⟨by fun_prop, h⟩, fun h => ⟨h.2⟩⟩

instance (priority := 900) quasiCompact_of_isIso {X Y : Scheme} (f : X ⟶ Y) [IsIso f] :
    QuasiCompact f := by
  constructor
  intro U _ hU'
  convert hU'.image (inv f.1.base).continuous_toFun using 1
  rw [Set.image_eq_preimage_of_inverse]
  delta Function.LeftInverse
  exact IsIso.inv_hom_id_apply f.1.base
  exact IsIso.hom_inv_id_apply f.1.base

instance quasiCompact_comp {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) [QuasiCompact f]
    [QuasiCompact g] : QuasiCompact (f ≫ g) := by
  constructor
  intro U hU hU'
  rw [Scheme.comp_val_base, TopCat.coe_comp, Set.preimage_comp]
  apply QuasiCompact.isCompact_preimage
  exact Continuous.isOpen_preimage (by fun_prop) _ hU
  apply QuasiCompact.isCompact_preimage <;> assumption

theorem isCompactOpen_iff_eq_finset_affine_union {X : Scheme} (U : Set X) :
    IsCompact U ∧ IsOpen U ↔ ∃ s : Set X.affineOpens, s.Finite ∧ U = ⋃ i ∈ s, i := by
  apply Opens.IsBasis.isCompact_open_iff_eq_finite_iUnion
    (fun (U : X.affineOpens) => (U : X.Opens))
  rw [Subtype.range_coe]; exact isBasis_affine_open X
  exact fun i => i.2.isCompact

theorem isCompactOpen_iff_eq_basicOpen_union {X : Scheme} [IsAffine X] (U : Set X) :
    IsCompact U ∧ IsOpen U ↔
      ∃ s : Set Γ(X, ⊤), s.Finite ∧ U = ⋃ i ∈ s, X.basicOpen i :=
  (isBasis_basicOpen X).isCompact_open_iff_eq_finite_iUnion _
    (fun _ => ((isAffineOpen_top _).basicOpen _).isCompact) _

theorem quasiCompact_iff_forall_affine :
    QuasiCompact f ↔
      ∀ U : Y.Opens, IsAffineOpen U → IsCompact (f ⁻¹ᵁ U : Set X) := by
  rw [quasiCompact_iff]
  refine ⟨fun H U hU => H U U.isOpen hU.isCompact, ?_⟩
  intro H U hU hU'
  obtain ⟨S, hS, rfl⟩ := (isCompactOpen_iff_eq_finset_affine_union U).mp ⟨hU', hU⟩
  simp only [Set.preimage_iUnion]
  exact Set.Finite.isCompact_biUnion hS (fun i _ => H i i.prop)

open Classical in
theorem isCompact_basicOpen (X : Scheme) {U : X.Opens} (hU : IsCompact (U : Set X))
    (f : Γ(X, U)) : IsCompact (X.basicOpen f : Set X) := by
  refine ((isCompactOpen_iff_eq_finset_affine_union _).mpr ?_).1
  obtain ⟨s, hs, e⟩ := (isCompactOpen_iff_eq_finset_affine_union _).mp ⟨hU, U.isOpen⟩
  let g : s → X.affineOpens := by
    intro V
    use V.1 ⊓ X.basicOpen f
    have : V.1.1 ⟶ U
    apply homOfLE; change _ ⊆ (U : Set X); rw [e]
    convert Set.subset_iUnion₂ (s := fun (U : X.affineOpens) (_ : U ∈ s) => (U : Set X))
      V V.prop using 1
    erw [← X.toLocallyRingedSpace.toRingedSpace.basicOpen_res this.op]
    exact IsAffineOpen.basicOpen V.1.prop _
  haveI : Finite s := hs.to_subtype
  refine ⟨Set.range g, Set.finite_range g, ?_⟩
  refine (Set.inter_eq_right.mpr
            (SetLike.coe_subset_coe.2 <| RingedSpace.basicOpen_le _ _)).symm.trans ?_
  rw [e, Set.iUnion₂_inter]
  apply le_antisymm <;> apply Set.iUnion₂_subset
  intro i hi
  -- Porting note: had to make explicit the first given parameter to `Set.subset_iUnion₂`
  exact Set.Subset.trans (Set.Subset.rfl : _ ≤ g ⟨i, hi⟩)
    (@Set.subset_iUnion₂ _ _ _
      (fun (i : X.affineOpens) (_ : i ∈ Set.range g) => (i : Set X.toPresheafedSpace)) _
      (Set.mem_range_self ⟨i, hi⟩))
  rintro ⟨i, hi⟩ ⟨⟨j, hj⟩, hj'⟩
  rw [← hj']
  refine Set.Subset.trans ?_ (Set.subset_iUnion₂ j hj)
  exact Set.Subset.rfl

@[reducible]
instance : HasAffineProperty @QuasiCompact (fun X _ _ _ ↦ CompactSpace X) where
  eq_targetAffineLocally' := by
    ext X Y f
    simp only [quasiCompact_iff_forall_affine, isCompact_iff_compactSpace, targetAffineLocally,
      Subtype.forall]
    rfl
  isLocal_affineProperty := by
    constructor
    · apply AffineTargetMorphismProperty.respectsIso_mk <;> rintro X Y Z e _ _ H
      exacts [@Homeomorph.compactSpace _ _ _ _ H (TopCat.homeoOfIso (asIso e.inv.1.base)), H]
    introv _ H
    change CompactSpace ((Opens.map f.val.base).obj (Y.basicOpen r))
    rw [Scheme.preimage_basicOpen f r]
    erw [← isCompact_iff_compactSpace]
    rw [← isCompact_univ_iff] at H
    apply isCompact_basicOpen
    exact H
    rintro X Y H f S hS hS'
    rw [← IsAffineOpen.basicOpen_union_eq_self_iff] at hS
    rw [← isCompact_univ_iff]
    change IsCompact ((Opens.map f.val.base).obj ⊤).1
    rw [← hS]
    dsimp [Opens.map]
    simp only [Opens.iSup_mk, Opens.coe_mk, Set.preimage_iUnion]
    exact isCompact_iUnion fun i => isCompact_iff_compactSpace.mpr (hS' i)
    exact isAffineOpen_top _

theorem quasiCompact_over_affine_iff {X Y : Scheme} (f : X ⟶ Y) [IsAffine Y] :
    QuasiCompact f ↔ CompactSpace X := by
  rw [HasAffineProperty.iff_of_isAffine (P := @QuasiCompact)]

theorem compactSpace_iff_quasiCompact (X : Scheme) :
    CompactSpace X ↔ QuasiCompact (terminal.from X) := by
  rw [HasAffineProperty.iff_of_isAffine (P := @QuasiCompact)]

instance quasiCompact_isStableUnderComposition :
    MorphismProperty.IsStableUnderComposition @QuasiCompact where
  comp_mem _ _ _ _ := inferInstance

theorem quasiCompact_stableUnderBaseChange :
    MorphismProperty.StableUnderBaseChange @QuasiCompact := by
  letI := HasAffineProperty.isLocal_affineProperty @QuasiCompact
  apply HasAffineProperty.stableUnderBaseChange
  apply AffineTargetMorphismProperty.StableUnderBaseChange.mk
  intro X Y S _ _ f g h
  let 𝒰 := Scheme.Pullback.openCoverOfRight Y.affineCover.finiteSubcover f g
  have : Finite 𝒰.J
  dsimp [𝒰]; infer_instance
  have : ∀ i, CompactSpace (𝒰.obj i)
  intro i; dsimp [𝒰]; infer_instance
  exact 𝒰.compactSpace

variable {Z : Scheme.{u}}

instance (f : X ⟶ Z) (g : Y ⟶ Z) [QuasiCompact g] : QuasiCompact (pullback.fst f g) :=
  quasiCompact_stableUnderBaseChange.fst f g inferInstance

instance (f : X ⟶ Z) (g : Y ⟶ Z) [QuasiCompact f] : QuasiCompact (pullback.snd f g) :=
  quasiCompact_stableUnderBaseChange.snd f g inferInstance

open Classical in
@[elab_as_elim]
theorem compact_open_induction_on {P : X.Opens → Prop} (S : X.Opens)
    (hS : IsCompact S.1) (h₁ : P ⊥)
    (h₂ : ∀ (S : X.Opens) (_ : IsCompact S.1) (U : X.affineOpens), P S → P (S ⊔ U)) :
    P S := by
  obtain ⟨s, hs, hs'⟩ := (isCompactOpen_iff_eq_finset_affine_union S.1).mp ⟨hS, S.2⟩
  replace hs' : S = iSup fun i : s => (i : X.Opens) := by ext1; simpa using hs'
  subst hs'
  apply @Set.Finite.induction_on _ _ _ hs
  convert h₁; rw [iSup_eq_bot]; rintro ⟨_, h⟩; exact h.elim
  intro x s _ hs h₄
  have : IsCompact (⨆ i : s, (i : X.Opens)).1
  refine ((isCompactOpen_iff_eq_finset_affine_union _).mpr ?_).1; exact ⟨s, hs, by simp⟩
  convert h₂ _ this x h₄
  rw [iSup_subtype, sup_comm]
  conv_rhs => rw [iSup_subtype]
  exact iSup_insert

theorem exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isAffineOpen (X : Scheme)
    {U : X.Opens} (hU : IsAffineOpen U) (x f : Γ(X, U))
    (H : x |_ X.basicOpen f = 0) : ∃ n : ℕ, f ^ n * x = 0 := by
  rw [← map_zero (X.presheaf.map (homOfLE <| X.basicOpen_le f : X.basicOpen f ⟶ U).op)] at H
  obtain ⟨⟨_, n, rfl⟩, e⟩ := (hU.isLocalization_basicOpen f).exists_of_eq H
  exact ⟨n, by simpa [mul_comm x] using e⟩

/-- If `x : Γ(X, U)` is zero on `D(f)` for some `f : Γ(X, U)`, and `U` is quasi-compact, then
`f ^ n * x = 0` for some `n`. -/
theorem exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isCompact (X : Scheme.{u})
    {U : X.Opens} (hU : IsCompact U.1) (x f : Γ(X, U))
    (H : x |_ X.basicOpen f = 0) : ∃ n : ℕ, f ^ n * x = 0 := by
  obtain ⟨s, hs, e⟩ := (isCompactOpen_iff_eq_finset_affine_union U.1).mp ⟨hU, U.2⟩
  replace e : U = iSup fun i : s => (i : X.Opens) := by
    ext1; simpa using e
  have h₁ : ∀ i : s, i.1.1 ≤ U
  intro i
  change (i : X.Opens) ≤ U
  rw [e]
  -- Porting note: `exact le_iSup _ _` no longer works
  exact le_iSup (fun (i : s) => (i : Opens (X.toPresheafedSpace))) _
  have H' := fun i : s =>
    exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isAffineOpen X i.1.2
      (X.presheaf.map (homOfLE (h₁ i)).op x) (X.presheaf.map (homOfLE (h₁ i)).op f) ?_
  swap
  delta TopCat.Presheaf.restrictOpen TopCat.Presheaf.restrict at H ⊢
  convert congr_arg (X.presheaf.map (homOfLE _).op) H
  -- Note: the below was `simp only [← comp_apply]`
  rw [← comp_apply, ← comp_apply]
  simp only [← Functor.map_comp]
  rfl
  rw [map_zero]
  simp only [Scheme.basicOpen_res, inf_le_right]
  choose n hn using H'
  haveI := hs.to_subtype
  cases nonempty_fintype s
  use Finset.univ.sup n
  suffices ∀ i : s, X.presheaf.map (homOfLE (h₁ i)).op (f ^ Finset.univ.sup n * x) = 0 by
    subst e
    apply TopCat.Sheaf.eq_of_locally_eq X.sheaf fun i : s => (i : X.Opens)
    intro i
    rw [map_zero]
    apply this
  intro i
  replace hn :=
    congr_arg (fun x => X.presheaf.map (homOfLE (h₁ i)).op (f ^ (Finset.univ.sup n - n i)) * x)
      (hn i)
  dsimp at hn
  simp only [← map_mul, ← map_pow] at hn
  rwa [mul_zero, ← mul_assoc, ← pow_add, tsub_add_cancel_of_le] at hn
  apply Finset.le_sup (Finset.mem_univ i)

/-- A section over a compact open of a scheme is nilpotent if and only if its associated
basic open is empty. -/
lemma Scheme.isNilpotent_iff_basicOpen_eq_bot_of_isCompact {X : Scheme.{u}}
    {U : X.Opens} (hU : IsCompact (U : Set X)) (f : Γ(X, U)) :
    IsNilpotent f ↔ X.basicOpen f = ⊥ := by
  refine ⟨X.basicOpen_eq_bot_of_isNilpotent U f, fun hf ↦ ?_⟩
  have h : (1 : Γ(X, U)) |_ X.basicOpen f = (0 : Γ(X, X.basicOpen f))
  have e : X.basicOpen f ≤ ⊥
  rw [hf]
  rw [← X.presheaf.restrict_restrict e bot_le]
  have : Subsingleton Γ(X, ⊥) :=
    CommRingCat.subsingleton_of_isTerminal X.sheaf.isTerminalOfEmpty
  rw [Subsingleton.eq_zero (1 |_ ⊥)]
  show X.presheaf.map _ 0 = 0
  rw [map_zero]
  obtain ⟨n, hn⟩ := exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isCompact X hU 1 f h
  rw [mul_one] at hn
  use n

/-- The zero locus of a set of sections over a compact open of a scheme is `X` if and only if
`s` is contained in the nilradical of `Γ(X, U)`. -/
lemma Scheme.zeroLocus_eq_top_iff_subset_nilradical_of_isCompact {X : Scheme.{u}} {U : X.Opens}
    (hU : IsCompact (U : Set X)) (s : Set Γ(X, U)) :
    X.zeroLocus s = ⊤ ↔ s ⊆ nilradical Γ(X, U) := by
  simp [Scheme.zeroLocus_def, ← Scheme.isNilpotent_iff_basicOpen_eq_bot_of_isCompact hU,
    ← mem_nilradical, Set.subset_def]

end AlgebraicGeometry
