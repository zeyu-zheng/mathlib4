import Mathlib.Tactic.Have
/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.AlgebraicGeometry.OpenImmersion

/-!
# Open covers of schemes

This file provides the basic API for open covers of schemes.

## Main definition
- `AlgebraicGeometry.Scheme.OpenCover`: The type of open covers of a scheme `X`,
  consisting of a family of open immersions into `X`,
  and for each `x : X` an open immersion (indexed by `f x`) that covers `x`.
- `AlgebraicGeometry.Scheme.affineCover`: `X.affineCover` is a choice of an affine cover of `X`.
- `AlgebraicGeometry.Scheme.AffineOpenCover`: The type of affine open covers of a scheme `X`.
-/


noncomputable section

open TopologicalSpace CategoryTheory Opposite CategoryTheory.Limits

universe v v₁ v₂ u

namespace AlgebraicGeometry

namespace Scheme

-- TODO: provide API to and from a presieve.
/-- An open cover of `X` consists of a family of open immersions into `X`,
and for each `x : X` an open immersion (indexed by `f x`) that covers `x`.

This is merely a coverage in the Zariski pretopology, and it would be optimal
if we could reuse the existing API about pretopologies, However, the definitions of sieves and
grothendieck topologies uses `Prop`s, so that the actual open sets and immersions are hard to
obtain. Also, since such a coverage in the pretopology usually contains a proper class of
immersions, it is quite hard to glue them, reason about finite covers, etc.
-/
structure OpenCover (X : Scheme.{u}) where
  /-- index set of an open cover of a scheme `X` -/
  J : Type v
  /-- the subschemes of an open cover -/
  obj : J → Scheme
  /-- the embedding of subschemes to `X` -/
  map : ∀ j : J, obj j ⟶ X
  /-- given a point of `x : X`, `f x` is the index of the subscheme which contains `x`  -/
  f : X → J
  /-- the subschemes covers `X` -/
  covers : ∀ x, x ∈ Set.range (map (f x)).1.base
  /-- the embedding of subschemes are open immersions -/
  IsOpen : ∀ x, IsOpenImmersion (map x) := by infer_instance

@[deprecated (since := "2024-06-23")] alias OpenCover.Covers := OpenCover.covers

attribute [instance] OpenCover.IsOpen

variable {X Y Z : Scheme.{u}} (𝒰 : OpenCover X) (f : X ⟶ Z) (g : Y ⟶ Z)
variable [∀ x, HasPullback (𝒰.map x ≫ f) g]

/-- The affine cover of a scheme. -/
def affineCover (X : Scheme.{u}) : OpenCover X where
  J := X
  obj x := Spec (X.local_affine x).choose_spec.choose
  map x :=
    ((X.local_affine x).choose_spec.choose_spec.some.inv ≫ X.toLocallyRingedSpace.ofRestrict _ : _)
  f x := x
  covers := by
    intro x
    erw [TopCat.coe_comp] -- now `erw` after #13170
    rw [Set.range_comp, Set.range_iff_surjective.mpr, Set.image_univ]
    · erw [Subtype.range_coe_subtype]
      exact (X.local_affine x).choose.2
    erw [← TopCat.epi_iff_surjective] -- now `erw` after #13170
    change Epi ((SheafedSpace.forget _).map (LocallyRingedSpace.forgetToSheafedSpace.map _))
    infer_instance

instance : Inhabited X.OpenCover :=
  ⟨X.affineCover⟩

theorem OpenCover.iUnion_range {X : Scheme.{u}} (𝒰 : X.OpenCover) :
    ⋃ i, Set.range (𝒰.map i).1.base = Set.univ := by
  rw [Set.eq_univ_iff_forall]
  intro x
  rw [Set.mem_iUnion]
  exact ⟨𝒰.f x, 𝒰.covers x⟩

theorem OpenCover.iSup_opensRange {X : Scheme.{u}} (𝒰 : X.OpenCover) :
    ⨆ i, (𝒰.map i).opensRange = ⊤ :=
  Opens.ext <| by rw [Opens.coe_iSup]; exact 𝒰.iUnion_range

/-- Given an open cover `{ Uᵢ }` of `X`, and for each `Uᵢ` an open cover, we may combine these
open covers to form an open cover of `X`.  -/
@[simps! J obj map]
def OpenCover.bind (f : ∀ x : 𝒰.J, OpenCover (𝒰.obj x)) : OpenCover X where
  J := Σ i : 𝒰.J, (f i).J
  obj x := (f x.1).obj x.2
  map x := (f x.1).map x.2 ≫ 𝒰.map x.1
  f x := ⟨_, (f _).f (𝒰.covers x).choose⟩
  covers x := by
    let y := (𝒰.covers x).choose
    have hy : (𝒰.map (𝒰.f x)).val.base y = x := (𝒰.covers x).choose_spec
    rcases (f (𝒰.f x)).covers y with ⟨z, hz⟩
    change x ∈ Set.range ((f (𝒰.f x)).map ((f (𝒰.f x)).f y) ≫ 𝒰.map (𝒰.f x)).1.base
    use z
    erw [comp_apply]
    erw [hz, hy] -- now `erw` after #13170
  -- Porting note: weirdly, even though no input is needed, `inferInstance` does not work
  -- `PresheafedSpace.IsOpenImmersion.comp` is marked as `instance`
  IsOpen x := PresheafedSpace.IsOpenImmersion.comp _ _

/-- An isomorphism `X ⟶ Y` is an open cover of `Y`. -/
@[simps J obj map]
def openCoverOfIsIso {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f] : OpenCover.{v} Y where
  J := PUnit.{v + 1}
  obj _ := X
  map _ := f
  f _ := PUnit.unit
  covers x := by
    rw [Set.range_iff_surjective.mpr]
    all_goals try trivial
    rw [← TopCat.epi_iff_surjective]
    infer_instance

/-- We construct an open cover from another, by providing the needed fields and showing that the
provided fields are isomorphic with the original open cover. -/
@[simps J obj map]
def OpenCover.copy {X : Scheme.{u}} (𝒰 : OpenCover X) (J : Type*) (obj : J → Scheme)
    (map : ∀ i, obj i ⟶ X) (e₁ : J ≃ 𝒰.J) (e₂ : ∀ i, obj i ≅ 𝒰.obj (e₁ i))
    (e₂ : ∀ i, map i = (e₂ i).hom ≫ 𝒰.map (e₁ i)) : OpenCover X :=
  { J, obj, map
    f := fun x => e₁.symm (𝒰.f x)
    covers := fun x => by
      rw [e₂, Scheme.comp_val_base, TopCat.coe_comp, Set.range_comp, Set.range_iff_surjective.mpr,
        Set.image_univ, e₁.rightInverse_symm]
      · exact 𝒰.covers x
      · erw [← TopCat.epi_iff_surjective]; infer_instance -- now `erw` after #13170
    -- Porting note: weirdly, even though no input is needed, `inferInstance` does not work
    -- `PresheafedSpace.IsOpenImmersion.comp` is marked as `instance`
    IsOpen := fun i => by rw [e₂]; exact PresheafedSpace.IsOpenImmersion.comp _ _ }

-- Porting note: need more hint on universe level
/-- The pushforward of an open cover along an isomorphism. -/
@[simps! J obj map]
def OpenCover.pushforwardIso {X Y : Scheme.{u}} (𝒰 : OpenCover.{v} X) (f : X ⟶ Y) [IsIso f] :
    OpenCover.{v} Y :=
  ((openCoverOfIsIso.{v, u} f).bind fun _ => 𝒰).copy 𝒰.J _ _
    ((Equiv.punitProd _).symm.trans (Equiv.sigmaEquivProd PUnit 𝒰.J).symm) (fun _ => Iso.refl _)
    fun _ => (Category.id_comp _).symm

/-- Adding an open immersion into an open cover gives another open cover. -/
@[simps]
def OpenCover.add {X Y : Scheme.{u}} (𝒰 : X.OpenCover) (f : Y ⟶ X) [IsOpenImmersion f] :
    X.OpenCover where
  J := Option 𝒰.J
  obj i := Option.rec Y 𝒰.obj i
  map i := Option.rec f 𝒰.map i
  f x := some (𝒰.f x)
  covers := 𝒰.covers
  IsOpen := by rintro (_ | _) <;> dsimp <;> infer_instance

/-- Given an open cover on `X`, we may pull them back along a morphism `W ⟶ X` to obtain
an open cover of `W`. -/
@[simps]
def OpenCover.pullbackCover {X W : Scheme.{u}} (𝒰 : X.OpenCover) (f : W ⟶ X) :
    W.OpenCover where
  J := 𝒰.J
  obj x := pullback f (𝒰.map x)
  map x := pullback.fst _ _
  f x := 𝒰.f (f.1.base x)
  covers x := by
    rw [←
      show _ = (pullback.fst _ _ : pullback f (𝒰.map (𝒰.f (f.1.base x))) ⟶ _).1.base from
        PreservesPullback.iso_hom_fst Scheme.forgetToTop f (𝒰.map (𝒰.f (f.1.base x)))]
    -- Porting note: `rw` to `erw` on this single lemma
    rw [TopCat.coe_comp, Set.range_comp, Set.range_iff_surjective.mpr, Set.image_univ,
      TopCat.pullback_fst_range]
    · obtain ⟨y, h⟩ := 𝒰.covers (f.1.base x)
      exact ⟨y, h.symm⟩
    · rw [← TopCat.epi_iff_surjective]; infer_instance

/-- The family of morphisms from the pullback cover to the original cover. -/
def OpenCover.pullbackHom {X W : Scheme.{u}} (𝒰 : X.OpenCover) (f : W ⟶ X) (i) :
    (𝒰.pullbackCover f).obj i ⟶ 𝒰.obj i :=
  pullback.snd f (𝒰.map i)

@[reassoc (attr := simp)]
lemma OpenCover.pullbackHom_map {X W : Scheme.{u}} (𝒰 : X.OpenCover) (f : W ⟶ X) (i) :
    𝒰.pullbackHom f i ≫ 𝒰.map i = (𝒰.pullbackCover f).map i ≫ f := pullback.condition.symm

/-- Given an open cover on `X`, we may pull them back along a morphism `f : W ⟶ X` to obtain
an open cover of `W`. This is similar to `Scheme.OpenCover.pullbackCover`, but here we
take `pullback (𝒰.map x) f` instead of `pullback f (𝒰.map x)`. -/
@[simps]
def OpenCover.pullbackCover' {X W : Scheme.{u}} (𝒰 : X.OpenCover) (f : W ⟶ X) :
    W.OpenCover where
  J := 𝒰.J
  obj x := pullback (𝒰.map x) f
  map x := pullback.snd _ _
  f x := 𝒰.f (f.1.base x)
  covers x := by
    rw [←
      show _ = (pullback.snd (𝒰.map (𝒰.f (f.1.base x))) f).1.base from
        PreservesPullback.iso_hom_snd Scheme.forgetToTop (𝒰.map (𝒰.f (f.1.base x))) f]
    -- Porting note: `rw` to `erw` on this single lemma
    rw [TopCat.coe_comp, Set.range_comp, Set.range_iff_surjective.mpr, Set.image_univ,
      TopCat.pullback_snd_range]
    · obtain ⟨y, h⟩ := 𝒰.covers (f.1.base x)
      exact ⟨y, h⟩
    · rw [← TopCat.epi_iff_surjective]; infer_instance

/-- Every open cover of a quasi-compact scheme can be refined into a finite subcover.
-/
@[simps! obj map]
def OpenCover.finiteSubcover {X : Scheme.{u}} (𝒰 : OpenCover X) [H : CompactSpace X] :
    OpenCover X := by
  have :=
    @CompactSpace.elim_nhds_subcover _ _ H (fun x : X => Set.range (𝒰.map (𝒰.f x)).1.base)
      fun x => (IsOpenImmersion.isOpen_range (𝒰.map (𝒰.f x))).mem_nhds (𝒰.covers x)
  let t := this.choose
  have h : ∀ x : X, ∃ y : t, x ∈ Set.range (𝒰.map (𝒰.f y)).1.base := by
    intro x
    have h' : x ∈ (⊤ : Set X) := trivial
    rw [← Classical.choose_spec this, Set.mem_iUnion] at h'
    rcases h' with ⟨y, _, ⟨hy, rfl⟩, hy'⟩
    exact ⟨⟨y, hy⟩, hy'⟩
  exact
    { J := t
      obj := fun x => 𝒰.obj (𝒰.f x.1)
      map := fun x => 𝒰.map (𝒰.f x.1)
      f := fun x => (h x).choose
      covers := fun x => (h x).choose_spec }

instance [H : CompactSpace X] : Fintype 𝒰.finiteSubcover.J := by
  delta OpenCover.finiteSubcover; infer_instance

theorem OpenCover.compactSpace {X : Scheme.{u}} (𝒰 : X.OpenCover) [Finite 𝒰.J]
    [H : ∀ i, CompactSpace (𝒰.obj i)] : CompactSpace X := by
  cases nonempty_fintype 𝒰.J
  rw [← isCompact_univ_iff, ← 𝒰.iUnion_range]
  apply isCompact_iUnion
  intro i
  rw [isCompact_iff_compactSpace]
  exact
    @Homeomorph.compactSpace _ _ _ _ (H i)
      (TopCat.homeoOfIso
        (asIso
          (IsOpenImmersion.isoOfRangeEq (𝒰.map i)
                  (X.ofRestrict (Opens.openEmbedding ⟨_, (𝒰.IsOpen i).base_open.isOpen_range⟩))
                  Subtype.range_coe.symm).hom.1.base))

/-- Given open covers `{ Uᵢ }` and `{ Uⱼ }`, we may form the open cover `{ Uᵢ ∩ Uⱼ }`. -/
def OpenCover.inter {X : Scheme.{u}} (𝒰₁ : Scheme.OpenCover.{v₁} X)
    (𝒰₂ : Scheme.OpenCover.{v₂} X) : X.OpenCover where
  J := 𝒰₁.J × 𝒰₂.J
  obj ij := pullback (𝒰₁.map ij.1) (𝒰₂.map ij.2)
  map ij := pullback.fst _ _ ≫ 𝒰₁.map ij.1
  f x := ⟨𝒰₁.f x, 𝒰₂.f x⟩
  covers x := by
    rw [IsOpenImmersion.range_pullback_to_base_of_left]
    exact ⟨𝒰₁.covers x, 𝒰₂.covers x⟩
  IsOpen x := inferInstance

/--
An affine open cover of `X` consists of a family of open immersions into `X` from
spectra of rings.
-/
structure AffineOpenCover (X : Scheme.{u}) where
  /-- index set of an affine open cover of a scheme `X` -/
  J : Type v
  /-- the ring associated to a component of an affine open cover -/
  obj : J → CommRingCat.{u}
  /-- the embedding of subschemes to `X` -/
  map : ∀ j : J, Spec (obj j) ⟶ X
  /-- given a point of `x : X`, `f x` is the index of the subscheme which contains `x`  -/
  f : X → J
  /-- the subschemes covers `X` -/
  covers : ∀ x, x ∈ Set.range (map (f x)).1.base
  /-- the embedding of subschemes are open immersions -/
  IsOpen : ∀ x, IsOpenImmersion (map x) := by infer_instance

namespace AffineOpenCover

attribute [instance] AffineOpenCover.IsOpen

/-- The open cover associated to an affine open cover. -/
@[simps]
def openCover {X : Scheme.{u}} (𝓤 : X.AffineOpenCover) : X.OpenCover where
  J := 𝓤.J
  map := 𝓤.map
  f := 𝓤.f
  covers := 𝓤.covers

end AffineOpenCover

/-- A choice of an affine open cover of a scheme. -/
def affineOpenCover (X : Scheme.{u}) : X.AffineOpenCover where
  J := X.affineCover.J
  map := X.affineCover.map
  f := X.affineCover.f
  covers := X.affineCover.covers

@[simp]
lemma openCover_affineOpenCover (X : Scheme.{u}) : X.affineOpenCover.openCover = X.affineCover :=
  rfl

/-- Given any open cover `𝓤`, this is an affine open cover which refines it.
The morphism in the category of open covers which proves that this is indeed a refinement, see
`AlgebraicGeometry.Scheme.OpenCover.fromAffineRefinement`.
-/
def OpenCover.affineRefinement {X : Scheme.{u}} (𝓤 : X.OpenCover) : X.AffineOpenCover where
  J := (𝓤.bind fun j => (𝓤.obj j).affineCover).J
  map := (𝓤.bind fun j => (𝓤.obj j).affineCover).map
  f := (𝓤.bind fun j => (𝓤.obj j).affineCover).f
  covers := (𝓤.bind fun j => (𝓤.obj j).affineCover).covers

/-- The pullback of the affine refinement is the pullback of the affine cover. -/
def OpenCover.pullbackCoverAffineRefinementObjIso (f : X ⟶ Y) (𝒰 : Y.OpenCover) (i) :
    (𝒰.affineRefinement.openCover.pullbackCover f).obj i ≅
      ((𝒰.obj i.1).affineCover.pullbackCover (𝒰.pullbackHom f i.1)).obj i.2 :=
  pullbackSymmetry _ _ ≪≫ (pullbackRightPullbackFstIso _ _ _).symm ≪≫
    pullbackSymmetry _ _ ≪≫ asIso (pullback.map _ _ _ _ (pullbackSymmetry _ _).hom (𝟙 _) (𝟙 _)
      (by simp [pullbackHom]) (by simp))

@[reassoc]
lemma OpenCover.pullbackCoverAffineRefinementObjIso_inv_map (f : X ⟶ Y) (𝒰 : Y.OpenCover) (i) :
    (𝒰.pullbackCoverAffineRefinementObjIso f i).inv ≫
      (𝒰.affineRefinement.openCover.pullbackCover f).map i =
      ((𝒰.obj i.1).affineCover.pullbackCover (𝒰.pullbackHom f i.1)).map i.2 ≫
        (𝒰.pullbackCover f).map i.1 := by
  simp only [pullbackCover_obj, AffineOpenCover.openCover_obj, AffineOpenCover.openCover_map,
    pullbackCoverAffineRefinementObjIso, Iso.trans_inv, asIso_inv, Iso.symm_inv, Category.assoc,
    pullbackCover_map, pullbackSymmetry_inv_comp_fst, IsIso.inv_comp_eq, limit.lift_π_assoc, id_eq,
    PullbackCone.mk_pt, cospan_left, PullbackCone.mk_π_app, pullbackSymmetry_hom_comp_fst]
  convert pullbackSymmetry_inv_comp_snd_assoc
    ((𝒰.obj i.1).affineCover.map i.2) (pullback.fst _ _) _ using 2
  exact pullbackRightPullbackFstIso_hom_snd _ _ _

@[reassoc]
lemma OpenCover.pullbackCoverAffineRefinementObjIso_inv_pullbackHom
    (f : X ⟶ Y) (𝒰 : Y.OpenCover) (i) :
    (𝒰.pullbackCoverAffineRefinementObjIso f i).inv ≫
      𝒰.affineRefinement.openCover.pullbackHom f i =
      (𝒰.obj i.1).affineCover.pullbackHom (𝒰.pullbackHom f i.1) i.2 := by
  simp only [pullbackCover_obj, pullbackHom, AffineOpenCover.openCover_obj,
    AffineOpenCover.openCover_map, pullbackCoverAffineRefinementObjIso, Iso.trans_inv, asIso_inv,
    Iso.symm_inv, Category.assoc, pullbackSymmetry_inv_comp_snd, IsIso.inv_comp_eq, limit.lift_π,
    id_eq, PullbackCone.mk_pt, PullbackCone.mk_π_app, Category.comp_id]
  convert pullbackSymmetry_inv_comp_fst ((𝒰.obj i.1).affineCover.map i.2) (pullback.fst _ _)
  exact pullbackRightPullbackFstIso_hom_fst _ _ _

section category

/--
A morphism between open covers `𝓤 ⟶ 𝓥` indicates that `𝓤` is a refinement of `𝓥`.
Since open covers of schemes are indexed, the definition also involves a map on the
indexing types.
-/
structure OpenCover.Hom {X : Scheme.{u}} (𝓤 𝓥 : OpenCover.{v} X) where
  /-- The map on indexing types associated to a morphism of open covers. -/
  idx : 𝓤.J → 𝓥.J
  /-- The morphism between open subsets associated to a morphism of open covers. -/
  app (j : 𝓤.J) : 𝓤.obj j ⟶ 𝓥.obj (idx j)
  isOpen (j : 𝓤.J) : IsOpenImmersion (app j) := by infer_instance
  w (j : 𝓤.J) : app j ≫ 𝓥.map _ = 𝓤.map _ := by aesop_cat

attribute [reassoc (attr := simp)] OpenCover.Hom.w
attribute [instance] OpenCover.Hom.isOpen

/-- The identity morphism in the category of open covers of a scheme. -/
def OpenCover.Hom.id {X : Scheme.{u}} (𝓤 : OpenCover.{v} X) : 𝓤.Hom 𝓤 where
  idx j := j
  app j := 𝟙 _

/-- The composition of two morphisms in the category of open covers of a scheme. -/
def OpenCover.Hom.comp {X : Scheme.{u}} {𝓤 𝓥 𝓦 : OpenCover.{v} X}
    (f : 𝓤.Hom 𝓥) (g : 𝓥.Hom 𝓦) : 𝓤.Hom 𝓦 where
  idx j := g.idx <| f.idx j
  app j := f.app _ ≫ g.app _

instance OpenCover.category {X : Scheme.{u}} : Category (OpenCover.{v} X) where
  Hom 𝓤 𝓥 := 𝓤.Hom 𝓥
  id := OpenCover.Hom.id
  comp f g := f.comp g

@[simp]
lemma OpenCover.id_idx_apply {X : Scheme.{u}} (𝓤 : X.OpenCover) (j : 𝓤.J) :
    (𝟙 𝓤 : 𝓤 ⟶ 𝓤).idx j = j := rfl

@[simp]
lemma OpenCover.id_app {X : Scheme.{u}} (𝓤 : X.OpenCover) (j : 𝓤.J) :
    (𝟙 𝓤 : 𝓤 ⟶ 𝓤).app j = 𝟙 _ := rfl

@[simp]
lemma OpenCover.comp_idx_apply {X : Scheme.{u}} {𝓤 𝓥 𝓦 : X.OpenCover}
    (f : 𝓤 ⟶ 𝓥) (g : 𝓥 ⟶ 𝓦) (j : 𝓤.J) :
    (f ≫ g).idx j = g.idx (f.idx j) := rfl

@[simp]
lemma OpenCover.comp_app {X : Scheme.{u}} {𝓤 𝓥 𝓦 : X.OpenCover}
    (f : 𝓤 ⟶ 𝓥) (g : 𝓥 ⟶ 𝓦) (j : 𝓤.J) :
    (f ≫ g).app j = f.app j ≫ g.app _ := rfl

end category

/-- Given any open cover `𝓤`, this is an affine open cover which refines it. -/
def OpenCover.fromAffineRefinement {X : Scheme.{u}} (𝓤 : X.OpenCover) :
    𝓤.affineRefinement.openCover ⟶ 𝓤 where
  idx j := j.fst
  app j := (𝓤.obj j.fst).affineCover.map _

/-- If two global sections agree after restriction to each member of an open cover, then
they agree globally. -/
lemma OpenCover.ext_elem {X : Scheme.{u}} {U : X.Opens} (f g : Γ(X, U)) (𝒰 : X.OpenCover)
    (h : ∀ i : 𝒰.J, (𝒰.map i).app U f = (𝒰.map i).app U g) : f = g := by
  fapply TopCat.Sheaf.eq_of_locally_eq' X.sheaf
    (fun i ↦ (𝒰.map (𝒰.f i)).opensRange ⊓ U) _ (fun _ ↦ homOfLE inf_le_right)
  intro x hx
  simp only [Opens.iSup_mk, Opens.carrier_eq_coe, Opens.coe_inf, Hom.opensRange_coe, Opens.coe_mk,
    Set.mem_iUnion, Set.mem_inter_iff, Set.mem_range, SetLike.mem_coe, exists_and_right]
  refine ⟨?_, hx⟩
  simpa using ⟨_, 𝒰.covers x⟩
  intro x
  replace h := h (𝒰.f x)
  rw [← IsOpenImmersion.map_ΓIso_inv] at h
  exact (IsOpenImmersion.ΓIso (𝒰.map (𝒰.f x)) U).commRingCatIsoToRingEquiv.symm.injective h

/-- If the restriction of a global section to each member of an open cover is zero, then it is
globally zero. -/
lemma zero_of_zero_cover {X : Scheme.{u}} {U : X.Opens} (s : Γ(X, U)) (𝒰 : X.OpenCover)
    (h : ∀ i : 𝒰.J, (𝒰.map i).app U s = 0) : s = 0 :=
  𝒰.ext_elem s 0 (fun i ↦ by rw [map_zero]; exact h i)

/-- If a global section is nilpotent on each member of a finite open cover, then `f` is
nilpotent. -/
lemma isNilpotent_of_isNilpotent_cover {X : Scheme.{u}} {U : X.Opens} (s : Γ(X, U))
    (𝒰 : X.OpenCover) [Finite 𝒰.J] (h : ∀ i : 𝒰.J, IsNilpotent ((𝒰.map i).app U s)) :
    IsNilpotent s := by
  choose fn hfn using h
  have : Fintype 𝒰.J := Fintype.ofFinite 𝒰.J
  /- the maximum of all `fn i` (exists, because `𝒰.J` is finite) -/
  let N : ℕ := Finset.sup Finset.univ fn
  have hfnleN (i : 𝒰.J) : fn i ≤ N := Finset.le_sup (Finset.mem_univ i)
  use N
  apply zero_of_zero_cover
  on_goal 1 => intro i; simp only [map_pow]
  -- This closes both remaining goals at once.
  exact pow_eq_zero_of_le (hfnleN i) (hfn i)

section deprecated

/-- The basic open sets form an affine open cover of `Spec R`. -/
def affineBasisCoverOfAffine (R : CommRingCat.{u}) : OpenCover (Spec R) where
  J := R
  obj r := Spec (CommRingCat.of <| Localization.Away r)
  map r := Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r)))
  f _ := 1
  covers r := by
    rw [Set.range_iff_surjective.mpr ((TopCat.epi_iff_surjective _).mp _)]
    · exact trivial
    · -- Porting note: need more hand holding here because Lean knows that
      -- `CommRing.ofHom ...` is iso, but without `ofHom` Lean does not know what to do
      change Epi (Spec.map (CommRingCat.ofHom (algebraMap _ _))).1.base
      infer_instance
  IsOpen x := AlgebraicGeometry.Scheme.basic_open_isOpenImmersion x

/-- We may bind the basic open sets of an open affine cover to form an affine cover that is also
a basis. -/
def affineBasisCover (X : Scheme.{u}) : OpenCover X :=
  X.affineCover.bind fun _ => affineBasisCoverOfAffine _

/-- The coordinate ring of a component in the `affine_basis_cover`. -/
def affineBasisCoverRing (X : Scheme.{u}) (i : X.affineBasisCover.J) : CommRingCat :=
  CommRingCat.of <| @Localization.Away (X.local_affine i.1).choose_spec.choose _ i.2

theorem affineBasisCover_obj (X : Scheme.{u}) (i : X.affineBasisCover.J) :
    X.affineBasisCover.obj i = Spec (X.affineBasisCoverRing i) :=
  rfl

theorem affineBasisCover_map_range (X : Scheme.{u}) (x : X)
    (r : (X.local_affine x).choose_spec.choose) :
    Set.range (X.affineBasisCover.map ⟨x, r⟩).1.base =
      (X.affineCover.map x).1.base '' (PrimeSpectrum.basicOpen r).1 := by
  erw [coe_comp, Set.range_comp]
  -- Porting note: `congr` fails to see the goal is comparing image of the same function
  refine congr_arg (_ '' ·) ?_
  exact (PrimeSpectrum.localization_away_comap_range (Localization.Away r) r : _)

theorem affineBasisCover_is_basis (X : Scheme.{u}) :
    TopologicalSpace.IsTopologicalBasis
      {x : Set X |
        ∃ a : X.affineBasisCover.J, x = Set.range (X.affineBasisCover.map a).1.base} := by
  apply TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds
  rintro _ ⟨a, rfl⟩
  exact IsOpenImmersion.isOpen_range (X.affineBasisCover.map a)
  rintro a U haU hU
  rcases X.affineCover.covers a with ⟨x, e⟩
  let U' := (X.affineCover.map (X.affineCover.f a)).1.base ⁻¹' U
  have hxU' : x ∈ U'
  rw [← e] at haU; exact haU
  rcases PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open hxU'
      ((X.affineCover.map (X.affineCover.f a)).1.base.continuous_toFun.isOpen_preimage _
        hU) with
    ⟨_, ⟨_, ⟨s, rfl⟩, rfl⟩, hxV, hVU⟩
  refine ⟨_, ⟨⟨_, s⟩, rfl⟩, ?_, ?_⟩ <;> erw [affineBasisCover_map_range]
  exact ⟨x, hxV, e⟩
  rw [Set.image_subset_iff]; exact hVU

end deprecated

end Scheme

end AlgebraicGeometry
