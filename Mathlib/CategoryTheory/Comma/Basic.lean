import Mathlib.Tactic.Have
/-
Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Johan Commelin, Bhavik Mehta
-/
import Mathlib.CategoryTheory.Iso
import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.EqToHom

/-!
# Comma categories

A comma category is a construction in category theory, which builds a category out of two functors
with a common codomain. Specifically, for functors `L : A ⥤ T` and `R : B ⥤ T`, an object in
`Comma L R` is a morphism `hom : L.obj left ⟶ R.obj right` for some objects `left : A` and
`right : B`, and a morphism in `Comma L R` between `hom : L.obj left ⟶ R.obj right` and
`hom' : L.obj left' ⟶ R.obj right'` is a commutative square

```
L.obj left  ⟶  L.obj left'
      |               |
  hom |               | hom'
      ↓               ↓
R.obj right ⟶  R.obj right',
```

where the top and bottom morphism come from morphisms `left ⟶ left'` and `right ⟶ right'`,
respectively.

## Main definitions

* `Comma L R`: the comma category of the functors `L` and `R`.
* `Over X`: the over category of the object `X` (developed in `Over.lean`).
* `Under X`: the under category of the object `X` (also developed in `Over.lean`).
* `Arrow T`: the arrow category of the category `T` (developed in `Arrow.lean`).

## References

* <https://ncatlab.org/nlab/show/comma+category>

## Tags

comma, slice, coslice, over, under, arrow
-/


namespace CategoryTheory

open Category

-- declare the `v`'s first; see `CategoryTheory.Category` for an explanation
universe v₁ v₂ v₃ v₄ v₅ u₁ u₂ u₃ u₄ u₅

variable {A : Type u₁} [Category.{v₁} A]
variable {B : Type u₂} [Category.{v₂} B]
variable {T : Type u₃} [Category.{v₃} T]
variable {A' B' T' : Type*} [Category A'] [Category B'] [Category T']

/-- The objects of the comma category are triples of an object `left : A`, an object
   `right : B` and a morphism `hom : L.obj left ⟶ R.obj right`.  -/
structure Comma (L : A ⥤ T) (R : B ⥤ T) : Type max u₁ u₂ v₃ where
  left : A
  right : B
  hom : L.obj left ⟶ R.obj right

-- Satisfying the inhabited linter
instance Comma.inhabited [Inhabited T] : Inhabited (Comma (𝟭 T) (𝟭 T)) where
  default :=
    { left := default
      right := default
      hom := 𝟙 default }

variable {L : A ⥤ T} {R : B ⥤ T}

/-- A morphism between two objects in the comma category is a commutative square connecting the
    morphisms coming from the two objects using morphisms in the image of the functors `L` and `R`.
-/
@[ext]
structure CommaMorphism (X Y : Comma L R) where
  left : X.left ⟶ Y.left
  right : X.right ⟶ Y.right
  w : L.map left ≫ Y.hom = X.hom ≫ R.map right := by aesop_cat

-- Satisfying the inhabited linter
instance CommaMorphism.inhabited [Inhabited (Comma L R)] :
    Inhabited (CommaMorphism (default : Comma L R) default) :=
    ⟨{ left := 𝟙 _, right := 𝟙 _}⟩

attribute [reassoc (attr := simp)] CommaMorphism.w

instance commaCategory : Category (Comma L R) where
  Hom X Y := CommaMorphism X Y
  id X :=
    { left := 𝟙 X.left
      right := 𝟙 X.right }
  comp f g :=
    { left := f.left ≫ g.left
      right := f.right ≫ g.right }

namespace Comma

section

variable {X Y Z : Comma L R} {f : X ⟶ Y} {g : Y ⟶ Z}

-- Porting note: this lemma was added because `CommaMorphism.ext`
-- was not triggered automatically
@[ext]
lemma hom_ext (f g : X ⟶ Y) (h₁ : f.left = g.left) (h₂ : f.right = g.right) : f = g :=
  CommaMorphism.ext _ _ h₁ h₂

@[simp]
theorem id_left : (𝟙 X : CommaMorphism X X).left = 𝟙 X.left :=
  rfl

@[simp]
theorem id_right : (𝟙 X : CommaMorphism X X).right = 𝟙 X.right :=
  rfl

@[simp]
theorem comp_left : (f ≫ g).left = f.left ≫ g.left :=
  rfl

@[simp]
theorem comp_right : (f ≫ g).right = f.right ≫ g.right :=
  rfl

end

variable (L) (R)

/-- The functor sending an object `X` in the comma category to `X.left`. -/
@[simps]
def fst : Comma L R ⥤ A where
  obj X := X.left
  map f := f.left

/-- The functor sending an object `X` in the comma category to `X.right`. -/
@[simps]
def snd : Comma L R ⥤ B where
  obj X := X.right
  map f := f.right

/-- We can interpret the commutative square constituting a morphism in the comma category as a
    natural transformation between the functors `fst ⋙ L` and `snd ⋙ R` from the comma category
    to `T`, where the components are given by the morphism that constitutes an object of the comma
    category. -/
@[simps]
def natTrans : fst L R ⋙ L ⟶ snd L R ⋙ R where app X := X.hom

@[simp]
theorem eqToHom_left (X Y : Comma L R) (H : X = Y) :
    CommaMorphism.left (eqToHom H) = eqToHom (by cases H; rfl) := by
  cases H
  rfl

@[simp]
theorem eqToHom_right (X Y : Comma L R) (H : X = Y) :
    CommaMorphism.right (eqToHom H) = eqToHom (by cases H; rfl) := by
  cases H
  rfl

section

variable {L₁ L₂ L₃ : A ⥤ T} {R₁ R₂ R₃ : B ⥤ T}

/-- Extract the isomorphism between the left objects from an isomorphism in the comma category. -/
@[simps!]
def leftIso {X Y : Comma L₁ R₁} (α : X ≅ Y) : X.left ≅ Y.left := (fst L₁ R₁).mapIso α

/-- Extract the isomorphism between the right objects from an isomorphism in the comma category. -/
@[simps!]
def rightIso {X Y : Comma L₁ R₁} (α : X ≅ Y) : X.right ≅ Y.right := (snd L₁ R₁).mapIso α

/-- Construct an isomorphism in the comma category given isomorphisms of the objects whose forward
directions give a commutative square.
-/
@[simps]
def isoMk {X Y : Comma L₁ R₁} (l : X.left ≅ Y.left) (r : X.right ≅ Y.right)
    (h : L₁.map l.hom ≫ Y.hom = X.hom ≫ R₁.map r.hom := by aesop_cat) : X ≅ Y where
  hom :=
    { left := l.hom
      right := r.hom
      w := h }
  inv :=
    { left := l.inv
      right := r.inv
      w := by
        rw [← L₁.mapIso_inv l, Iso.inv_comp_eq, L₁.mapIso_hom, ← Category.assoc, h,
          Category.assoc, ← R₁.map_comp]
        simp }

section

variable {L R}
variable {L' : A' ⥤ T'} {R' : B' ⥤ T'}
  {F₁ : A ⥤ A'} {F₂ : B ⥤ B'} {F : T ⥤ T'}
  (α : F₁ ⋙ L' ⟶ L ⋙ F) (β : R ⋙ F ⟶ F₂ ⋙ R')

/-- The functor `Comma L R ⥤ Comma L' R'` induced by three functors `F₁`, `F₂`, `F`
and two natural transformations `F₁ ⋙ L' ⟶ L ⋙ F` and `R ⋙ F ⟶ F₂ ⋙ R'`. -/
@[simps]
def map : Comma L R ⥤ Comma L' R' where
  obj X :=
    { left := F₁.obj X.left
      right := F₂.obj X.right
      hom := α.app X.left ≫ F.map X.hom ≫ β.app X.right }
  map {X Y} φ :=
    { left := F₁.map φ.left
      right := F₂.map φ.right
      w := by
        dsimp
        rw [assoc, assoc]
        erw [α.naturality_assoc, ← β.naturality]
        dsimp
        rw [← F.map_comp_assoc, ← F.map_comp_assoc, φ.w] }

instance faithful_map [F₁.Faithful] [F₂.Faithful] : (map α β).Faithful where
  map_injective {X Y} f g h := by
    ext
    exact F₁.map_injective (congr_arg CommaMorphism.left h)
    exact F₂.map_injective (congr_arg CommaMorphism.right h)

instance full_map [F.Faithful] [F₁.Full] [F₂.Full] [IsIso α] [IsIso β] : (map α β).Full where
  map_surjective {X Y} φ :=
   ⟨{ left := F₁.preimage φ.left
      right := F₂.preimage φ.right
      w := F.map_injective (by
        rw [← cancel_mono (β.app _), ← cancel_epi (α.app _), F.map_comp, F.map_comp,
          assoc, assoc]
        erw [← α.naturality_assoc, β.naturality]
        dsimp
        rw [F₁.map_preimage, F₂.map_preimage]
        simpa using φ.w) }, by aesop_cat⟩

instance essSurj_map [F₁.EssSurj] [F₂.EssSurj] [F.Full] [IsIso α] [IsIso β] :
    (map α β).EssSurj where
  mem_essImage X :=
    ⟨{  left := F₁.objPreimage X.left
        right := F₂.objPreimage X.right
        hom := F.preimage ((inv α).app _ ≫ L'.map (F₁.objObjPreimageIso X.left).hom ≫
          X.hom ≫ R'.map (F₂.objObjPreimageIso X.right).inv ≫ (inv β).app _) },
            ⟨isoMk (F₁.objObjPreimageIso X.left) (F₂.objObjPreimageIso X.right) (by
              dsimp
              simp only [NatIso.isIso_inv_app, Functor.comp_obj, Functor.map_preimage, assoc,
                IsIso.inv_hom_id, comp_id, IsIso.hom_inv_id_assoc]
              rw [← R'.map_comp, Iso.inv_hom_id, R'.map_id, comp_id])⟩⟩

noncomputable instance isEquivalenceMap
    [F₁.IsEquivalence] [F₂.IsEquivalence] [F.Faithful] [F.Full] [IsIso α] [IsIso β] :
    (map α β).IsEquivalence where

end

/-- A natural transformation `L₁ ⟶ L₂` induces a functor `Comma L₂ R ⥤ Comma L₁ R`. -/
@[simps]
def mapLeft (l : L₁ ⟶ L₂) : Comma L₂ R ⥤ Comma L₁ R where
  obj X :=
    { left := X.left
      right := X.right
      hom := l.app X.left ≫ X.hom }
  map f :=
    { left := f.left
      right := f.right }

/-- The functor `Comma L R ⥤ Comma L R` induced by the identity natural transformation on `L` is
    naturally isomorphic to the identity functor. -/
@[simps!]
def mapLeftId : mapLeft R (𝟙 L) ≅ 𝟭 _ :=
  NatIso.ofComponents (fun X => isoMk (Iso.refl _) (Iso.refl _))

/-- The functor `Comma L₁ R ⥤ Comma L₃ R` induced by the composition of two natural transformations
    `l : L₁ ⟶ L₂` and `l' : L₂ ⟶ L₃` is naturally isomorphic to the composition of the two functors
    induced by these natural transformations. -/
@[simps!]
def mapLeftComp (l : L₁ ⟶ L₂) (l' : L₂ ⟶ L₃) :
    mapLeft R (l ≫ l') ≅ mapLeft R l' ⋙ mapLeft R l :=
  NatIso.ofComponents (fun X => isoMk (Iso.refl _) (Iso.refl _))

/-- Two equal natural transformations `L₁ ⟶ L₂` yield naturally isomorphic functors
    `Comma L₁ R ⥤ Comma L₂ R`. -/
@[simps!]
def mapLeftEq (l l' : L₁ ⟶ L₂) (h : l = l') : mapLeft R l ≅ mapLeft R l' :=
  NatIso.ofComponents (fun X => isoMk (Iso.refl _) (Iso.refl _))

/-- A natural isomorphism `L₁ ≅ L₂` induces an equivalence of categories
    `Comma L₁ R ≌ Comma L₂ R`. -/
@[simps!]
def mapLeftIso (i : L₁ ≅ L₂) : Comma L₁ R ≌ Comma L₂ R :=
  Equivalence.mk (mapLeft _ i.inv) (mapLeft _ i.hom)
    ((mapLeftId _ _).symm ≪≫ mapLeftEq _ _ _ i.hom_inv_id.symm ≪≫ mapLeftComp _ _ _)
    ((mapLeftComp _ _ _).symm ≪≫ mapLeftEq _ _ _ i.inv_hom_id ≪≫ mapLeftId _ _)

/-- A natural transformation `R₁ ⟶ R₂` induces a functor `Comma L R₁ ⥤ Comma L R₂`. -/
@[simps]
def mapRight (r : R₁ ⟶ R₂) : Comma L R₁ ⥤ Comma L R₂ where
  obj X :=
    { left := X.left
      right := X.right
      hom := X.hom ≫ r.app X.right }
  map f :=
    { left := f.left
      right := f.right }

/-- The functor `Comma L R ⥤ Comma L R` induced by the identity natural transformation on `R` is
    naturally isomorphic to the identity functor. -/
@[simps!]
def mapRightId : mapRight L (𝟙 R) ≅ 𝟭 _ :=
  NatIso.ofComponents (fun X => isoMk (Iso.refl _) (Iso.refl _))

/-- The functor `Comma L R₁ ⥤ Comma L R₃` induced by the composition of the natural transformations
    `r : R₁ ⟶ R₂` and `r' : R₂ ⟶ R₃` is naturally isomorphic to the composition of the functors
    induced by these natural transformations. -/
@[simps!]
def mapRightComp (r : R₁ ⟶ R₂) (r' : R₂ ⟶ R₃) :
    mapRight L (r ≫ r') ≅ mapRight L r ⋙ mapRight L r' :=
  NatIso.ofComponents (fun X => isoMk (Iso.refl _) (Iso.refl _))

/-- Two equal natural transformations `R₁ ⟶ R₂` yield naturally isomorphic functors
    `Comma L R₁ ⥤ Comma L R₂`. -/
@[simps!]
def mapRightEq (r r' : R₁ ⟶ R₂) (h : r = r') : mapRight L r ≅ mapRight L r' :=
  NatIso.ofComponents (fun X => isoMk (Iso.refl _) (Iso.refl _))

/-- A natural isomorphism `R₁ ≅ R₂` induces an equivalence of categories
    `Comma L R₁ ≌ Comma L R₂`. -/
@[simps!]
def mapRightIso (i : R₁ ≅ R₂) : Comma L R₁ ≌ Comma L R₂ :=
  Equivalence.mk (mapRight _ i.hom) (mapRight _ i.inv)
    ((mapRightId _ _).symm ≪≫ mapRightEq _ _ _ i.hom_inv_id.symm ≪≫ mapRightComp _ _ _)
    ((mapRightComp _ _ _).symm ≪≫ mapRightEq _ _ _ i.inv_hom_id ≪≫ mapRightId _ _)

end

section

variable {C : Type u₄} [Category.{v₄} C] {D : Type u₅} [Category.{v₅} D]

/-- The functor `(F ⋙ L, R) ⥤ (L, R)` -/
@[simps]
def preLeft (F : C ⥤ A) (L : A ⥤ T) (R : B ⥤ T) : Comma (F ⋙ L) R ⥤ Comma L R where
  obj X :=
    { left := F.obj X.left
      right := X.right
      hom := X.hom }
  map f :=
    { left := F.map f.left
      right := f.right
      w := by simpa using f.w }

/-- `Comma.preLeft` is a particular case of `Comma.map`,
but with better definitional properties. -/
def preLeftIso (F : C ⥤ A) (L : A ⥤ T) (R : B ⥤ T) :
    preLeft F L R ≅ map (F ⋙ L).rightUnitor.inv (R.rightUnitor.hom ≫ R.leftUnitor.inv) :=
  NatIso.ofComponents (fun X => isoMk (Iso.refl _) (Iso.refl _))

instance (F : C ⥤ A) (L : A ⥤ T) (R : B ⥤ T) [F.Faithful] : (preLeft F L R).Faithful :=
  Functor.Faithful.of_iso (preLeftIso F L R).symm

instance (F : C ⥤ A) (L : A ⥤ T) (R : B ⥤ T) [F.Full] : (preLeft F L R).Full :=
  Functor.Full.of_iso (preLeftIso F L R).symm

instance (F : C ⥤ A) (L : A ⥤ T) (R : B ⥤ T) [F.EssSurj] : (preLeft F L R).EssSurj :=
  Functor.essSurj_of_iso (preLeftIso F L R).symm

/-- If `F` is an equivalence, then so is `preLeft F L R`. -/
instance isEquivalence_preLeft (F : C ⥤ A) (L : A ⥤ T) (R : B ⥤ T) [F.IsEquivalence] :
    (preLeft F L R).IsEquivalence where

/-- The functor `(F ⋙ L, R) ⥤ (L, R)` -/
@[simps]
def preRight (L : A ⥤ T) (F : C ⥤ B) (R : B ⥤ T) : Comma L (F ⋙ R) ⥤ Comma L R where
  obj X :=
    { left := X.left
      right := F.obj X.right
      hom := X.hom }
  map f :=
    { left := f.left
      right := F.map f.right }

/-- `Comma.preRight` is a particular case of `Comma.map`,
but with better definitional properties. -/
def preRightIso (L : A ⥤ T) (F : C ⥤ B) (R : B ⥤ T) :
    preRight L F R ≅ map (L.leftUnitor.hom ≫ L.rightUnitor.inv) (F ⋙ R).rightUnitor.hom :=
  NatIso.ofComponents (fun X => isoMk (Iso.refl _) (Iso.refl _))

instance (L : A ⥤ T) (F : C ⥤ B) (R : B ⥤ T) [F.Faithful] : (preRight L F R).Faithful :=
  Functor.Faithful.of_iso (preRightIso L F R).symm

instance (L : A ⥤ T) (F : C ⥤ B) (R : B ⥤ T) [F.Full] : (preRight L F R).Full :=
  Functor.Full.of_iso (preRightIso L F R).symm

instance (L : A ⥤ T) (F : C ⥤ B) (R : B ⥤ T) [F.EssSurj] : (preRight L F R).EssSurj :=
  Functor.essSurj_of_iso (preRightIso L F R).symm

/-- If `F` is an equivalence, then so is `preRight L F R`. -/
instance isEquivalence_preRight (L : A ⥤ T) (F : C ⥤ B) (R : B ⥤ T) [F.IsEquivalence] :
    (preRight L F R).IsEquivalence where

/-- The functor `(L, R) ⥤ (L ⋙ F, R ⋙ F)` -/
@[simps]
def post (L : A ⥤ T) (R : B ⥤ T) (F : T ⥤ C) : Comma L R ⥤ Comma (L ⋙ F) (R ⋙ F) where
  obj X :=
    { left := X.left
      right := X.right
      hom := F.map X.hom }
  map f :=
    { left := f.left
      right := f.right
      w := by simp only [Functor.comp_map, ← F.map_comp, f.w] }

end

end Comma

end CategoryTheory
