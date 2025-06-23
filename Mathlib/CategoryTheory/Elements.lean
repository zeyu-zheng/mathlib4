import Mathlib.Tactic.Have
/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.CategoryTheory.Comma.StructuredArrow
import Mathlib.CategoryTheory.Groupoid
import Mathlib.CategoryTheory.PUnit

/-!
# The category of elements

This file defines the category of elements, also known as (a special case of) the Grothendieck
construction.

Given a functor `F : C ⥤ Type`, an object of `F.Elements` is a pair `(X : C, x : F.obj X)`.
A morphism `(X, x) ⟶ (Y, y)` is a morphism `f : X ⟶ Y` in `C`, so `F.map f` takes `x` to `y`.

## Implementation notes

This construction is equivalent to a special case of a comma construction, so this is mostly just a
more convenient API. We prove the equivalence in
`CategoryTheory.CategoryOfElements.structuredArrowEquivalence`.

## References
* [Emily Riehl, *Category Theory in Context*, Section 2.4][riehl2017]
* <https://en.wikipedia.org/wiki/Category_of_elements>
* <https://ncatlab.org/nlab/show/category+of+elements>

## Tags
category of elements, Grothendieck construction, comma category
-/


namespace CategoryTheory

universe w v u

variable {C : Type u} [Category.{v} C]

/-- The type of objects for the category of elements of a functor `F : C ⥤ Type`
is a pair `(X : C, x : F.obj X)`.
-/
def Functor.Elements (F : C ⥤ Type w) :=
  Σc : C, F.obj c

/-- Constructor for the type `F.Elements` when `F` is a functor to types. -/
abbrev Functor.elementsMk (F : C ⥤ Type w) (X : C) (x : F.obj X) : F.Elements := ⟨X, x⟩

-- Porting note: added because Sigma.ext would be triggered automatically
lemma Functor.Elements.ext {F : C ⥤ Type w} (x y : F.Elements) (h₁ : x.fst = y.fst)
    (h₂ : F.map (eqToHom h₁) x.snd = y.snd) : x = y := by
  cases x
  cases y
  cases h₁
  simp only [eqToHom_refl, FunctorToTypes.map_id_apply] at h₂
  simp [h₂]

/-- The category structure on `F.Elements`, for `F : C ⥤ Type`.
    A morphism `(X, x) ⟶ (Y, y)` is a morphism `f : X ⟶ Y` in `C`, so `F.map f` takes `x` to `y`.
 -/
instance categoryOfElements (F : C ⥤ Type w) : Category.{v} F.Elements where
  Hom p q := { f : p.1 ⟶ q.1 // (F.map f) p.2 = q.2 }
  id p := ⟨𝟙 p.1, by aesop_cat⟩
  comp {X Y Z} f g := ⟨f.val ≫ g.val, by simp [f.2, g.2]⟩

namespace CategoryOfElements

/-- Constructor for morphisms in the category of elements of a functor to types. -/
@[simps]
def homMk {F : C ⥤ Type w} (x y : F.Elements) (f : x.1 ⟶ y.1) (hf : F.map f x.snd = y.snd) :
    x ⟶ y :=
  ⟨f, hf⟩

@[ext]
theorem ext (F : C ⥤ Type w) {x y : F.Elements} (f g : x ⟶ y) (w : f.val = g.val) : f = g :=
  Subtype.ext_val w

@[simp]
theorem comp_val {F : C ⥤ Type w} {p q r : F.Elements} {f : p ⟶ q} {g : q ⟶ r} :
    (f ≫ g).val = f.val ≫ g.val :=
  rfl

@[simp]
theorem id_val {F : C ⥤ Type w} {p : F.Elements} : (𝟙 p : p ⟶ p).val = 𝟙 p.1 :=
  rfl

@[simp]
theorem map_snd {F : C ⥤ Type w} {p q : F.Elements} (f : p ⟶ q) : (F.map f.val) p.2 = q.2 :=
  f.property

end CategoryOfElements

instance groupoidOfElements {G : Type u} [Groupoid.{v} G] (F : G ⥤ Type w) :
    Groupoid F.Elements where
  inv {p q} f :=
    ⟨Groupoid.inv f.val,
      calc
        F.map (Groupoid.inv f.val) q.2 = F.map (Groupoid.inv f.val) (F.map f.val p.2) := by rw [f.2]
        _ = (F.map f.val ≫ F.map (Groupoid.inv f.val)) p.2 := rfl
        _ = p.2 := by
          rw [← F.map_comp]
          simp
        ⟩
  inv_comp _ := by
    ext
    simp
  comp_inv _ := by
    ext
    simp

namespace CategoryOfElements

variable (F : C ⥤ Type w)

/-- The functor out of the category of elements which forgets the element. -/
@[simps]
def π : F.Elements ⥤ C where
  obj X := X.1
  map f := f.val

instance : (π F).Faithful where

instance : (π F).ReflectsIsomorphisms where
  reflects {X Y} f h := ⟨⟨⟨inv ((π F).map f),
    by rw [← map_snd f, ← FunctorToTypes.map_comp_apply]; simp⟩, by aesop_cat⟩⟩

/-- A natural transformation between functors induces a functor between the categories of elements.
-/
@[simps]
def map {F₁ F₂ : C ⥤ Type w} (α : F₁ ⟶ F₂) : F₁.Elements ⥤ F₂.Elements where
  obj t := ⟨t.1, α.app t.1 t.2⟩
  map {t₁ t₂} k := ⟨k.1, by simpa [map_snd] using (FunctorToTypes.naturality _ _ α k.1 t₁.2).symm⟩

@[simp]
theorem map_π {F₁ F₂ : C ⥤ Type w} (α : F₁ ⟶ F₂) : map α ⋙ π F₂ = π F₁ :=
  rfl

/-- The forward direction of the equivalence `F.Elements ≅ (*, F)`. -/
def toStructuredArrow : F.Elements ⥤ StructuredArrow PUnit F where
  obj X := StructuredArrow.mk fun _ => X.2
  map {X Y} f := StructuredArrow.homMk f.val (by funext; simp [f.2])

@[simp]
theorem toStructuredArrow_obj (X) :
    (toStructuredArrow F).obj X =
      { left := ⟨⟨⟩⟩
        right := X.1
        hom := fun _ => X.2 } :=
  rfl

@[simp]
theorem to_comma_map_right {X Y} (f : X ⟶ Y) : ((toStructuredArrow F).map f).right = f.val :=
  rfl

/-- The reverse direction of the equivalence `F.Elements ≅ (*, F)`. -/
def fromStructuredArrow : StructuredArrow PUnit F ⥤ F.Elements where
  obj X := ⟨X.right, X.hom PUnit.unit⟩
  map f := ⟨f.right, congr_fun f.w.symm PUnit.unit⟩

@[simp]
theorem fromStructuredArrow_obj (X) : (fromStructuredArrow F).obj X = ⟨X.right, X.hom PUnit.unit⟩ :=
  rfl

@[simp]
theorem fromStructuredArrow_map {X Y} (f : X ⟶ Y) :
    (fromStructuredArrow F).map f = ⟨f.right, congr_fun f.w.symm PUnit.unit⟩ :=
  rfl

/-- The equivalence between the category of elements `F.Elements`
    and the comma category `(*, F)`. -/
@[simps! functor_obj functor_map inverse_obj inverse_map unitIso_hom
  unitIso_inv counitIso_hom counitIso_inv]
def structuredArrowEquivalence : F.Elements ≌ StructuredArrow PUnit F :=
  Equivalence.mk (toStructuredArrow F) (fromStructuredArrow F)
    (NatIso.ofComponents fun X => eqToIso (by aesop_cat))
    (NatIso.ofComponents fun X => StructuredArrow.isoMk (Iso.refl _))

open Opposite

/-- The forward direction of the equivalence `F.Elementsᵒᵖ ≅ (yoneda, F)`,
given by `CategoryTheory.yonedaEquiv`.
-/
@[simps]
def toCostructuredArrow (F : Cᵒᵖ ⥤ Type v) : F.Elementsᵒᵖ ⥤ CostructuredArrow yoneda F where
  obj X := CostructuredArrow.mk (yonedaEquiv.symm (unop X).2)
  map f := by
    fapply CostructuredArrow.homMk
    · exact f.unop.val.unop
    · ext Z y
      dsimp [yonedaEquiv]
      simp only [FunctorToTypes.map_comp_apply, ← f.unop.2]

/-- The reverse direction of the equivalence `F.Elementsᵒᵖ ≅ (yoneda, F)`,
given by `CategoryTheory.yonedaEquiv`.
-/
@[simps]
def fromCostructuredArrow (F : Cᵒᵖ ⥤ Type v) : (CostructuredArrow yoneda F)ᵒᵖ ⥤ F.Elements where
  obj X := ⟨op (unop X).1, yonedaEquiv.1 (unop X).3⟩
  map {X Y} f :=
    ⟨f.unop.1.op, by
      convert (congr_fun ((unop X).hom.naturality f.unop.left.op) (𝟙 _)).symm
      simp only [Equiv.toFun_as_coe, Quiver.Hom.unop_op, yonedaEquiv_apply, types_comp_apply,
        Category.comp_id, yoneda_obj_map]
      have : yoneda.map f.unop.left ≫ (unop X).hom = (unop Y).hom := by
        convert f.unop.3
      erw [← this]
      simp only [yoneda_map_app, FunctorToTypes.comp]
      erw [Category.id_comp]⟩

@[simp]
theorem fromCostructuredArrow_obj_mk (F : Cᵒᵖ ⥤ Type v) {X : C} (f : yoneda.obj X ⟶ F) :
    (fromCostructuredArrow F).obj (op (CostructuredArrow.mk f)) = ⟨op X, yonedaEquiv.1 f⟩ :=
  rfl

/-- The unit of the equivalence `F.Elementsᵒᵖ ≅ (yoneda, F)` is indeed iso. -/
theorem from_toCostructuredArrow_eq (F : Cᵒᵖ ⥤ Type v) :
    (toCostructuredArrow F).rightOp ⋙ fromCostructuredArrow F = 𝟭 _ := by
  refine Functor.ext ?_ ?_
  intro X
  exact Functor.Elements.ext _ _ rfl (by simp [yonedaEquiv])
  intro X Y f
  have : ∀ {a b : F.Elements} (H : a = b),
      (eqToHom H).1 = eqToHom (show a.fst = b.fst by cases H; rfl) := by
    rintro _ _ rfl
    simp
  ext
  simp [this]

/-- The counit of the equivalence `F.Elementsᵒᵖ ≅ (yoneda, F)` is indeed iso. -/
theorem to_fromCostructuredArrow_eq (F : Cᵒᵖ ⥤ Type v) :
    (fromCostructuredArrow F).rightOp ⋙ toCostructuredArrow F = 𝟭 _ := by
  refine Functor.ext ?_ ?_
  intro X
  cases' X with X_left X_right X_hom
  cases X_right
  simp only [Functor.id_obj, Functor.rightOp_obj, toCostructuredArrow_obj, Functor.comp_obj,
    CostructuredArrow.mk]
  congr
  ext x f
  convert congr_fun (X_hom.naturality f.op).symm (𝟙 X_left)
  simp
  aesop

/-- The equivalence `F.Elementsᵒᵖ ≅ (yoneda, F)` given by yoneda lemma. -/
@[simps! functor_obj functor_map inverse_obj inverse_map unitIso_inv counitIso_hom counitIso_inv]
def costructuredArrowYonedaEquivalence (F : Cᵒᵖ ⥤ Type v) :
    F.Elementsᵒᵖ ≌ CostructuredArrow yoneda F :=
  Equivalence.mk (toCostructuredArrow F) (fromCostructuredArrow F).rightOp
    (NatIso.op (eqToIso (from_toCostructuredArrow_eq F))) (eqToIso <| to_fromCostructuredArrow_eq F)

-- Porting note:
-- Running `@[simps! unitIso_hom]` is mysteriously slow.
-- We separate it out to avoid needing to increase the maxHeartbeats.
attribute [simps! unitIso_hom] costructuredArrowYonedaEquivalence

/-- The equivalence `(-.Elements)ᵒᵖ ≅ (yoneda, -)` of is actually a natural isomorphism of functors.
-/
theorem costructuredArrow_yoneda_equivalence_naturality {F₁ F₂ : Cᵒᵖ ⥤ Type v} (α : F₁ ⟶ F₂) :
    (map α).op ⋙ toCostructuredArrow F₂ = toCostructuredArrow F₁ ⋙ CostructuredArrow.map α := by
  fapply Functor.ext
  intro X
  simp only [CostructuredArrow.map_mk, toCostructuredArrow_obj, Functor.op_obj,
    Functor.comp_obj]
  congr
  ext _ f
  simpa using congr_fun (α.naturality f.op).symm (unop X).snd
  simp [autoParam]

/-- The equivalence `F.elementsᵒᵖ ≌ (yoneda, F)` is compatible with the forgetful functors. -/
@[simps!]
def costructuredArrowYonedaEquivalenceFunctorProj (F : Cᵒᵖ ⥤ Type v) :
    (costructuredArrowYonedaEquivalence F).functor ⋙ CostructuredArrow.proj _ _ ≅ (π F).leftOp :=
  Iso.refl _

/-- The equivalence `F.elementsᵒᵖ ≌ (yoneda, F)` is compatible with the forgetful functors. -/
@[simps!]
def costructuredArrowYonedaEquivalenceInverseπ (F : Cᵒᵖ ⥤ Type v) :
    (costructuredArrowYonedaEquivalence F).inverse ⋙ (π F).leftOp ≅ CostructuredArrow.proj _ _ :=
  Iso.refl _

end CategoryOfElements

namespace Functor

/--
The initial object in the category of elements for a representable functor. In `isInitial` it is
shown that this is initial.
-/
def Elements.initial (A : C) : (yoneda.obj A).Elements :=
  ⟨Opposite.op A, 𝟙 _⟩

/-- Show that `Elements.initial A` is initial in the category of elements for the `yoneda` functor.
-/
def Elements.isInitial (A : C) : Limits.IsInitial (Elements.initial A) where
  desc s := ⟨s.pt.2.op, Category.comp_id _⟩
  uniq s m _ := by
    simp_rw [← m.2]
    dsimp [Elements.initial]
    simp
  fac := by rintro s ⟨⟨⟩⟩

end Functor

end CategoryTheory
