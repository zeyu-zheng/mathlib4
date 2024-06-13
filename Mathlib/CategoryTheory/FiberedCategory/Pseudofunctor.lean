/-
Copyright (c) 2024 Calle Sönne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Lezeau, Calle Sönne
-/

import Mathlib.CategoryTheory.FiberedCategory.HasFibers
import Mathlib.CategoryTheory.Bicategory.Functor.Strict
import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.Bicategory.LocallyDiscrete

/-!
# The fibered category associated to a pseudofunctor

Given a category `𝒮` and any pseudofunctor valued in `Cat` we associate to it a fibered category
category `ℱ F ⥤ 𝒮`.

The category `ℱ F` is defined as follows:
* Objects: pairs `(S, a)` where `S` is an object of the base category and `a` is an object of the
  category `F(S)`
* Morphisms: morphisms `(R, b) ⟶ (S, a)` are defined as pairs `(f, h)` where `f : R ⟶ S` is a
  morphism in `𝒮` and `h : b ⟶ F(f)(a)`

The projection functor `ℱ F ⥤ 𝒮` is then given by projecting to the first factors, i.e.
* On objects, it sends `(S, a)` to `S`
* On morphisms, it sends `(f, h)` to `f`

We also provide a `HasFibers` instance `ℱ F`, such that the fiber over `S` is the category `F(S)`.

## References
[Vistoli2008] "Notes on Grothendieck Topologies, Fibered Categories and Descent Theory" by
Angelo Vistoli

-/

/-
TODO:
- Fix "↑F.toPrelaxFunctor.obj" instead of "F.obj"
- Fix naming
- (Later) splittings & functoriality
- Make `presheaf.lean` a special instance of the above
  - Isomorphism between the overcategory and fibered category associated to the corresponding
  presheaf?
-/



universe w v₁ v₂ v₃ u₁ u₂ u₃

open CategoryTheory Functor Category Opposite Discrete Bicategory

-- TODO: add @[pp_dot] in LocallyDiscrete
section mathlib_lemmas

lemma Cat.whiskerLeft_app {C D E : Cat} (F : C ⟶ D) {G H : D ⟶ E} (η : G ⟶ H) (X : C) :
    (F ◁ η).app X = η.app (F.obj X) :=
  CategoryTheory.whiskerLeft_app F η X

lemma Cat.whiskerRight_app {C D E : Cat} {F G : C ⟶ D} (H : D ⟶ E) (η : F ⟶ G) (X : C) :
    (η ▷ H).app X = H.map (η.app X) :=
  CategoryTheory.whiskerRight_app η H X

-- already in mathlib!
@[simp]
lemma Quiver.Hom.eqToHom_toLoc {C : Type u₁} [Category.{v₁} C] {a b : C}
    (h : a = b) : (eqToHom h).toLoc = eqToHom (congrArg LocallyDiscrete.mk h) := by
  subst h; rfl

end mathlib_lemmas

variable {𝒮 : Type u₁} [Category.{v₁} 𝒮] {F : Pseudofunctor (LocallyDiscrete 𝒮ᵒᵖ) Cat.{v₂, u₂}}

/-- The type of objects in the fibered category associated to a presheaf valued in types. -/
def ℱ (F : Pseudofunctor (LocallyDiscrete 𝒮ᵒᵖ) Cat.{v₂, u₂}) := (S : 𝒮) × (F.obj ⟨op S⟩)

@[simps]
instance ℱ.CategoryStruct : CategoryStruct (ℱ F) where
  -- Can I flip the second morphism?
  Hom X Y := (f : X.1 ⟶ Y.1) × (X.2 ⟶ (F.map f.op.toLoc).obj Y.2)
  id X := ⟨𝟙 X.1, (F.mapId ⟨op X.1⟩).inv.app X.2⟩
  comp {_ _ Z} f g := ⟨f.1 ≫ g.1, f.2 ≫ (F.map f.1.op.toLoc).map g.2 ≫
    (F.mapComp g.1.op.toLoc f.1.op.toLoc).inv.app Z.2⟩

@[ext]
lemma ℱ.hom_ext {a b : ℱ F} (f g : a ⟶ b) (hfg₁ : f.1 = g.1)
    (hfg₂ : f.2 = g.2 ≫ eqToHom (hfg₁ ▸ rfl)) : f = g := by
  apply Sigma.ext hfg₁
  rw [← conj_eqToHom_iff_heq _ _ rfl (hfg₁ ▸ rfl)]
  simp only [hfg₂, eqToHom_refl, id_comp]

-- Might not need this lemma in the end
lemma ℱ.hom_ext_iff {a b : ℱ F} (f g : a ⟶ b) : f = g ↔
    ∃ (hfg : f.1 = g.1), f.2 = g.2 ≫ eqToHom (hfg ▸ rfl) where
  mp := fun hfg => ⟨by rw [hfg], by simp [hfg]⟩
  mpr := fun ⟨hfg₁, hfg₂⟩ => ℱ.hom_ext f g hfg₁ hfg₂

@[simp]
protected lemma ℱ.id_comp {a b : ℱ F} (f : a ⟶ b) : 𝟙 a ≫ f = f := by
  ext
  · simp
  dsimp
  rw [F.mapComp_id_right_ofStrict_inv f.1.op.toLoc]
  rw [← (F.mapId ⟨op a.1⟩).inv.naturality_assoc f.2]
  conv_lhs =>
    congr; rfl;
    rw [← Cat.whiskerLeft_app, ← NatTrans.comp_app, ← assoc]
    rw [← Bicategory.whiskerLeft_comp, Iso.inv_hom_id]
  simp

@[simp]
protected lemma ℱ.comp_id {a b : ℱ F} (f : a ⟶ b) : f ≫ 𝟙 b = f := by
  ext
  · simp
  dsimp
  rw [F.mapComp_id_left_ofStrict_inv f.1.op.toLoc]
  rw [← Cat.whiskerRight_app, ← NatTrans.comp_app]
  nth_rw 1 [← assoc]
  rw [← Bicategory.comp_whiskerRight, Iso.inv_hom_id]
  simp

/-- The category structure on the fibered category associated to a presheaf valued in types. -/
instance : Category (ℱ F) where
  toCategoryStruct := ℱ.CategoryStruct
  id_comp := ℱ.id_comp
  comp_id := ℱ.comp_id
  -- This one is especially slow!
  assoc {a b c d} f g h := by
    ext
    · simp
    dsimp
    conv_lhs =>
      rw [assoc, assoc]
      rw [← (F.mapComp g.1.op.toLoc f.1.op.toLoc).inv.naturality_assoc h.2]
      rw [← Cat.whiskerLeft_app, ← NatTrans.comp_app]
      rw [F.map₂_associator_ofStrict_inv h.1.op.toLoc g.1.op.toLoc f.1.op.toLoc]
      rw [NatTrans.comp_app, NatTrans.comp_app, eqToHom_app, eqToHom_app, eqToHom_refl, id_comp]
    conv_rhs => simp only [Cat.comp_obj, Cat.comp_map, map_comp, assoc]
    congr 3
    rw [← Cat.whiskerRight_app, NatTrans.comp_app]
    simp only [Cat.comp_obj, assoc]

/-- The projection `ℱ F ⥤ 𝒮` given by projecting both objects and homs to the first factor -/
@[simps]
def ℱ.π (F : Pseudofunctor (LocallyDiscrete 𝒮ᵒᵖ) Cat.{v₂, u₂}) : ℱ F ⥤ 𝒮 where
  obj := fun X => X.1
  map := fun f => f.1

-- TODO: improve comment after I know final form of this...
/-- An object of `ℱ F` lying over `S`, given by some `a : F(T)` and `S ⟶ T` -/
abbrev ℱ.pullback_obj {R S : 𝒮} (a : F.obj ⟨op S⟩) (f : R ⟶ S) : ℱ F :=
  ⟨R, (F.map f.op.toLoc).obj a⟩

abbrev ℱ.pullback_map {R S : 𝒮} (a : F.obj ⟨op S⟩) (f : R ⟶ S) : ℱ.pullback_obj a f ⟶ ⟨S, a⟩ :=
  ⟨f, 𝟙 _⟩

instance ℱ.pullback_IsHomLift {R S : 𝒮} (a : F.obj ⟨op S⟩) (f : R ⟶ S) :
    IsHomLift (ℱ.π F) f (ℱ.pullback_map a f) :=
  -- TODO: rename
  instIsHomLiftMap (ℱ.π F) (ℱ.pullback_map a f)


abbrev ℱ.pullback_inducedMap {R S : 𝒮} {a : F.obj ⟨op S⟩} (f : R ⟶ S) {a' : ℱ F} (g : a'.1 ⟶ R)
    (φ' : a' ⟶ ⟨S, a⟩) [IsHomLift (ℱ.π F) (g ≫ f) φ'] : a' ⟶ ℱ.pullback_obj a f :=
  have : g ≫ f = φ'.1 := by simpa using IsHomLift.fac (ℱ.π F) (g ≫ f) φ'
  ⟨g, φ'.2 ≫ eqToHom (by simp [this.symm]) ≫ (F.mapComp f.op.toLoc g.op.toLoc).hom.app a⟩

instance ℱ.pullback_inducedMap_isHomLift {R S : 𝒮} (a : F.obj ⟨op S⟩) {f : R ⟶ S} {a' : ℱ F}
    {φ' : a' ⟶ ⟨S, a⟩} {g : a'.1 ⟶ R} [IsHomLift (ℱ.π F) (g ≫ f) φ'] :
      IsHomLift (ℱ.π F) g (ℱ.pullback_inducedMap f g φ') :=
  instIsHomLiftMap (ℱ.π F) (ℱ.pullback_inducedMap f g φ')

lemma ℱ.pullback_IsPullback {R S : 𝒮} (a : F.obj ⟨op S⟩) (f : R ⟶ S) :
    IsStronglyCartesian (ℱ.π F) f (ℱ.pullback_map a f) where
  universal_property' := by
    intros a' g φ' hφ'
    -- This should be included in API somehow...
    have : g ≫ f = φ'.1 := by simpa using IsHomLift.fac (ℱ.π F) (g ≫ f) φ'
    use ℱ.pullback_inducedMap f g φ'
    refine ⟨⟨inferInstance, ?_⟩, ?_⟩
    ext
    · exact this
    · simp
    rintro χ' ⟨hχ', hχ'₁⟩
    symm at hχ'₁
    subst hχ'₁
    -- Again this should also be included in API somehow
    have hgχ' : g = χ'.1 := by simpa using IsHomLift.fac (ℱ.π F) g χ'
    subst hgχ'
    ext
    · simp
    simp

/-- `ℱ.π` is a fibered category. -/
instance : IsFibered (ℱ.π F) := by
  apply IsFibered.of_has_pullbacks'
  intros a R f
  use ℱ.pullback_obj a.2 f, ℱ.pullback_map a.2 f
  exact ℱ.pullback_IsPullback a.2 f

variable (F) (S : 𝒮)

@[simps]
def ℱ.ι : F.obj ⟨op S⟩ ⥤ ℱ F where
  obj := fun a => ⟨S, a⟩
  map := @fun a b φ => ⟨𝟙 S, φ ≫ (F.mapId ⟨op S⟩).inv.app b⟩
  map_id := fun a => by ext <;> simp
  map_comp := by
    intro a b c φ ψ
    ext
    · simp
    dsimp
    conv_rhs =>
      congr; rw [assoc]; congr; rfl
      rw [Functor.map_comp, assoc, ← (F.mapId ⟨op S⟩).inv.naturality_assoc ψ]
      rw [← Cat.whiskerRight_app, ← NatTrans.comp_app, F.mapComp_id_left_ofStrict_inv]
      rw [← assoc (h := eqToHom _), inv_hom_whiskerRight]
    simp


@[simps]
def ℱ.comp_iso : (ℱ.ι F S) ⋙ ℱ.π F ≅ (const (F.obj ⟨op S⟩)).obj S where
  hom := { app := fun a => 𝟙 _ }
  inv := { app := fun a => 𝟙 _ }

lemma ℱ.comp_const : (ℱ.ι F S) ⋙ ℱ.π F = (const (F.obj ⟨op S⟩)).obj S := by
  apply Functor.ext_of_iso (ℱ.comp_iso F S) <;> simp

noncomputable instance : Functor.Full (Fiber.InducedFunctor (ℱ.comp_const F S)) where
  map_surjective := by
    intro X Y f
    have hf : f.1.1 = 𝟙 S := by simpa using (IsHomLift.fac (ℱ.π F) (𝟙 S) f.1).symm
    use f.1.2 ≫ eqToHom (by simp [hf]) ≫ (F.mapId ⟨op S⟩).hom.app Y
    ext <;> simp [hf]

instance : Functor.Faithful (Fiber.InducedFunctor (ℱ.comp_const F S)) where
  map_injective := by
    intros a b f g heq
    -- can be made a one liner...
    rw [← Subtype.val_inj] at heq
    obtain ⟨_, heq₂⟩ := (ℱ.hom_ext_iff _ _).1 heq
    simpa [cancel_mono] using heq₂

noncomputable instance : Functor.EssSurj (Fiber.InducedFunctor (ℱ.comp_const F S)) := by
  apply essSurj_of_surj
  intro Y
  have hYS : Y.1.1 = S := by simpa using Y.2
  use (hYS.symm ▸ Y.1.2)
  apply Subtype.val_inj.1
  apply Sigma.ext <;> simp [hYS]

noncomputable instance : Functor.IsEquivalence (Fiber.InducedFunctor (ℱ.comp_const F S)) where

noncomputable instance : HasFibers (ℱ.π F) where
  Fib S := F.obj ⟨op S⟩
  ι := ℱ.ι F
  comp_const := ℱ.comp_const F
