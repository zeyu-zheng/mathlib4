/-
Copyright (c) 2024 Calle Sönne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Lezeau, Calle Sönne
-/

import Mathlib.CategoryTheory.Bicategory.Grothendieck
import Mathlib.CategoryTheory.FiberedCategory.HasFibers

/-!
# The fibered category obtained from the Grothendieck construction

Given a category `𝒮` and any pseudofunctor valued in `Cat`, the Grothendieck construction
associates to it a category `∫ F` and a functor `∫ F ⥤ 𝒮`. In this file, we show that this functor
makes `∫ F` a fibered category over `𝒮`.

We also provide a `HasFibers` instance `∫ F`, such that the fiber over `S` is the
category `F(S)`.

## References
[Vistoli2008] "Notes on Grothendieck Topologies, Fibered Categories and Descent Theory" by
Angelo Vistoli

-/

/-
TODO:
- Fix naming
- Make `presheaf.lean` a special instance of the above
  - Isomorphism between the overcategory and fibered category associated to the corresponding
  presheaf?
-/

namespace CategoryTheory

universe w v₁ v₂ v₃ u₁ u₂ u₃

open CategoryTheory Functor Category Opposite Discrete Bicategory Pseudofunctor.Grothendieck

variable {𝒮 : Type u₁} [Category.{v₁} 𝒮] {F : Pseudofunctor (LocallyDiscrete 𝒮ᵒᵖ) Cat.{v₂, u₂}}

section

variable {R S : 𝒮} (a : F.obj ⟨op S⟩) (f : R ⟶ S)

-- TODO: improve comment after I know final form of this...
/-- An object of `∫ F` lying over `S`, given by some `a : F(T)` and `S ⟶ T` -/
abbrev pullback_obj : ∫ F := ⟨R, (F.map f.op.toLoc).obj a⟩

abbrev pullback_map : pullback_obj a f ⟶ ⟨S, a⟩ := ⟨f, 𝟙 _⟩

instance pullback_IsHomLift : IsHomLift (forget F) f (pullback_map a f) :=
  instIsHomLiftMap (forget F) (pullback_map a f)

-- TODO a implicit here?
abbrev pullback_inducedMap {a : F.obj ⟨op S⟩} (f : R ⟶ S) {a' : ∫ F} (g : a'.1 ⟶ R)
    (φ' : a' ⟶ ⟨S, a⟩) [IsHomLift (forget F) (g ≫ f) φ'] : a' ⟶ pullback_obj a f :=
  have : g ≫ f = φ'.1 := by simpa using IsHomLift.fac (forget F) (g ≫ f) φ'
  ⟨g, φ'.2 ≫ eqToHom (by simp [this.symm]) ≫ (F.mapComp f.op.toLoc g.op.toLoc).hom.app a⟩

instance pullback_inducedMap_isHomLift {a : F.obj ⟨op S⟩} (f : R ⟶ S) {a' : ∫ F}
    {φ' : a' ⟶ ⟨S, a⟩} {g : a'.1 ⟶ R} [IsHomLift (forget F) (g ≫ f) φ'] :
      IsHomLift (forget F) g (pullback_inducedMap f g φ') :=
  instIsHomLiftMap (forget F) (pullback_inducedMap f g φ')

lemma pullback_IsPullback : IsStronglyCartesian (forget F) f (pullback_map a f) where
  universal_property' := by
    intros a' g φ' hφ'
    have : g ≫ f = φ'.1 := by simpa using IsHomLift.fac (forget F) (g ≫ f) φ'
    use pullback_inducedMap f g φ'
    refine ⟨⟨inferInstance, ?_⟩, ?_⟩
    ext
    · exact this
    · simp
    rintro χ' ⟨hχ'.symm, hχ'₁⟩
    subst hχ'₁
    -- TODO: subst_hom_lift here? Need better version for that ....
    have hgχ' : g = χ'.1 := by simpa using IsHomLift.fac (forget F) g χ'
    subst hgχ'
    ext <;> simp

end

/-- `π` is a fibered category. -/
instance : IsFibered (forget F) := by
  apply IsFibered.of_has_pullbacks'
  intros a R f
  use pullback_obj a.2 f, pullback_map a.2 f
  exact pullback_IsPullback a.2 f

-- section?
variable (F) (S : 𝒮)

@[simps]
def ι : F.obj ⟨op S⟩ ⥤ ∫ F where
  obj := fun a => ⟨S, a⟩
  map := @fun a b φ => ⟨𝟙 S, φ ≫ (F.mapId ⟨op S⟩).inv.app b⟩
  map_id := fun a => by ext <;> simp
  map_comp := by
    intro a b c φ ψ
    ext
    · simp
    dsimp
    slice_rhs 2 4 =>
      rw [Functor.map_comp, assoc, ← (F.mapId ⟨op S⟩).inv.naturality_assoc ψ]
      rw [← Cat.whiskerRight_app, ← NatTrans.comp_app, F.mapComp_id_left_inv]
      congr; rfl; congr; rfl
      rw [← assoc, inv_hom_whiskerRight]
    simp

@[simps]
def comp_iso : (ι F S) ⋙ forget F ≅ (const (F.obj ⟨op S⟩)).obj S where
  hom := { app := fun a => 𝟙 _ }
  inv := { app := fun a => 𝟙 _ }

lemma comp_const : (ι F S) ⋙ forget F = (const (F.obj ⟨op S⟩)).obj S := by
  apply Functor.ext_of_iso (comp_iso F S) <;> simp

noncomputable instance : Functor.Full (Fiber.InducedFunctor (comp_const F S)) where
  map_surjective := by
    intro X Y f
    have hf : f.1.1 = 𝟙 S := by simpa using (IsHomLift.fac (forget F) (𝟙 S) f.1).symm
    use f.1.2 ≫ eqToHom (by simp [hf]) ≫ (F.mapId ⟨op S⟩).hom.app Y
    ext <;> simp [hf]

instance : Functor.Faithful (Fiber.InducedFunctor (comp_const F S)) where
  map_injective := by
    intros a b f g heq
    -- can be made a one liner...
    rw [← Subtype.val_inj] at heq
    obtain ⟨_, heq₂⟩ := (hom_ext_iff _ _).1 heq
    simpa [cancel_mono] using heq₂

noncomputable instance : Functor.EssSurj (Fiber.InducedFunctor (comp_const F S)) := by
  apply essSurj_of_surj
  intro Y
  have hYS : Y.1.1 = S := by simpa using Y.2
  use (hYS.symm ▸ Y.1.2)
  apply Subtype.val_inj.1
  ext <;> simp [hYS]

noncomputable instance : Functor.IsEquivalence (Fiber.InducedFunctor (comp_const F S)) where

noncomputable instance : HasFibers (forget F) where
  Fib S := F.obj ⟨op S⟩
  ι := ι F
  comp_const := comp_const F

end CategoryTheory
