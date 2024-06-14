/-
Copyright (c) 2024 Calle Sönne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Calle Sönne
-/

import Mathlib.CategoryTheory.Bicategory.Functor.Pseudofunctor
import Mathlib.CategoryTheory.Bicategory.EqToHom
import Mathlib.CategoryTheory.Bicategory.Strict

/-!
# Bifunctors between strict bicategories

This file develops some API for working with bifunctors between strict bicategories. In those cases,
the properties can be simplified since the associators and unitors are eqToIsos.

-/

namespace CategoryTheory

open Category Bicategory

universe w₂ w₁ v₂ v₁ u₂ u₁ v u

section

variable {C : Type u} [Category.{v} C]

lemma eqToHom_conj_iff {a b c d : C} (f : a ⟶ b) (g : c ⟶ d) (hac : a = c) (hdb : d = b) :
    f = eqToHom hac ≫ g ≫ eqToHom hdb ↔ eqToHom hac.symm ≫ f ≫ eqToHom hdb.symm = g := by
  rw [eqToHom_comp_iff, comp_eqToHom_iff, assoc]

end

open CategoryTheory Bicategory


variable {B : Type u₂} [Bicategory.{w₂, v₂} B] [Strict B]
variable {C : Type u₁} [Bicategory.{w₁, v₁} C] [Strict C]

section

variable (F : OplaxFunctor B C)

lemma map₂_leftUnitor_ofStrict {a b : B} (f : a ⟶ b) : (F.mapComp (𝟙 a)) f ≫ F.mapId a ▷ F.map f =
    eqToHom (by simp only [id_comp]) := by
  have h := by simpa using F.map₂_leftUnitor f
  rw [← assoc, ← comp_eqToHom_iff (id_comp (F.map f)).symm, eqToHom_trans] at h
  exact h.symm

lemma map₂_rightUnitor_ofStrict {a b : B} (f : a ⟶ b) : (F.mapComp f) (𝟙 b) ≫ F.map f ◁ F.mapId b =
    eqToHom (by simp) := by
  have h := by simpa using F.map₂_rightUnitor f
  rw [← assoc, ← comp_eqToHom_iff (comp_id (F.map f)).symm, eqToHom_trans] at h
  exact h.symm

lemma map₂_associator_ofStrict {a b c d : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
    F.mapComp f (g ≫ h) ≫ F.map f ◁ F.mapComp g h = eqToHom (by simp) ≫
    (F.mapComp (f ≫ g) h ≫ (F.mapComp f g) ▷ F.map h) ≫ eqToHom (by simp) := by
  simpa [eqToHom_comp_iff] using F.map₂_associator f g h

end

namespace Pseudofunctor

variable (F : Pseudofunctor B C)

lemma mapComp_id_left_ofStrict {a b : B} (f : a ⟶ b) : F.mapComp (𝟙 a) f =
    eqToIso (by simp) ≪≫ (whiskerRightIso (F.mapId a) (F.map f)).symm := by
  ext
  simp only [Iso.trans_hom, eqToIso.hom, Iso.symm_hom, Iso.eq_comp_inv]
  apply map₂_leftUnitor_ofStrict F.toOplax

lemma mapComp_id_left_ofStrict_hom {a b : B} (f : a ⟶ b) : (F.mapComp (𝟙 a) f).hom =
    eqToHom (by simp) ≫ (F.mapId a).inv ▷ F.map f := by
  simp [mapComp_id_left_ofStrict]

lemma mapComp_id_left_ofStrict_inv {a b : B} (f : a ⟶ b) : (F.mapComp (𝟙 a) f).inv =
    (F.mapId a).hom ▷ F.map f ≫ eqToHom (by simp) := by
  simp [mapComp_id_left_ofStrict]

lemma mapId_whiskerRightIso_ofStrict {a b : B} (f : a ⟶ b) :
    (whiskerRightIso (F.mapId a) (F.map f)) = (F.mapComp (𝟙 a) f).symm ≪≫ eqToIso (by simp) := by
  simp [mapComp_id_left_ofStrict]

lemma mapId_whiskerRight_ofStrict_hom {a b : B} (f : a ⟶ b) :
    (F.mapId a).hom ▷ F.map f = ((F.mapComp (𝟙 a)) f).inv ≫ eqToHom (by simp) := by
  simp [mapComp_id_left_ofStrict]

lemma mapId_whiskerRight_ofStrict_inv {a b : B} (f : a ⟶ b) :
    (F.mapId a).inv ▷ F.map f = eqToHom (by simp) ≫ ((F.mapComp (𝟙 a)) f).hom := by
  simp [mapComp_id_left_ofStrict]

lemma mapComp_id_right_ofStrict {a b : B} (f : a ⟶ b) : F.mapComp f (𝟙 b) =
    eqToIso (by simp) ≪≫ (whiskerLeftIso (F.map f) (F.mapId b)).symm := by
  ext
  simp only [Iso.trans_hom, eqToIso.hom, Iso.symm_hom, Iso.eq_comp_inv]
  apply map₂_rightUnitor_ofStrict F.toOplax

lemma mapComp_id_right_ofStrict_hom {a b : B} (f : a ⟶ b) : (F.mapComp f (𝟙 b)).hom =
    eqToHom (by simp) ≫ F.map f ◁ (F.mapId b).inv := by
  simp [mapComp_id_right_ofStrict]

lemma mapComp_id_right_ofStrict_inv {a b : B} (f : a ⟶ b) : (F.mapComp f (𝟙 b)).inv =
    ((F.map f) ◁ (F.mapId b).hom) ≫ eqToHom (by simp) := by
  simp [mapComp_id_right_ofStrict]

lemma mapId_whiskerLeft_ofStrict {a b : B} (f : a ⟶ b) :
    whiskerLeftIso (F.map f) (F.mapId b) = (F.mapComp f (𝟙 b)).symm ≪≫ eqToIso (by simp) := by
  simp [mapComp_id_right_ofStrict]

lemma mapId_whiskerLeft_ofStrict_hom {a b : B} (f : a ⟶ b) :
    (F.map f) ◁ (F.mapId b).hom = ((F.mapComp f (𝟙 b)).inv) ≫ eqToHom (by simp) := by
  simp [mapComp_id_right_ofStrict]

lemma mapId_whiskerLeft_ofStrict_inv {a b : B} (f : a ⟶ b) :
    (F.map f) ◁ (F.mapId b).inv = eqToHom (by simp) ≫ (F.mapComp f (𝟙 b)).hom := by
  simp [mapComp_id_right_ofStrict]

lemma map₂_associator_ofStrict_iso {a b c d : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
    (F.mapComp f (g ≫ h)) ≪≫ (whiskerLeftIso (F.map f) (F.mapComp g h))
    = eqToIso (by simp) ≪≫ ((F.mapComp (f ≫ g) h) ≪≫
    whiskerRightIso (F.mapComp f g) (F.map h)) ≪≫ eqToIso (by simp) := by
  ext
  apply map₂_associator_ofStrict F.toOplax

lemma map₂_associator_ofStrict_hom {a b c d : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
    (F.mapComp f (g ≫ h)).hom ≫ (F.map f) ◁ (F.mapComp g h).hom
    = eqToHom (by simp) ≫ ((F.mapComp (f ≫ g) h).hom ≫
    (F.mapComp f g).hom ▷ F.map h) ≫ eqToHom (by simp) := by
  apply map₂_associator_ofStrict F.toOplax

lemma map₂_associator_ofStrict_inv {a b c d : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
    (F.map f) ◁ (F.mapComp g h).inv ≫ (F.mapComp f (g ≫ h)).inv
    = eqToHom (by simp) ≫ ((F.mapComp f g).inv ▷ F.map h ≫
    (F.mapComp (f ≫ g) h).inv) ≫ eqToHom (by simp) := by
  simpa using congrArg (·.inv) (map₂_associator_ofStrict_iso F f g h)

end Pseudofunctor
