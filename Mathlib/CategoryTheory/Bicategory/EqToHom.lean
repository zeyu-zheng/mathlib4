import Mathlib.CategoryTheory.Bicategory.Functor
import Mathlib.CategoryTheory.Bicategory.Strict
import Mathlib.CategoryTheory.Bicategory.LocallyDiscrete
import Mathlib.CategoryTheory.EqToHom

namespace CategoryTheory

open Category Bicategory

universe w₂ v₂ u₂ w₁ v₁ u₁ v u

section

variable {C : Type u} [Category.{v} C]

lemma eqToHom_conj_iff {a b c d : C} (f : a ⟶ b) (g : c ⟶ d) (hac : a = c) (hdb : d = b) :
    f = eqToHom hac ≫ g ≫ eqToHom hdb ↔ eqToHom hac.symm ≫ f ≫ eqToHom hdb.symm = g := by
  subst hac hdb; simp only [eqToHom_refl, comp_id, id_comp]

end

namespace Pseudofunctor

variable {B : Type u₁} [Bicategory.{w₁, v₁} B] {C : Type u₂} [Bicategory.{w₂, v₂} C]
variable (F : OplaxFunctor B C)

@[simp]
lemma map₂_eqToHom {a b : B} {f g : a ⟶ b} (h : f = g) :
    F.map₂ (eqToHom h) = eqToHom (F.congr_map h) := by
  subst h; simp only [eqToHom_refl, OplaxFunctor.map₂_id]

end Pseudofunctor

open CategoryTheory Bicategory


variable {B : Type u₂} [Bicategory.{w₂, v₂} B] [Strict B]
variable {C : Type u₁} [Bicategory.{w₁, v₁} C] [Strict C]

section

variable (F : OplaxFunctor B C)

lemma map₂_leftUnitor_strict {a b : B} (f : a ⟶ b) : (F.mapComp (𝟙 a)) f ≫ F.mapId a ▷ F.map f =
    eqToHom (by simp only [id_comp]) := by
  have h : eqToHom _ = (F.mapComp (𝟙 a) f ≫ F.mapId a ▷ F.map f) ≫ eqToHom _ := by
    simpa using OplaxFunctor.map₂_leftUnitor F f
  rw [← comp_eqToHom_iff (id_comp _).symm, eqToHom_trans] at h
  exact h.symm

lemma map₂_rightUnitor_strict {a b : B} (f : a ⟶ b) : (F.mapComp f) (𝟙 b) ≫ F.map f ◁ F.mapId b =
    eqToHom (by simp) := by
  have h : eqToHom _ = ((F.mapComp f) (𝟙 b) ≫ F.map f ◁ F.mapId b) ≫ eqToHom _ := by
    simpa using OplaxFunctor.map₂_rightUnitor F f
  rw [← comp_eqToHom_iff (comp_id _).symm, eqToHom_trans] at h
  exact h.symm

lemma map₂_associator_strict {a b c d : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
    F.mapComp f (g ≫ h) ≫ F.map f ◁ F.mapComp g h = eqToHom (by simp) ≫
    (F.mapComp (f ≫ g) h ≫ (F.mapComp f g) ▷ F.map h) ≫ eqToHom (by simp) := by
  have h' := by simpa using F.map₂_associator f g h
  rw [eqToHom_comp_iff] at h'
  conv_rhs => congr; rfl; rw [assoc]
  exact h'

lemma map₂_associator_strict' {a b c d : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
    F.mapComp (f ≫ g) h ≫ (F.mapComp f g) ▷ F.map h = eqToHom (by simp) ≫
    (F.mapComp f (g ≫ h) ≫ F.map f ◁ F.mapComp g h) ≫ eqToHom (by simp) := by
  rw [eqToHom_conj_iff]
  apply (map₂_associator_strict F f g h).symm

end


namespace Pseudofunctor

variable (F : Pseudofunctor B C)

lemma mapComp_id_left_strict {a b : B} (f : a ⟶ b) : (F.mapComp (𝟙 a) f).hom =
    eqToHom (by simp) ≫ (F.mapId a).inv ▷ F.map f := by
  rw [← whiskerRightIso_inv, Iso.eq_comp_inv]
  apply map₂_leftUnitor_strict F.toOplax

lemma mapComp_id_left_strict' {a b : B} (f : a ⟶ b) :
    (F.mapId a).hom ▷ F.map f = ((F.mapComp (𝟙 a)) f).inv ≫ eqToHom (by simp) := by
  rw [Iso.eq_inv_comp, mapComp_id_left_strict]
  simp

lemma mapComp_id_right_strict {a b : B} (f : a ⟶ b) : (F.mapComp f (𝟙 b)).hom =
    eqToHom (by simp) ≫ F.map f ◁ (F.mapId b).inv := by
  rw [← whiskerLeftIso_inv, Iso.eq_comp_inv]
  apply map₂_rightUnitor_strict F.toOplax

lemma mapComp_id_right_strict' {a b : B} (f : a ⟶ b) :
    (F.map f) ◁ (F.mapId b).hom = ((F.mapComp f (𝟙 b)).inv) ≫ eqToHom (by simp) := by
  rw [Iso.eq_inv_comp, mapComp_id_right_strict]
  simp

protected lemma map₂_associator_strict {a b c d : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
    (F.mapComp f (g ≫ h)).hom ≫ (F.map f) ◁ (F.mapComp g h).hom
    = eqToHom (by simp) ≫ ((F.mapComp (f ≫ g) h).hom ≫
    (F.mapComp f g).hom ▷ F.map h) ≫ eqToHom (by simp) := by
  apply map₂_associator_strict F.toOplax

protected lemma map₂_associator_strict' {a b c d : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
    (F.mapComp (f ≫ g) h).hom ≫ (F.mapComp f g).hom ▷ F.map h = eqToHom (by simp) ≫
    ((F.mapComp f (g ≫ h)).hom ≫ (F.map f) ◁ (F.mapComp g h).hom) ≫ eqToHom (by simp) := by
  apply map₂_associator_strict' F.toOplax

end Pseudofunctor
