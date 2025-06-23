import Mathlib.Tactic.Have
/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.ChosenFiniteProducts
import Mathlib.CategoryTheory.Limits.FunctorCategory

/-!
# Functor categories have chosen finite products

If `C` is a category with chosen finite products, then so is `J ⥤ C`.

-/

namespace CategoryTheory

open Limits MonoidalCategory Category

variable (J C : Type*) [Category J] [Category C] [ChosenFiniteProducts C]

namespace Functor

/-- The chosen terminal object in `J ⥤ C`. -/
abbrev chosenTerminal : J ⥤ C := (Functor.const J).obj (𝟙_ C)

/-- The chosen terminal object in `J ⥤ C` is terminal. -/
def chosenTerminalIsTerminal : IsTerminal (chosenTerminal J C) :=
  evaluationJointlyReflectsLimits _
    (fun _ => isLimitChangeEmptyCone _ ChosenFiniteProducts.terminal.2 _ (Iso.refl _))

section

variable {J C}
variable (F₁ F₂ : J ⥤ C)

/-- The chosen binary product on `J ⥤ C`. -/
@[simps]
def chosenProd : J ⥤ C where
  obj j := F₁.obj j ⊗ F₂.obj j
  map φ := F₁.map φ ⊗ F₂.map φ

namespace chosenProd

/-- The first projection `chosenProd F₁ F₂ ⟶ F₁`. -/
@[simps]
def fst : chosenProd F₁ F₂ ⟶ F₁ where
  app _ := ChosenFiniteProducts.fst _ _

/-- The second projection `chosenProd F₁ F₂ ⟶ F₂`. -/
@[simps]
def snd : chosenProd F₁ F₂ ⟶ F₂ where
  app j := ChosenFiniteProducts.snd _ _

/-- `Functor.chosenProd F₁ F₂` is a binary product of `F₁` and `F₂`. -/
noncomputable def isLimit : IsLimit (BinaryFan.mk (fst F₁ F₂) (snd F₁ F₂)) :=
  evaluationJointlyReflectsLimits _ (fun j =>
    (IsLimit.postcomposeHomEquiv (mapPairIso (by exact Iso.refl _) (by exact Iso.refl _)) _).1
      (IsLimit.ofIsoLimit (ChosenFiniteProducts.product (X := F₁.obj j) (Y := F₂.obj j)).2
        (Cones.ext (Iso.refl _) (by rintro ⟨_|_⟩; all_goals aesop_cat))))

end chosenProd

end

noncomputable instance chosenFiniteProducts :
    ChosenFiniteProducts (J ⥤ C) where
  terminal := ⟨_, chosenTerminalIsTerminal J C⟩
  product F₁ F₂ := ⟨_, chosenProd.isLimit F₁ F₂⟩

namespace Monoidal

open ChosenFiniteProducts

variable {J C}

@[simp]
lemma leftUnitor_hom_app (F : J ⥤ C) (j : J) :
    (λ_ F).hom.app j = (λ_ (F.obj j)).hom := rfl

@[simp]
lemma leftUnitor_inv_app (F : J ⥤ C) (j : J) :
    (λ_ F).inv.app j = (λ_ (F.obj j)).inv := by
  rw [← cancel_mono ((λ_ (F.obj j)).hom), Iso.inv_hom_id, ← leftUnitor_hom_app,
    Iso.inv_hom_id_app]

@[simp]
lemma rightUnitor_hom_app (F : J ⥤ C) (j : J) :
    (ρ_ F).hom.app j = (ρ_ (F.obj j)).hom := rfl

@[simp]
lemma rightUnitor_inv_app (F : J ⥤ C) (j : J) :
    (ρ_ F).inv.app j = (ρ_ (F.obj j)).inv := by
  rw [← cancel_mono ((ρ_ (F.obj j)).hom), Iso.inv_hom_id, ← rightUnitor_hom_app,
    Iso.inv_hom_id_app]

@[reassoc (attr := simp)]
lemma tensorHom_app_fst {F₁ F₁' F₂ F₂' : J ⥤ C} (f : F₁ ⟶ F₁') (g : F₂ ⟶ F₂') (j : J) :
    (f ⊗ g).app j ≫ fst _ _ = fst _ _ ≫ f.app j := by
  change (f ⊗ g).app j ≫ (fst F₁' F₂').app j = _
  rw [← NatTrans.comp_app, tensorHom_fst, NatTrans.comp_app]
  rfl

@[reassoc (attr := simp)]
lemma tensorHom_app_snd {F₁ F₁' F₂ F₂' : J ⥤ C} (f : F₁ ⟶ F₁') (g : F₂ ⟶ F₂') (j : J) :
    (f ⊗ g).app j ≫ snd _ _ = snd _ _ ≫ g.app j := by
  change (f ⊗ g).app j ≫ (snd F₁' F₂').app j = _
  rw [← NatTrans.comp_app, tensorHom_snd, NatTrans.comp_app]
  rfl

@[reassoc (attr := simp)]
lemma whiskerLeft_app_fst (F₁ : J ⥤ C) {F₂ F₂' : J ⥤ C} (g : F₂ ⟶ F₂') (j : J) :
    (F₁ ◁ g).app j ≫ fst _ _ = fst _ _ :=
  (tensorHom_app_fst (𝟙 F₁) g j).trans (by simp)

@[reassoc (attr := simp)]
lemma whiskerLeft_app_snd (F₁ : J ⥤ C) {F₂ F₂' : J ⥤ C} (g : F₂ ⟶ F₂') (j : J) :
    (F₁ ◁ g).app j ≫ snd _ _ = snd _ _ ≫ g.app j :=
  (tensorHom_app_snd (𝟙 F₁) g j)

@[reassoc (attr := simp)]
lemma whiskerRight_app_fst {F₁ F₁' : J ⥤ C} (f : F₁ ⟶ F₁') (F₂ : J ⥤ C) (j : J) :
    (f ▷ F₂).app j ≫ fst _ _ = fst _ _ ≫ f.app j :=
  (tensorHom_app_fst f (𝟙 F₂) j)

@[reassoc (attr := simp)]
lemma whiskerRight_app_snd {F₁ F₁' : J ⥤ C} (f : F₁ ⟶ F₁') (F₂ : J ⥤ C) (j : J) :
    (f ▷ F₂).app j ≫ snd _ _ = snd _ _ :=
  (tensorHom_app_snd f (𝟙 F₂) j).trans (by simp)

@[simp]
lemma associator_hom_app (F₁ F₂ F₃ : J ⥤ C) (j : J) :
    (α_ F₁ F₂ F₃).hom.app j = (α_ _ _ _).hom := by
  apply hom_ext
  change _ ≫ (fst F₁ (F₂ ⊗ F₃)).app j = _
  rw [← NatTrans.comp_app, associator_hom_fst]
  erw [associator_hom_fst]
  rfl
  apply hom_ext
  change (_ ≫ (snd F₁ (F₂ ⊗ F₃)).app j) ≫ (fst F₂ F₃).app j = _
  rw [← NatTrans.comp_app, ← NatTrans.comp_app, assoc, associator_hom_snd_fst, assoc]
  erw [associator_hom_snd_fst]
  rfl
  change (_ ≫ (snd F₁ (F₂ ⊗ F₃)).app j) ≫ (snd F₂ F₃).app j = _
  rw [← NatTrans.comp_app, ← NatTrans.comp_app, assoc, associator_hom_snd_snd, assoc]
  erw [associator_hom_snd_snd]
  rfl

@[simp]
lemma associator_inv_app (F₁ F₂ F₃ : J ⥤ C) (j : J) :
    (α_ F₁ F₂ F₃).inv.app j = (α_ _ _ _).inv := by
  rw [← cancel_mono ((α_ _ _ _).hom), Iso.inv_hom_id, ← associator_hom_app, Iso.inv_hom_id_app]

end Monoidal

end Functor

end CategoryTheory
