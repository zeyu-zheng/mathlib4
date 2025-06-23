import Mathlib.Tactic.Have
/-
Copyright (c) 2021 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts
import Mathlib.CategoryTheory.Monad.Limits
import Mathlib.CategoryTheory.Adjunction.FullyFaithful
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Adjunction.Reflective
import Mathlib.CategoryTheory.Closed.Cartesian
import Mathlib.CategoryTheory.Subterminal

/-!
# Exponential ideals

An exponential ideal of a cartesian closed category `C` is a subcategory `D ⊆ C` such that for any
`B : D` and `A : C`, the exponential `A ⟹ B` is in `D`: resembling ring theoretic ideals. We
define the notion here for inclusion functors `i : D ⥤ C` rather than explicit subcategories to
preserve the principle of equivalence.

We additionally show that if `C` is cartesian closed and `i : D ⥤ C` is a reflective functor, the
following are equivalent.
* The left adjoint to `i` preserves binary (equivalently, finite) products.
* `i` is an exponential ideal.
-/


universe v₁ v₂ u₁ u₂

noncomputable section

namespace CategoryTheory

open Limits Category

section Ideal

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₁} D] {i : D ⥤ C}
variable (i) [HasFiniteProducts C] [CartesianClosed C]

/-- The subcategory `D` of `C` expressed as an inclusion functor is an *exponential ideal* if
`B ∈ D` implies `A ⟹ B ∈ D` for all `A`.
-/
class ExponentialIdeal : Prop where
  exp_closed : ∀ {B}, B ∈ i.essImage → ∀ A, (A ⟹ B) ∈ i.essImage
attribute [nolint docBlame] ExponentialIdeal.exp_closed

/-- To show `i` is an exponential ideal it suffices to show that `A ⟹ iB` is "in" `D` for any `A` in
`C` and `B` in `D`.
-/
theorem ExponentialIdeal.mk' (h : ∀ (B : D) (A : C), (A ⟹ i.obj B) ∈ i.essImage) :
    ExponentialIdeal i :=
  ⟨fun hB A => by
    rcases hB with ⟨B', ⟨iB'⟩⟩
    exact Functor.essImage.ofIso ((exp A).mapIso iB') (h B' A)⟩

/-- The entire category viewed as a subcategory is an exponential ideal. -/
instance : ExponentialIdeal (𝟭 C) :=
  ExponentialIdeal.mk' _ fun _ _ => ⟨_, ⟨Iso.refl _⟩⟩

open CartesianClosed

/-- The subcategory of subterminal objects is an exponential ideal. -/
instance : ExponentialIdeal (subterminalInclusion C) := by
  apply ExponentialIdeal.mk'
  intro B A
  refine ⟨⟨A ⟹ B.1, fun Z g h => ?_⟩, ⟨Iso.refl _⟩⟩
  exact uncurry_injective (B.2 (CartesianClosed.uncurry g) (CartesianClosed.uncurry h))

/-- If `D` is a reflective subcategory, the property of being an exponential ideal is equivalent to
the presence of a natural isomorphism `i ⋙ exp A ⋙ leftAdjoint i ⋙ i ≅ i ⋙ exp A`, that is:
`(A ⟹ iB) ≅ i L (A ⟹ iB)`, naturally in `B`.
The converse is given in `ExponentialIdeal.mk_of_iso`.
-/
def exponentialIdealReflective (A : C) [Reflective i] [ExponentialIdeal i] :
    i ⋙ exp A ⋙ reflector i ⋙ i ≅ i ⋙ exp A := by
  symm
  apply NatIso.ofComponents _ _
  · intro X
    haveI := Functor.essImage.unit_isIso (ExponentialIdeal.exp_closed (i.obj_mem_essImage X) A)
    apply asIso ((reflectorAdjunction i).unit.app (A ⟹ i.obj X))
  · simp [asIso]

/-- Given a natural isomorphism `i ⋙ exp A ⋙ leftAdjoint i ⋙ i ≅ i ⋙ exp A`, we can show `i`
is an exponential ideal.
-/
theorem ExponentialIdeal.mk_of_iso [Reflective i]
    (h : ∀ A : C, i ⋙ exp A ⋙ reflector i ⋙ i ≅ i ⋙ exp A) : ExponentialIdeal i := by
  apply ExponentialIdeal.mk'
  intro B A
  exact ⟨_, ⟨(h A).app B⟩⟩

end Ideal

section

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₁} D]
variable (i : D ⥤ C)

-- Porting note: this used to be used as a local instance,
-- now it can instead be used as a have when needed
-- we assume HasFiniteProducts D as a hypothesis below
theorem reflective_products [HasFiniteProducts C] [Reflective i] : HasFiniteProducts D :=
  ⟨fun _ => hasLimitsOfShape_of_reflective i⟩


open CartesianClosed

variable [HasFiniteProducts C] [Reflective i] [CartesianClosed C] [HasFiniteProducts D]

/-- If the reflector preserves binary products, the subcategory is an exponential ideal.
This is the converse of `preservesBinaryProductsOfExponentialIdeal`.
-/
instance (priority := 10) exponentialIdeal_of_preservesBinaryProducts
    [PreservesLimitsOfShape (Discrete WalkingPair) (reflector i)] : ExponentialIdeal i := by
  let ir := reflectorAdjunction i
  let L : C ⥤ D := reflector i
  let η : 𝟭 C ⟶ L ⋙ i := ir.unit
  let ε : i ⋙ L ⟶ 𝟭 D := ir.counit
  apply ExponentialIdeal.mk'
  intro B A
  let q : i.obj (L.obj (A ⟹ i.obj B)) ⟶ A ⟹ i.obj B := by
    apply CartesianClosed.curry (ir.homEquiv _ _ _)
    apply _ ≫ (ir.homEquiv _ _).symm ((exp.ev A).app (i.obj B))
    exact prodComparison L A _ ≫ Limits.prod.map (𝟙 _) (ε.app _) ≫ inv (prodComparison _ _ _)
  have : η.app (A ⟹ i.obj B) ≫ q = 𝟙 (A ⟹ i.obj B)
  dsimp
  rw [← curry_natural_left, curry_eq_iff, uncurry_id_eq_ev, ← ir.homEquiv_naturality_left,
    ir.homEquiv_apply_eq, assoc, assoc, prodComparison_natural_assoc, L.map_id,
    ← prod.map_id_comp_assoc, ir.left_triangle_components, prod.map_id_id, id_comp]
  apply IsIso.hom_inv_id_assoc
  haveI : IsSplitMono (η.app (A ⟹ i.obj B)) := IsSplitMono.mk' ⟨_, this⟩
  apply mem_essImage_of_unit_isSplitMono

variable [ExponentialIdeal i]

/-- If `i` witnesses that `D` is a reflective subcategory and an exponential ideal, then `D` is
itself cartesian closed.
-/
def cartesianClosedOfReflective : CartesianClosed D :=
  { __ := monoidalOfHasFiniteProducts D -- Porting note (#10754): added this instance
    closed := fun B =>
      { rightAdj := i ⋙ exp (i.obj B) ⋙ reflector i
        adj := by
          apply (exp.adjunction (i.obj B)).restrictFullyFaithful i.fullyFaithfulOfReflective
            i.fullyFaithfulOfReflective
          · symm
            refine NatIso.ofComponents (fun X => ?_) (fun f => ?_)
            · haveI :=
                Adjunction.rightAdjointPreservesLimits.{0, 0} (reflectorAdjunction i)
              apply asIso (prodComparison i B X)
            · dsimp [asIso]
              rw [prodComparison_natural, Functor.map_id]
          · apply (exponentialIdealReflective i _).symm } }

-- It's annoying that I need to do this.
attribute [-instance] CategoryTheory.preservesLimitOfCreatesLimitAndHasLimit
  CategoryTheory.preservesLimitOfShapeOfCreatesLimitsOfShapeAndHasLimitsOfShape

/-- We construct a bijection between morphisms `L(A ⨯ B) ⟶ X` and morphisms `LA ⨯ LB ⟶ X`.
This bijection has two key properties:
* It is natural in `X`: See `bijection_natural`.
* When `X = LA ⨯ LB`, then the backwards direction sends the identity morphism to the product
  comparison morphism: See `bijection_symm_apply_id`.

Together these help show that `L` preserves binary products. This should be considered
*internal implementation* towards `preservesBinaryProductsOfExponentialIdeal`.
-/
noncomputable def bijection (A B : C) (X : D) :
    ((reflector i).obj (A ⨯ B) ⟶ X) ≃ ((reflector i).obj A ⨯ (reflector i).obj B ⟶ X) :=
  calc
    _ ≃ (A ⨯ B ⟶ i.obj X) := (reflectorAdjunction i).homEquiv _ _
    _ ≃ (B ⨯ A ⟶ i.obj X) := (Limits.prod.braiding _ _).homCongr (Iso.refl _)
    _ ≃ (A ⟶ B ⟹ i.obj X) := (exp.adjunction _).homEquiv _ _
    _ ≃ (i.obj ((reflector i).obj A) ⟶ B ⟹ i.obj X) :=
      (unitCompPartialBijective _ (ExponentialIdeal.exp_closed (i.obj_mem_essImage _) _))
    _ ≃ (B ⨯ i.obj ((reflector i).obj A) ⟶ i.obj X) := ((exp.adjunction _).homEquiv _ _).symm
    _ ≃ (i.obj ((reflector i).obj A) ⨯ B ⟶ i.obj X) :=
      ((Limits.prod.braiding _ _).homCongr (Iso.refl _))
    _ ≃ (B ⟶ i.obj ((reflector i).obj A) ⟹ i.obj X) := (exp.adjunction _).homEquiv _ _
    _ ≃ (i.obj ((reflector i).obj B) ⟶ i.obj ((reflector i).obj A) ⟹ i.obj X) :=
      (unitCompPartialBijective _ (ExponentialIdeal.exp_closed (i.obj_mem_essImage _) _))
    _ ≃ (i.obj ((reflector i).obj A) ⨯ i.obj ((reflector i).obj B) ⟶ i.obj X) :=
      ((exp.adjunction _).homEquiv _ _).symm
    _ ≃ (i.obj ((reflector i).obj A ⨯ (reflector i).obj B) ⟶ i.obj X) :=
      haveI : PreservesLimits i := (reflectorAdjunction i).rightAdjointPreservesLimits
      haveI := preservesSmallestLimitsOfPreservesLimits i
      Iso.homCongr (PreservesLimitPair.iso _ _ _).symm (Iso.refl (i.obj X))
    _ ≃ ((reflector i).obj A ⨯ (reflector i).obj B ⟶ X) :=
      i.fullyFaithfulOfReflective.homEquiv.symm

theorem bijection_symm_apply_id (A B : C) :
    (bijection i A B _).symm (𝟙 _) = prodComparison _ _ _ := by
  dsimp [bijection]
  -- Porting note: added
  erw [homEquiv_symm_apply_eq, homEquiv_symm_apply_eq, homEquiv_apply_eq, homEquiv_apply_eq]
  rw [comp_id, comp_id, comp_id, i.map_id, comp_id, unitCompPartialBijective_symm_apply,
    unitCompPartialBijective_symm_apply, uncurry_natural_left, uncurry_curry,
    uncurry_natural_left, uncurry_curry, prod.lift_map_assoc, comp_id, prod.lift_map_assoc, comp_id]
  -- Porting note: added
  dsimp only [Functor.comp_obj]
  rw [prod.comp_lift_assoc, prod.lift_snd, prod.lift_fst_assoc, prod.lift_fst_comp_snd_comp,
    ← Adjunction.eq_homEquiv_apply, Adjunction.homEquiv_unit, Iso.comp_inv_eq, assoc]
  rw [PreservesLimitPair.iso_hom i ((reflector i).obj A) ((reflector i).obj B)]
  apply prod.hom_ext
  rw [Limits.prod.map_fst, assoc, assoc, prodComparison_fst, ← i.map_comp, prodComparison_fst]
  apply (reflectorAdjunction i).unit.naturality
  rw [Limits.prod.map_snd, assoc, assoc, prodComparison_snd, ← i.map_comp, prodComparison_snd]
  apply (reflectorAdjunction i).unit.naturality

theorem bijection_natural (A B : C) (X X' : D) (f : (reflector i).obj (A ⨯ B) ⟶ X) (g : X ⟶ X') :
    bijection i _ _ _ (f ≫ g) = bijection i _ _ _ f ≫ g := by
  dsimp [bijection]
  -- Porting note: added
  erw [homEquiv_symm_apply_eq, homEquiv_symm_apply_eq, homEquiv_apply_eq, homEquiv_apply_eq,
    homEquiv_symm_apply_eq, homEquiv_symm_apply_eq, homEquiv_apply_eq, homEquiv_apply_eq]
  apply i.map_injective
  rw [Functor.FullyFaithful.map_preimage, i.map_comp, Functor.FullyFaithful.map_preimage,
    comp_id, comp_id, comp_id, comp_id, comp_id,
    comp_id, Adjunction.homEquiv_naturality_right, ← assoc, curry_natural_right _ (i.map g),
    unitCompPartialBijective_natural, uncurry_natural_right, ← assoc, curry_natural_right,
    unitCompPartialBijective_natural, uncurry_natural_right, assoc]

/--
The bijection allows us to show that `prodComparison L A B` is an isomorphism, where the inverse
is the forward map of the identity morphism.
-/
theorem prodComparison_iso (A B : C) : IsIso (prodComparison (reflector i) A B) :=
  ⟨⟨bijection i _ _ _ (𝟙 _), by
      rw [← (bijection i _ _ _).injective.eq_iff, bijection_natural, ← bijection_symm_apply_id,
        Equiv.apply_symm_apply, id_comp],
      by rw [← bijection_natural, id_comp, ← bijection_symm_apply_id, Equiv.apply_symm_apply]⟩⟩

attribute [local instance] prodComparison_iso

/--
If a reflective subcategory is an exponential ideal, then the reflector preserves binary products.
This is the converse of `exponentialIdeal_of_preserves_binary_products`.
-/
noncomputable def preservesBinaryProductsOfExponentialIdeal :
    PreservesLimitsOfShape (Discrete WalkingPair) (reflector i) where
  preservesLimit {K} :=
    letI := PreservesLimitPair.ofIsoProdComparison
      (reflector i) (K.obj ⟨WalkingPair.left⟩) (K.obj ⟨WalkingPair.right⟩)
    Limits.preservesLimitOfIsoDiagram _ (diagramIsoPair K).symm

/--
If a reflective subcategory is an exponential ideal, then the reflector preserves finite products.
-/
noncomputable def preservesFiniteProductsOfExponentialIdeal (J : Type) [Fintype J] :
    PreservesLimitsOfShape (Discrete J) (reflector i) := by
  letI := preservesBinaryProductsOfExponentialIdeal i
  letI : PreservesLimitsOfShape _ (reflector i) := leftAdjointPreservesTerminalOfReflective.{0} i
  apply preservesFiniteProductsOfPreservesBinaryAndTerminal (reflector i) J

end

end CategoryTheory
