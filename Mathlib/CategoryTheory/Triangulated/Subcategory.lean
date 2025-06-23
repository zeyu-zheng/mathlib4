import Mathlib.Tactic.Have
/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.ClosedUnderIsomorphisms
import Mathlib.CategoryTheory.Localization.CalculusOfFractions
import Mathlib.CategoryTheory.Localization.Triangulated
import Mathlib.CategoryTheory.Shift.Localization

/-! # Triangulated subcategories

In this file, we introduce the notion of triangulated subcategory of
a pretriangulated category `C`. If `S : Subcategory W`, we define the
class of morphisms `S.W : MorphismProperty C` consisting of morphisms
whose "cone" belongs to `S` (up to isomorphisms). We show that `S.W`
has both calculus of left and right fractions.

## TODO

* obtain (pre)triangulated instances on the localized category with respect to `S.W`
* define the type `S.category` as `Fullsubcategory S.set` and show that it
is a pretriangulated category.

## Implementation notes

In the definition of `Triangulated.Subcategory`, we do not assume that the predicate
on objects is closed under isomorphisms (i.e. that the subcategory is "strictly full").
Part of the theory would be more convenient under this stronger assumption
(e.g. `Subcategory C` would be a lattice), but some applications require this:
for example, the subcategory of bounded below complexes in the homotopy category
of an additive category is not closed under isomorphisms.

## References
* [Jean-Louis Verdier, *Des catégories dérivées des catégories abéliennes*][verdier1996]

-/

namespace CategoryTheory

open Category Limits Preadditive ZeroObject

namespace Triangulated

open Pretriangulated

variable (C : Type*) [Category C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]

/-- A triangulated subcategory of a pretriangulated category `C` consists of
a predicate `P : C → Prop` which contains a zero object, is stable by shifts, and such that
if `X₁ ⟶ X₂ ⟶ X₃ ⟶ X₁⟦1⟧` is a distinguished triangle such that if `X₁` and `X₃` satisfy
`P` then `X₂` is isomorphic to an object satisfying `P`. -/
structure Subcategory where
  /-- the underlying predicate on objects of a triangulated subcategory -/
  P : C → Prop
  zero' : ∃ (Z : C) (_ : IsZero Z), P Z
  shift (X : C) (n : ℤ) : P X → P (X⟦n⟧)
  ext₂' (T : Triangle C) (_ : T ∈ distTriang C) : P T.obj₁ → P T.obj₃ → isoClosure P T.obj₂

namespace Subcategory

variable {C}
variable (S : Subcategory C)

lemma zero [ClosedUnderIsomorphisms S.P] : S.P 0 := by
  obtain ⟨X, hX, mem⟩ := S.zero'
  exact mem_of_iso _ hX.isoZero mem

/-- The closure under isomorphisms of a triangulated subcategory. -/
def isoClosure : Subcategory C where
  P := CategoryTheory.isoClosure S.P
  zero' := by
    obtain ⟨Z, hZ, hZ'⟩ := S.zero'
    exact ⟨Z, hZ, Z, hZ', ⟨Iso.refl _⟩⟩
  shift X n := by
    rintro ⟨Y, hY, ⟨e⟩⟩
    exact ⟨Y⟦n⟧, S.shift Y n hY, ⟨(shiftFunctor C n).mapIso e⟩⟩
  ext₂' := by
    rintro T hT ⟨X₁, h₁, ⟨e₁⟩⟩ ⟨X₃, h₃, ⟨e₃⟩⟩
    exact le_isoClosure _ _
      (S.ext₂' (Triangle.mk (e₁.inv ≫ T.mor₁) (T.mor₂ ≫ e₃.hom) (e₃.inv ≫ T.mor₃ ≫ e₁.hom⟦1⟧'))
      (isomorphic_distinguished _ hT _
        (Triangle.isoMk _ _ e₁.symm (Iso.refl _) e₃.symm (by aesop_cat) (by aesop_cat) (by
          dsimp
          simp only [assoc, Iso.cancel_iso_inv_left, ← Functor.map_comp, e₁.hom_inv_id,
            Functor.map_id, comp_id]))) h₁ h₃)

instance : ClosedUnderIsomorphisms S.isoClosure.P := by
  dsimp only [isoClosure]
  infer_instance

section

variable (P : C → Prop) (zero : P 0)
  (shift : ∀ (X : C) (n : ℤ), P X → P (X⟦n⟧))
  (ext₂ : ∀ (T : Triangle C) (_ : T ∈ distTriang C), P T.obj₁ → P T.obj₃ → P T.obj₂)

/-- An alternative constructor for "strictly full" triangulated subcategory. -/
def mk' : Subcategory C where
  P := P
  zero' := ⟨0, isZero_zero _, zero⟩
  shift := shift
  ext₂' T hT h₁ h₃ := le_isoClosure P _ (ext₂ T hT h₁ h₃)

instance : ClosedUnderIsomorphisms (mk' P zero shift ext₂).P where
  of_iso {X Y} e hX := by
    refine ext₂ (Triangle.mk e.hom (0 : Y ⟶ 0) 0) ?_ hX zero
    refine isomorphic_distinguished _ (contractible_distinguished X) _ ?_
    exact Triangle.isoMk _ _ (Iso.refl _) e.symm (Iso.refl _)

end

lemma ext₂ [ClosedUnderIsomorphisms S.P]
    (T : Triangle C) (hT : T ∈ distTriang C) (h₁ : S.P T.obj₁)
    (h₃ : S.P T.obj₃) : S.P T.obj₂ := by
  simpa only [isoClosure_eq_self] using S.ext₂' T hT h₁ h₃

/-- Given `S : Triangulated.Subcategory C`, this is the class of morphisms on `C` which
consists of morphisms whose cone satisfies `S.P`. -/
def W : MorphismProperty C := fun X Y f => ∃ (Z : C) (g : Y ⟶ Z) (h : Z ⟶ X⟦(1 : ℤ)⟧)
  (_ : Triangle.mk f g h ∈ distTriang C), S.P Z

lemma W_iff {X Y : C} (f : X ⟶ Y) :
    S.W f ↔ ∃ (Z : C) (g : Y ⟶ Z) (h : Z ⟶ X⟦(1 : ℤ)⟧)
      (_ : Triangle.mk f g h ∈ distTriang C), S.P Z := by rfl

lemma W_iff' {Y Z : C} (g : Y ⟶ Z) :
    S.W g ↔ ∃ (X : C) (f : X ⟶ Y) (h : Z ⟶ X⟦(1 : ℤ)⟧)
      (_ : Triangle.mk f g h ∈ distTriang C), S.P X := by
  rw [S.W_iff]
  constructor
  rintro ⟨Z, g, h, H, mem⟩
  exact ⟨_, _, _, inv_rot_of_distTriang _ H, S.shift _ (-1) mem⟩
  rintro ⟨Z, g, h, H, mem⟩
  exact ⟨_, _, _, rot_of_distTriang _ H, S.shift _ 1 mem⟩

lemma W.mk {T : Triangle C} (hT : T ∈ distTriang C) (h : S.P T.obj₃) : S.W T.mor₁ :=
  ⟨_, _, _, hT, h⟩

lemma W.mk' {T : Triangle C} (hT : T ∈ distTriang C) (h : S.P T.obj₁) : S.W T.mor₂ := by
  rw [W_iff']
  exact ⟨_, _, _, hT, h⟩

lemma isoClosure_W : S.isoClosure.W = S.W := by
  ext X Y f
  constructor
  rintro ⟨Z, g, h, mem, ⟨Z', hZ', ⟨e⟩⟩⟩
  refine ⟨Z', g ≫ e.hom, e.inv ≫ h, isomorphic_distinguished _ mem _ ?_, hZ'⟩
  exact Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) e.symm
  rintro ⟨Z, g, h, mem, hZ⟩
  exact ⟨Z, g, h, mem, le_isoClosure _ _ hZ⟩

instance respectsIso_W : S.W.RespectsIso where
  precomp := by
    rintro X' X Y e f ⟨Z, g, h, mem, mem'⟩
    refine ⟨Z, g, h ≫ e.inv⟦(1 : ℤ)⟧', isomorphic_distinguished _ mem _ ?_, mem'⟩
    refine Triangle.isoMk _ _ e (Iso.refl _) (Iso.refl _) (by aesop_cat) (by aesop_cat) ?_
    dsimp
    simp only [assoc, ← Functor.map_comp, e.inv_hom_id, Functor.map_id, comp_id, id_comp]
  postcomp := by
    rintro X Y Y' e f ⟨Z, g, h, mem, mem'⟩
    refine ⟨Z, e.inv ≫ g, h, isomorphic_distinguished _ mem _ ?_, mem'⟩
    exact Triangle.isoMk _ _ (Iso.refl _) e.symm (Iso.refl _)

instance : S.W.ContainsIdentities := by
  rw [← isoClosure_W]
  exact ⟨fun X => ⟨_, _, _, contractible_distinguished X, zero _⟩⟩

lemma W_of_isIso {X Y : C} (f : X ⟶ Y) [IsIso f] : S.W f := by
  refine (S.W.arrow_mk_iso_iff ?_).1 (MorphismProperty.id_mem _ X)
  exact Arrow.isoMk (Iso.refl _) (asIso f)

lemma smul_mem_W_iff {X Y : C} (f : X ⟶ Y) (n : ℤˣ) :
    S.W (n • f) ↔ S.W f :=
  S.W.arrow_mk_iso_iff (Arrow.isoMk (n • (Iso.refl _)) (Iso.refl _))

variable {S}

lemma W.shift {X₁ X₂ : C} {f : X₁ ⟶ X₂} (hf : S.W f) (n : ℤ) : S.W (f⟦n⟧') := by
  rw [← smul_mem_W_iff _ _ (n.negOnePow)]
  obtain ⟨X₃, g, h, hT, mem⟩ := hf
  exact ⟨_, _, _, Pretriangulated.Triangle.shift_distinguished _ hT n, S.shift _ _ mem⟩

lemma W.unshift {X₁ X₂ : C} {f : X₁ ⟶ X₂} {n : ℤ} (hf : S.W (f⟦n⟧')) : S.W f :=
  (S.W.arrow_mk_iso_iff
     (Arrow.isoOfNatIso (shiftEquiv C n).unitIso (Arrow.mk f))).2 (hf.shift (-n))

instance : S.W.IsCompatibleWithShift ℤ where
  condition n := by
    ext K L f
    exact ⟨fun hf => hf.unshift, fun hf => hf.shift n⟩

instance [IsTriangulated C] : S.W.IsMultiplicative where
  comp_mem := by
    rw [← isoClosure_W]
    rintro X₁ X₂ X₃ u₁₂ u₂₃ ⟨Z₁₂, v₁₂, w₁₂, H₁₂, mem₁₂⟩ ⟨Z₂₃, v₂₃, w₂₃, H₂₃, mem₂₃⟩
    obtain ⟨Z₁₃, v₁₃, w₁₂, H₁₃⟩ := distinguished_cocone_triangle (u₁₂ ≫ u₂₃)
    exact ⟨_, _, _, H₁₃, S.isoClosure.ext₂ _ (someOctahedron rfl H₁₂ H₂₃ H₁₃).mem mem₁₂ mem₂₃⟩

variable (S)

lemma mem_W_iff_of_distinguished
    [ClosedUnderIsomorphisms S.P] (T : Triangle C) (hT : T ∈ distTriang C) :
    S.W T.mor₁ ↔ S.P T.obj₃ := by
  constructor
  rintro ⟨Z, g, h, hT', mem⟩
  obtain ⟨e, _⟩ := exists_iso_of_arrow_iso _ _ hT' hT (Iso.refl _)
  exact mem_of_iso S.P (Triangle.π₃.mapIso e) mem
  intro h
  exact ⟨_, _, _, hT, h⟩

instance [IsTriangulated C] : S.W.HasLeftCalculusOfFractions where
  exists_leftFraction X Y φ := by
    obtain ⟨Z, f, g, H, mem⟩ := φ.hs
    obtain ⟨Y', s', f', mem'⟩ := distinguished_cocone_triangle₂ (g ≫ φ.f⟦1⟧')
    obtain ⟨b, ⟨hb₁, _⟩⟩ :=
      complete_distinguished_triangle_morphism₂ _ _ H mem' φ.f (𝟙 Z) (by simp)
    exact ⟨MorphismProperty.LeftFraction.mk b s' ⟨_, _, _, mem', mem⟩, hb₁.symm⟩
  ext := by
    rintro X' X Y f₁ f₂ s ⟨Z, g, h, H, mem⟩ hf₁
    have hf₂ : s ≫ (f₁ - f₂) = 0 := by rw [comp_sub, hf₁, sub_self]
    obtain ⟨q, hq⟩ := Triangle.yoneda_exact₂ _ H _ hf₂
    obtain ⟨Y', r, t, mem'⟩ := distinguished_cocone_triangle q
    refine ⟨Y', r, ?_, ?_⟩
    exact ⟨_, _, _, rot_of_distTriang _ mem', S.shift _ _ mem⟩
    have eq := comp_distTriang_mor_zero₁₂ _ mem'
    dsimp at eq
    rw [← sub_eq_zero, ← sub_comp, hq, assoc, eq, comp_zero]

instance [IsTriangulated C] : S.W.HasRightCalculusOfFractions where
  exists_rightFraction X Y φ := by
    obtain ⟨Z, f, g, H, mem⟩ := φ.hs
    obtain ⟨X', f', h', mem'⟩ := distinguished_cocone_triangle₁ (φ.f ≫ f)
    obtain ⟨a, ⟨ha₁, _⟩⟩ := complete_distinguished_triangle_morphism₁ _ _
      mem' H φ.f (𝟙 Z) (by simp)
    exact ⟨MorphismProperty.RightFraction.mk f' ⟨_, _, _, mem', mem⟩ a, ha₁⟩
  ext Y Z Z' f₁ f₂ s hs hf₁ := by
    rw [S.W_iff'] at hs
    obtain ⟨Z, g, h, H, mem⟩ := hs
    have hf₂ : (f₁ - f₂) ≫ s = 0
    rw [sub_comp, hf₁, sub_self]
    obtain ⟨q, hq⟩ := Triangle.coyoneda_exact₂ _ H _ hf₂
    obtain ⟨Y', r, t, mem'⟩ := distinguished_cocone_triangle₁ q
    refine ⟨Y', r, ?_, ?_⟩
    exact ⟨_, _, _, mem', mem⟩
    have eq := comp_distTriang_mor_zero₁₂ _ mem'
    dsimp at eq
    rw [← sub_eq_zero, ← comp_sub, hq, reassoc_of% eq, zero_comp]

instance [IsTriangulated C] : S.W.IsCompatibleWithTriangulation := ⟨by
  rintro T₁ T₃ mem₁ mem₃ a b ⟨Z₅, g₅, h₅, mem₅, mem₅'⟩ ⟨Z₄, g₄, h₄, mem₄, mem₄'⟩ comm
  obtain ⟨Z₂, g₂, h₂, mem₂⟩ := distinguished_cocone_triangle (T₁.mor₁ ≫ b)
  have H := someOctahedron rfl mem₁ mem₄ mem₂
  have H' := someOctahedron comm.symm mem₅ mem₃ mem₂
  let φ : T₁ ⟶ T₃ := H.triangleMorphism₁ ≫ H'.triangleMorphism₂
  exact ⟨φ.hom₃, S.W.comp_mem _ _ (W.mk S H.mem mem₄') (W.mk' S H'.mem mem₅'),
    by simpa [φ] using φ.comm₂, by simpa [φ] using φ.comm₃⟩⟩

section

variable (T : Triangle C) (hT : T ∈ distTriang C)

lemma ext₁ [ClosedUnderIsomorphisms S.P] (h₂ : S.P T.obj₂) (h₃ : S.P T.obj₃) :
    S.P T.obj₁ :=
  S.ext₂ _ (inv_rot_of_distTriang _ hT) (S.shift _ _ h₃) h₂

lemma ext₃ [ClosedUnderIsomorphisms S.P] (h₁ : S.P T.obj₁) (h₂ : S.P T.obj₂) :
    S.P T.obj₃ :=
  S.ext₂ _ (rot_of_distTriang _ hT) h₂ (S.shift _ _ h₁)

lemma ext₁' (h₂ : S.P T.obj₂) (h₃ : S.P T.obj₃) :
    CategoryTheory.isoClosure S.P T.obj₁ :=
  S.ext₂' _ (inv_rot_of_distTriang _ hT) (S.shift _ _ h₃) h₂

lemma ext₃' (h₁ : S.P T.obj₁) (h₂ : S.P T.obj₂) :
    CategoryTheory.isoClosure S.P T.obj₃ :=
  S.ext₂' _ (rot_of_distTriang _ hT) h₂ (S.shift _ _ h₁)

end

end Subcategory

end Triangulated

end CategoryTheory
