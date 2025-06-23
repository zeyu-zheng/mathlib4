import Mathlib.Tactic.Have
/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Mathlib.CategoryTheory.Comma.Basic

/-!
# The category of arrows

The category of arrows, with morphisms commutative squares.
We set this up as a specialization of the comma category `Comma L R`,
where `L` and `R` are both the identity functor.

## Tags

comma, arrow
-/


namespace CategoryTheory

universe v u

-- morphism levels before object levels. See note [CategoryTheory universes].
variable {T : Type u} [Category.{v} T]

section

variable (T)

/-- The arrow category of `T` has as objects all morphisms in `T` and as morphisms commutative
     squares in `T`. -/
def Arrow :=
  Comma.{v, v, v} (𝟭 T) (𝟭 T)

/- Porting note: could not derive `Category` above so this instance works in its place-/
instance : Category (Arrow T) := commaCategory

-- Satisfying the inhabited linter
instance Arrow.inhabited [Inhabited T] : Inhabited (Arrow T) where
  default := show Comma (𝟭 T) (𝟭 T) from default

end

namespace Arrow

@[ext]
lemma hom_ext {X Y : Arrow T} (f g : X ⟶ Y) (h₁ : f.left = g.left) (h₂ : f.right = g.right) :
    f = g :=
  CommaMorphism.ext _ _ h₁ h₂

@[simp]
theorem id_left (f : Arrow T) : CommaMorphism.left (𝟙 f) = 𝟙 f.left :=
  rfl

@[simp]
theorem id_right (f : Arrow T) : CommaMorphism.right (𝟙 f) = 𝟙 f.right :=
  rfl

-- Porting note (#10688): added to ease automation
@[simp, reassoc]
theorem comp_left {X Y Z : Arrow T} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).left = f.left ≫ g.left := rfl

-- Porting note (#10688): added to ease automation
@[simp, reassoc]
theorem comp_right {X Y Z : Arrow T} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).right = f.right ≫ g.right := rfl

/-- An object in the arrow category is simply a morphism in `T`. -/
@[simps]
def mk {X Y : T} (f : X ⟶ Y) : Arrow T where
  left := X
  right := Y
  hom := f

@[simp]
theorem mk_eq (f : Arrow T) : Arrow.mk f.hom = f := by
  cases f
  rfl

theorem mk_injective (A B : T) :
    Function.Injective (Arrow.mk : (A ⟶ B) → Arrow T) := fun f g h => by
  cases h
  rfl

theorem mk_inj (A B : T) {f g : A ⟶ B} : Arrow.mk f = Arrow.mk g ↔ f = g :=
  (mk_injective A B).eq_iff

/- Porting note: was marked as dangerous instance so changed from `Coe` to `CoeOut` -/
instance {X Y : T} : CoeOut (X ⟶ Y) (Arrow T) where
  coe := mk

/-- A morphism in the arrow category is a commutative square connecting two objects of the arrow
    category. -/
@[simps]
def homMk {f g : Arrow T} {u : f.left ⟶ g.left} {v : f.right ⟶ g.right}
    (w : u ≫ g.hom = f.hom ≫ v) : f ⟶ g where
  left := u
  right := v
  w := w

/-- We can also build a morphism in the arrow category out of any commutative square in `T`. -/
@[simps]
def homMk' {X Y : T} {f : X ⟶ Y} {P Q : T} {g : P ⟶ Q} {u : X ⟶ P} {v : Y ⟶ Q} (w : u ≫ g = f ≫ v) :
    Arrow.mk f ⟶ Arrow.mk g where
  left := u
  right := v
  w := w

/- Porting note: was warned simp could prove reassoc'd version. Found simp could not.
Added nolint. -/
@[reassoc (attr := simp, nolint simpNF)]
theorem w {f g : Arrow T} (sq : f ⟶ g) : sq.left ≫ g.hom = f.hom ≫ sq.right :=
  sq.w

-- `w_mk_left` is not needed, as it is a consequence of `w` and `mk_hom`.
@[reassoc (attr := simp)]
theorem w_mk_right {f : Arrow T} {X Y : T} {g : X ⟶ Y} (sq : f ⟶ mk g) :
    sq.left ≫ g = f.hom ≫ sq.right :=
  sq.w

theorem isIso_of_isIso_left_of_isIso_right {f g : Arrow T} (ff : f ⟶ g) [IsIso ff.left]
    [IsIso ff.right] : IsIso ff where
  out := by
    let inverse : g ⟶ f := ⟨inv ff.left, inv ff.right, (by simp)⟩
    apply Exists.intro inverse
    aesop_cat

/-- Create an isomorphism between arrows,
by providing isomorphisms between the domains and codomains,
and a proof that the square commutes. -/
@[simps!]
def isoMk {f g : Arrow T} (l : f.left ≅ g.left) (r : f.right ≅ g.right)
    (h : l.hom ≫ g.hom = f.hom ≫ r.hom := by aesop_cat) : f ≅ g :=
  Comma.isoMk l r h

/-- A variant of `Arrow.isoMk` that creates an iso between two `Arrow.mk`s with a better type
signature. -/
abbrev isoMk' {W X Y Z : T} (f : W ⟶ X) (g : Y ⟶ Z) (e₁ : W ≅ Y) (e₂ : X ≅ Z)
    (h : e₁.hom ≫ g = f ≫ e₂.hom := by aesop_cat) : Arrow.mk f ≅ Arrow.mk g :=
  Arrow.isoMk e₁ e₂ h

theorem hom.congr_left {f g : Arrow T} {φ₁ φ₂ : f ⟶ g} (h : φ₁ = φ₂) : φ₁.left = φ₂.left := by
  rw [h]

@[simp]
theorem hom.congr_right {f g : Arrow T} {φ₁ φ₂ : f ⟶ g} (h : φ₁ = φ₂) : φ₁.right = φ₂.right := by
  rw [h]

theorem iso_w {f g : Arrow T} (e : f ≅ g) : g.hom = e.inv.left ≫ f.hom ≫ e.hom.right := by
  have eq := Arrow.hom.congr_right e.inv_hom_id
  rw [Arrow.comp_right, Arrow.id_right] at eq
  erw [Arrow.w_assoc, eq, Category.comp_id]

theorem iso_w' {W X Y Z : T} {f : W ⟶ X} {g : Y ⟶ Z} (e : Arrow.mk f ≅ Arrow.mk g) :
    g = e.inv.left ≫ f ≫ e.hom.right :=
  iso_w e

section

variable {f g : Arrow T} (sq : f ⟶ g)

instance isIso_left [IsIso sq] : IsIso sq.left where
  out := by
    apply Exists.intro (inv sq).left
    simp only [← Comma.comp_left, IsIso.hom_inv_id, IsIso.inv_hom_id, Arrow.id_left,
      eq_self_iff_true, and_self_iff]
    simp

instance isIso_right [IsIso sq] : IsIso sq.right where
  out := by
    apply Exists.intro (inv sq).right
    simp only [← Comma.comp_right, IsIso.hom_inv_id, IsIso.inv_hom_id, Arrow.id_right,
      eq_self_iff_true, and_self_iff]
    simp

@[simp]
theorem inv_left [IsIso sq] : (inv sq).left = inv sq.left :=
  IsIso.eq_inv_of_hom_inv_id <| by rw [← Comma.comp_left, IsIso.hom_inv_id, id_left]

@[simp]
theorem inv_right [IsIso sq] : (inv sq).right = inv sq.right :=
  IsIso.eq_inv_of_hom_inv_id <| by rw [← Comma.comp_right, IsIso.hom_inv_id, id_right]

/- Porting note (#10618): simp can prove this so removed @[simp] -/
theorem left_hom_inv_right [IsIso sq] : sq.left ≫ g.hom ≫ inv sq.right = f.hom := by
  simp only [← Category.assoc, IsIso.comp_inv_eq, w]

-- simp proves this
theorem inv_left_hom_right [IsIso sq] : inv sq.left ≫ f.hom ≫ sq.right = g.hom := by
  simp only [w, IsIso.inv_comp_eq]

instance mono_left [Mono sq] : Mono sq.left where
  right_cancellation {Z} φ ψ h := by
    let aux : (Z ⟶ f.left) → (Arrow.mk (𝟙 Z) ⟶ f) := fun φ =>
      { left := φ
        right := φ ≫ f.hom }
    have : ∀ g, (aux g).right = g ≫ f.hom := fun g => by dsimp
    show (aux φ).left = (aux ψ).left
    congr 1
    rw [← cancel_mono sq]
    apply CommaMorphism.ext
    exact h
    rw [Comma.comp_right, Comma.comp_right, this, this, Category.assoc, Category.assoc]
    rw [← Arrow.w]
    simp only [← Category.assoc, h]

instance epi_right [Epi sq] : Epi sq.right where
  left_cancellation {Z} φ ψ h := by
    let aux : (g.right ⟶ Z) → (g ⟶ Arrow.mk (𝟙 Z)) := fun φ =>
      { right := φ
        left := g.hom ≫ φ }
    show (aux φ).right = (aux ψ).right
    congr 1
    rw [← cancel_epi sq]
    apply CommaMorphism.ext
    rw [Comma.comp_left, Comma.comp_left, Arrow.w_assoc, Arrow.w_assoc, h]
    exact h

@[reassoc (attr := simp)]
lemma hom_inv_id_left (e : f ≅ g) : e.hom.left ≫ e.inv.left = 𝟙 _ := by
  rw [← comp_left, e.hom_inv_id, id_left]

@[reassoc (attr := simp)]
lemma inv_hom_id_left (e : f ≅ g) : e.inv.left ≫ e.hom.left = 𝟙 _ := by
  rw [← comp_left, e.inv_hom_id, id_left]

@[reassoc (attr := simp)]
lemma hom_inv_id_right (e : f ≅ g) : e.hom.right ≫ e.inv.right = 𝟙 _ := by
  rw [← comp_right, e.hom_inv_id, id_right]

@[reassoc (attr := simp)]
lemma inv_hom_id_right (e : f ≅ g) : e.inv.right ≫ e.hom.right = 𝟙 _ := by
  rw [← comp_right, e.inv_hom_id, id_right]

end

/-- Given a square from an arrow `i` to an isomorphism `p`, express the source part of `sq`
in terms of the inverse of `p`. -/
@[simp]
theorem square_to_iso_invert (i : Arrow T) {X Y : T} (p : X ≅ Y) (sq : i ⟶ Arrow.mk p.hom) :
    i.hom ≫ sq.right ≫ p.inv = sq.left := by
  simpa only [Category.assoc] using (Iso.comp_inv_eq p).mpr (Arrow.w_mk_right sq).symm

/-- Given a square from an isomorphism `i` to an arrow `p`, express the target part of `sq`
in terms of the inverse of `i`. -/
theorem square_from_iso_invert {X Y : T} (i : X ≅ Y) (p : Arrow T) (sq : Arrow.mk i.hom ⟶ p) :
    i.inv ≫ sq.left ≫ p.hom = sq.right := by simp only [Iso.inv_hom_id_assoc, Arrow.w, Arrow.mk_hom]

variable {C : Type u} [Category.{v} C]

/-- A helper construction: given a square between `i` and `f ≫ g`, produce a square between
`i` and `g`, whose top leg uses `f`:
A  → X
     ↓f
↓i   Y             --> A → Y
     ↓g                ↓i  ↓g
B  → Z                 B → Z
 -/
@[simps]
def squareToSnd {X Y Z : C} {i : Arrow C} {f : X ⟶ Y} {g : Y ⟶ Z} (sq : i ⟶ Arrow.mk (f ≫ g)) :
    i ⟶ Arrow.mk g where
  left := sq.left ≫ f
  right := sq.right

/-- The functor sending an arrow to its source. -/
@[simps!]
def leftFunc : Arrow C ⥤ C :=
  Comma.fst _ _

/-- The functor sending an arrow to its target. -/
@[simps!]
def rightFunc : Arrow C ⥤ C :=
  Comma.snd _ _

/-- The natural transformation from `leftFunc` to `rightFunc`, given by the arrow itself. -/
@[simps]
def leftToRight : (leftFunc : Arrow C ⥤ C) ⟶ rightFunc where app f := f.hom

end Arrow

namespace Functor

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

/-- A functor `C ⥤ D` induces a functor between the corresponding arrow categories. -/
@[simps]
def mapArrow (F : C ⥤ D) : Arrow C ⥤ Arrow D where
  obj a :=
    { left := F.obj a.left
      right := F.obj a.right
      hom := F.map a.hom }
  map f :=
    { left := F.map f.left
      right := F.map f.right
      w := by
        let w := f.w
        simp only [id_map] at w
        dsimp
        simp only [← F.map_comp, w] }

variable (C D)

/-- The functor `(C ⥤ D) ⥤ (Arrow C ⥤ Arrow D)` which sends
a functor `F : C ⥤ D` to `F.mapArrow`. -/
@[simps]
def mapArrowFunctor : (C ⥤ D) ⥤ (Arrow C ⥤ Arrow D) where
  obj F := F.mapArrow
  map τ :=
    { app := fun f =>
        { left := τ.app _
          right := τ.app _ } }

variable {C D}

/-- The equivalence of categories `Arrow C ≌ Arrow D` induced by an equivalence `C ≌ D`. -/
def mapArrowEquivalence (e : C ≌ D) : Arrow C ≌ Arrow D where
  functor := e.functor.mapArrow
  inverse := e.inverse.mapArrow
  unitIso := Functor.mapIso (mapArrowFunctor C C) e.unitIso
  counitIso := Functor.mapIso (mapArrowFunctor D D) e.counitIso

instance isEquivalence_mapArrow (F : C ⥤ D) [IsEquivalence F] :
    IsEquivalence F.mapArrow :=
  (mapArrowEquivalence (asEquivalence F)).isEquivalence_functor

end Functor

/-- The images of `f : Arrow C` by two isomorphic functors `F : C ⥤ D` are
isomorphic arrows in `D`. -/
def Arrow.isoOfNatIso {C D : Type*} [Category C] [Category D] {F G : C ⥤ D} (e : F ≅ G)
    (f : Arrow C) : F.mapArrow.obj f ≅ G.mapArrow.obj f :=
  Arrow.isoMk (e.app f.left) (e.app f.right)

end CategoryTheory
