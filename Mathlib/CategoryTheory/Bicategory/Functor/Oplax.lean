/-
Copyright (c) 2022 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
import Mathlib.CategoryTheory.Bicategory.Basic

/-!
# Oplax functors

An oplax functor `F` between bicategories `B` and `C` consists of
* a function between objects `F.obj : B ⟶ C`,
* a family of functions between 1-morphisms `F.map : (a ⟶ b) → (F.obj a ⟶ F.obj b)`,
* a family of functions between 2-morphisms `F.map₂ : (f ⟶ g) → (F.map f ⟶ F.map g)`,
* a family of 2-morphisms `F.mapId a : F.map (𝟙 a) ⟶ 𝟙 (F.obj a)`,
* a family of 2-morphisms `F.mapComp f g : F.map (f ≫ g) ⟶ F.map f ≫ F.map g`, and
* certain consistency conditions on them.

## Main definitions

* `CategoryTheory.OplaxFunctor B C` : an oplax functor between bicategories `B` and `C`
* `CategoryTheory.OplaxFunctor.comp F G` : the composition of oplax functors

## Future work

There are two types of functors between bicategories, called lax and oplax functors, depending on
the directions of `mapId` and `mapComp`. We may need both in mathlib in the future, but for
now we only define oplax functors.
-/


namespace CategoryTheory

open Category Bicategory

open Bicategory

universe w₁ w₂ w₃ v₁ v₂ v₃ u₁ u₂ u₃

section

variable {B : Type u₁} [Quiver.{v₁ + 1} B] [∀ a b : B, Quiver.{w₁ + 1} (a ⟶ b)]
variable {C : Type u₂} [Quiver.{v₂ + 1} C] [∀ a b : C, Quiver.{w₂ + 1} (a ⟶ b)]
variable {D : Type u₃} [Quiver.{v₃ + 1} D] [∀ a b : D, Quiver.{w₃ + 1} (a ⟶ b)]

/-- A prelax functor between bicategories consists of functions between objects,
1-morphisms, and 2-morphisms. This structure will be extended to define `OplaxFunctor`.
-/
structure PrelaxFunctor (B : Type u₁) [Quiver.{v₁ + 1} B] [∀ a b : B, Quiver.{w₁ + 1} (a ⟶ b)]
  (C : Type u₂) [Quiver.{v₂ + 1} C] [∀ a b : C, Quiver.{w₂ + 1} (a ⟶ b)] extends
  Prefunctor B C where
  /-- The action of a prelax functor on 2-morphisms. -/
  map₂ {a b : B} {f g : a ⟶ b} : (f ⟶ g) → (map f ⟶ map g)

initialize_simps_projections PrelaxFunctor (+toPrefunctor, -obj, -map)

/-- The prefunctor between the underlying quivers. -/
add_decl_doc PrelaxFunctor.toPrefunctor

namespace PrelaxFunctor

attribute [coe] CategoryTheory.PrelaxFunctor.toPrefunctor

instance hasCoeToPrefunctor : Coe (PrelaxFunctor B C) (Prefunctor B C) :=
  ⟨toPrefunctor⟩

variable (F : PrelaxFunctor B C)

/-- The identity prelax functor. -/
@[simps]
def id (B : Type u₁) [Quiver.{v₁ + 1} B] [∀ a b : B, Quiver.{w₁ + 1} (a ⟶ b)] : PrelaxFunctor B B :=
  { Prefunctor.id B with map₂ := fun η => η }

instance : Inhabited (PrelaxFunctor B B) :=
  ⟨PrelaxFunctor.id B⟩

-- Porting note: `by exact` was not necessary in mathlib3
/-- Composition of prelax functors. -/
@[simps]
def comp (F : PrelaxFunctor B C) (G : PrelaxFunctor C D) : PrelaxFunctor B D :=
  { (F : Prefunctor B C).comp ↑G with map₂ := fun η => by exact G.map₂ (F.map₂ η) }

end PrelaxFunctor

end

section

variable {B : Type u₁} [Bicategory.{w₁, v₁} B] {C : Type u₂} [Bicategory.{w₂, v₂} C]
variable {D : Type u₃} [Bicategory.{w₃, v₃} D]

/-- An oplax functor `F` between bicategories `B` and `C` consists of a function between objects
`F.obj`, a function between 1-morphisms `F.map`, and a function between 2-morphisms `F.map₂`.

Unlike functors between categories, `F.map` do not need to strictly commute with the composition,
and do not need to strictly preserve the identity. Instead, there are specified 2-morphisms
`F.map (𝟙 a) ⟶ 𝟙 (F.obj a)` and `F.map (f ≫ g) ⟶ F.map f ≫ F.map g`.

`F.map₂` strictly commute with compositions and preserve the identity. They also preserve the
associator, the left unitor, and the right unitor modulo some adjustments of domains and codomains
of 2-morphisms.
-/
structure OplaxFunctor (B : Type u₁) [Bicategory.{w₁, v₁} B] (C : Type u₂)
  [Bicategory.{w₂, v₂} C] extends PrelaxFunctor B C where
  mapId (a : B) : map (𝟙 a) ⟶ 𝟙 (obj a)
  mapComp {a b c : B} (f : a ⟶ b) (g : b ⟶ c) : map (f ≫ g) ⟶ map f ≫ map g
  mapComp_naturality_left :
    ∀ {a b c : B} {f f' : a ⟶ b} (η : f ⟶ f') (g : b ⟶ c),
      map₂ (η ▷ g) ≫ mapComp f' g = mapComp f g ≫ map₂ η ▷ map g := by
    aesop_cat
  mapComp_naturality_right :
    ∀ {a b c : B} (f : a ⟶ b) {g g' : b ⟶ c} (η : g ⟶ g'),
      map₂ (f ◁ η) ≫ mapComp f g' = mapComp f g ≫ map f ◁ map₂ η := by
    aesop_cat
  map₂_id : ∀ {a b : B} (f : a ⟶ b), map₂ (𝟙 f) = 𝟙 (map f) := by aesop
  map₂_comp :
    ∀ {a b : B} {f g h : a ⟶ b} (η : f ⟶ g) (θ : g ⟶ h), map₂ (η ≫ θ) = map₂ η ≫ map₂ θ := by
    aesop_cat
  -- Porting note: `map₂_associator_aux` was used here in lean 3, but this was a hack
  -- to avoid a timeout; we revert this hack here (because it was causing other problems
  -- and was not necessary in lean 4)
  map₂_associator :
    ∀ {a b c d : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d),
      map₂ (α_ f g h).hom ≫ mapComp f (g ≫ h) ≫ map f ◁ mapComp g h =
    mapComp (f ≫ g) h ≫ mapComp f g ▷ map h ≫ (α_ (map f) (map g) (map h)).hom := by
    aesop_cat
  map₂_leftUnitor :
    ∀ {a b : B} (f : a ⟶ b),
      map₂ (λ_ f).hom = mapComp (𝟙 a) f ≫ mapId a ▷ map f ≫ (λ_ (map f)).hom := by
    aesop_cat
  map₂_rightUnitor :
    ∀ {a b : B} (f : a ⟶ b),
      map₂ (ρ_ f).hom = mapComp f (𝟙 b) ≫ map f ◁ mapId b ≫ (ρ_ (map f)).hom := by
    aesop_cat

initialize_simps_projections OplaxFunctor (+toPrelaxFunctor, -obj, -map, -map₂)

namespace OplaxFunctor

-- Porting note: more stuff was tagged `simp` here in lean 3 but `reassoc (attr := simp)`
-- is doing this job a couple of lines below this.
attribute [simp] map₂_id

attribute [reassoc (attr := simp)]
  mapComp_naturality_left mapComp_naturality_right map₂_associator

-- the simpNF linter complains that `map₂_leftUnitor_assoc` etc can be
-- proved with `simp` so I move them here
attribute [reassoc] map₂_leftUnitor map₂_comp map₂_rightUnitor
attribute [simp] map₂_leftUnitor map₂_comp map₂_rightUnitor
section

/-- The prelax functor between the underlying quivers. -/
add_decl_doc OplaxFunctor.toPrelaxFunctor

attribute [nolint docBlame] CategoryTheory.OplaxFunctor.mapId
  CategoryTheory.OplaxFunctor.mapComp
  CategoryTheory.OplaxFunctor.mapComp_naturality_left
  CategoryTheory.OplaxFunctor.mapComp_naturality_right
  CategoryTheory.OplaxFunctor.map₂_id
  CategoryTheory.OplaxFunctor.map₂_comp
  CategoryTheory.OplaxFunctor.map₂_associator
  CategoryTheory.OplaxFunctor.map₂_leftUnitor
  CategoryTheory.OplaxFunctor.map₂_rightUnitor

instance hasCoeToPrelax : Coe (OplaxFunctor B C) (PrelaxFunctor B C) :=
  ⟨toPrelaxFunctor⟩

variable (F : OplaxFunctor B C)

/-- Function between 1-morphisms as a functor. -/
@[simps]
def mapFunctor (a b : B) : (a ⟶ b) ⥤ (F.obj a ⟶ F.obj b) where
  obj f := F.map f
  map η := F.map₂ η

/-- The identity oplax functor. -/
@[simps]
def id (B : Type u₁) [Bicategory.{w₁, v₁} B] : OplaxFunctor B B :=
  { PrelaxFunctor.id B with
    mapId := fun a => 𝟙 (𝟙 a)
    mapComp := fun f g => 𝟙 (f ≫ g)
  }

instance : Inhabited (OplaxFunctor B B) :=
  ⟨id B⟩

/-- Composition of oplax functors. -/
--@[simps]
def comp (F : OplaxFunctor B C) (G : OplaxFunctor C D) : OplaxFunctor B D :=
  {
    (F : PrelaxFunctor B C).comp G with
    mapId := fun a => by exact (G.mapFunctor _ _).map (F.mapId a) ≫ G.mapId (F.obj a)
    mapComp := fun f g => by
      exact (G.mapFunctor _ _).map (F.mapComp f g) ≫ G.mapComp (F.map f) (F.map g)
    mapComp_naturality_left := fun η g => by
      dsimp
      rw [← map₂_comp_assoc, mapComp_naturality_left, map₂_comp_assoc, mapComp_naturality_left,
        assoc]
    mapComp_naturality_right := fun η => by
      dsimp
      intros
      rw [← map₂_comp_assoc, mapComp_naturality_right, map₂_comp_assoc, mapComp_naturality_right,
        assoc]
    map₂_associator := fun f g h => by
      dsimp
      simp only [map₂_associator, ← map₂_comp_assoc, ← mapComp_naturality_right_assoc,
        whiskerLeft_comp, assoc]
      simp only [map₂_associator, map₂_comp, mapComp_naturality_left_assoc, comp_whiskerRight,
        assoc]
    map₂_leftUnitor := fun f => by
      dsimp
      simp only [map₂_leftUnitor, map₂_comp, mapComp_naturality_left_assoc, comp_whiskerRight,
        assoc]
    map₂_rightUnitor := fun f => by
      dsimp
      simp only [map₂_rightUnitor, map₂_comp, mapComp_naturality_right_assoc, whiskerLeft_comp,
        assoc] }

@[simps]
def map₂Iso (F : OplaxFunctor B C) {a b : B} {f g : a ⟶ b} (η : f ≅ g) : F.map f ≅ F.map g where
  hom := F.map₂ η.hom
  inv := F.map₂ η.inv
  hom_inv_id := by rw [←F.map₂_comp]; simp only [Iso.hom_inv_id, map₂_id]
  inv_hom_id := by rw [←F.map₂_comp]; simp only [Iso.inv_hom_id, map₂_id]

/-- A structure on an oplax functor that promotes an oplax functor to a pseudofunctor.
See `Pseudofunctor.mkOfOplax`.
-/
structure PseudoCore (F : OplaxFunctor B C) where
  mapIdIso (a : B) : F.map (𝟙 a) ≅ 𝟙 (F.obj a)
  mapCompIso {a b c : B} (f : a ⟶ b) (g : b ⟶ c) : F.map (f ≫ g) ≅ F.map f ≫ F.map g
  mapIdIso_hom : ∀ {a : B}, (mapIdIso a).hom = F.mapId a := by aesop_cat
  mapCompIso_hom :
    ∀ {a b c : B} (f : a ⟶ b) (g : b ⟶ c), (mapCompIso f g).hom = F.mapComp f g := by aesop_cat

attribute [nolint docBlame] CategoryTheory.OplaxFunctor.PseudoCore.mapIdIso
  CategoryTheory.OplaxFunctor.PseudoCore.mapCompIso
  CategoryTheory.OplaxFunctor.PseudoCore.mapIdIso_hom
  CategoryTheory.OplaxFunctor.PseudoCore.mapCompIso_hom

attribute [simp] PseudoCore.mapIdIso_hom PseudoCore.mapCompIso_hom

end

end OplaxFunctor

end

end CategoryTheory
