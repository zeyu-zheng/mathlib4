import Mathlib.Tactic.Have
/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.CategoryTheory.Adjunction.Over
import Mathlib.CategoryTheory.Limits.Shapes.KernelPair
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.CommSq
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Assoc

/-!
# The diagonal object of a morphism.

We provide various API and isomorphisms considering the diagonal object `Δ_{Y/X} := pullback f f`
of a morphism `f : X ⟶ Y`.

-/


open CategoryTheory

noncomputable section

namespace CategoryTheory.Limits

variable {C : Type*} [Category C] {X Y Z : C}

namespace pullback

section Diagonal

variable (f : X ⟶ Y) [HasPullback f f]

/-- The diagonal object of a morphism `f : X ⟶ Y` is `Δ_{X/Y} := pullback f f`. -/
abbrev diagonalObj : C :=
  pullback f f

/-- The diagonal morphism `X ⟶ Δ_{X/Y}` for a morphism `f : X ⟶ Y`. -/
def diagonal : X ⟶ diagonalObj f :=
  pullback.lift (𝟙 _) (𝟙 _) rfl

@[reassoc (attr := simp)]
theorem diagonal_fst : diagonal f ≫ pullback.fst _ _ = 𝟙 _ :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem diagonal_snd : diagonal f ≫ pullback.snd _ _ = 𝟙 _ :=
  pullback.lift_snd _ _ _

instance : IsSplitMono (diagonal f) :=
  ⟨⟨⟨pullback.fst _ _, diagonal_fst f⟩⟩⟩

instance : IsSplitEpi (pullback.fst f f) :=
  ⟨⟨⟨diagonal f, diagonal_fst f⟩⟩⟩

instance : IsSplitEpi (pullback.snd f f) :=
  ⟨⟨⟨diagonal f, diagonal_snd f⟩⟩⟩

instance [Mono f] : IsIso (diagonal f) := by
  rw [(IsIso.inv_eq_of_inv_hom_id (diagonal_fst f)).symm]
  infer_instance

/-- The two projections `Δ_{X/Y} ⟶ X` form a kernel pair for `f : X ⟶ Y`. -/
theorem diagonal_isKernelPair : IsKernelPair f (pullback.fst f f) (pullback.snd f f) :=
  IsPullback.of_hasPullback f f

end Diagonal

end pullback

variable [HasPullbacks C]

open pullback

section

variable {U V₁ V₂ : C} (f : X ⟶ Y) (i : U ⟶ Y)
variable (i₁ : V₁ ⟶ pullback f i) (i₂ : V₂ ⟶ pullback f i)

@[reassoc (attr := simp)]
theorem pullback_diagonal_map_snd_fst_fst :
    (pullback.snd (diagonal f)
      (map (i₁ ≫ snd f i) (i₂ ≫ snd f i) f f (i₁ ≫ fst f i) (i₂ ≫ fst f i) i
        (by simp [condition]) (by simp [condition]))) ≫
      fst _ _ ≫ i₁ ≫ fst _ _ =
      pullback.fst _ _ := by
  conv_rhs => rw [← Category.comp_id (pullback.fst _ _)]
  rw [← diagonal_fst f, pullback.condition_assoc, pullback.lift_fst]

@[reassoc (attr := simp)]
theorem pullback_diagonal_map_snd_snd_fst :
    (pullback.snd (diagonal f)
      (map (i₁ ≫ snd f i) (i₂ ≫ snd f i) f f (i₁ ≫ fst f i) (i₂ ≫ fst f i) i
        (by simp [condition]) (by simp [condition]))) ≫
      snd _ _ ≫ i₂ ≫ fst _ _ =
      pullback.fst _ _ := by
  conv_rhs => rw [← Category.comp_id (pullback.fst _ _)]
  rw [← diagonal_snd f, pullback.condition_assoc, pullback.lift_snd]

variable [HasPullback i₁ i₂]

set_option maxHeartbeats 400000 in
/-- This iso witnesses the fact that
given `f : X ⟶ Y`, `i : U ⟶ Y`, and `i₁ : V₁ ⟶ X ×[Y] U`, `i₂ : V₂ ⟶ X ×[Y] U`, the diagram

```
V₁ ×[X ×[Y] U] V₂ ⟶ V₁ ×[U] V₂
        |                 |
        |                 |
        ↓                 ↓
        X         ⟶   X ×[Y] X
```

is a pullback square.
Also see `pullback_fst_map_snd_isPullback`.
-/
def pullbackDiagonalMapIso :
    pullback (diagonal f)
        (map (i₁ ≫ snd _ _) (i₂ ≫ snd _ _) f f (i₁ ≫ fst _ _) (i₂ ≫ fst _ _) i
          (by simp only [Category.assoc, condition])
          (by simp only [Category.assoc, condition])) ≅
      pullback i₁ i₂ where
  hom :=
    pullback.lift (pullback.snd _ _ ≫ pullback.fst _ _) (pullback.snd _ _ ≫ pullback.snd _ _) (by
      ext
      · simp [Category.assoc, pullback_diagonal_map_snd_fst_fst, pullback_diagonal_map_snd_snd_fst]
      · simp [Category.assoc, pullback.condition, pullback.condition_assoc])
  inv :=
    pullback.lift (pullback.fst _ _ ≫ i₁ ≫ pullback.fst _ _)
      (pullback.map _ _ _ _ (𝟙 _) (𝟙 _) (pullback.snd _ _) (Category.id_comp _).symm
        (Category.id_comp _).symm) (by
        ext
        · simp only [Category.assoc, diagonal_fst, Category.comp_id, limit.lift_π,
            PullbackCone.mk_pt, PullbackCone.mk_π_app, limit.lift_π_assoc, cospan_left]
        · simp only [condition_assoc, Category.assoc, diagonal_snd, Category.comp_id,
            limit.lift_π, PullbackCone.mk_pt, PullbackCone.mk_π_app,
            limit.lift_π_assoc, cospan_right])

@[reassoc (attr := simp)]
theorem pullbackDiagonalMapIso_hom_fst :
    (pullbackDiagonalMapIso f i i₁ i₂).hom ≫ pullback.fst _ _ =
      pullback.snd _ _ ≫ pullback.fst _ _ := by
  delta pullbackDiagonalMapIso
  simp

@[reassoc (attr := simp)]
theorem pullbackDiagonalMapIso_hom_snd :
    (pullbackDiagonalMapIso f i i₁ i₂).hom ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ pullback.snd _ _ := by
  delta pullbackDiagonalMapIso
  simp

@[reassoc (attr := simp)]
theorem pullbackDiagonalMapIso_inv_fst :
    (pullbackDiagonalMapIso f i i₁ i₂).inv ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ i₁ ≫ pullback.fst _ _ := by
  delta pullbackDiagonalMapIso
  simp

@[reassoc (attr := simp)]
theorem pullbackDiagonalMapIso_inv_snd_fst :
    (pullbackDiagonalMapIso f i i₁ i₂).inv ≫ pullback.snd _ _ ≫ pullback.fst _ _ =
      pullback.fst _ _ := by
  delta pullbackDiagonalMapIso
  simp

@[reassoc (attr := simp)]
theorem pullbackDiagonalMapIso_inv_snd_snd :
    (pullbackDiagonalMapIso f i i₁ i₂).inv ≫ pullback.snd _ _ ≫ pullback.snd _ _ =
      pullback.snd _ _ := by
  delta pullbackDiagonalMapIso
  simp

theorem pullback_fst_map_snd_isPullback :
    IsPullback (fst _ _ ≫ i₁ ≫ fst _ _)
      (map i₁ i₂ (i₁ ≫ snd _ _) (i₂ ≫ snd _ _) _ _ _
        (Category.id_comp _).symm (Category.id_comp _).symm)
      (diagonal f)
      (map (i₁ ≫ snd _ _) (i₂ ≫ snd _ _) f f (i₁ ≫ fst _ _) (i₂ ≫ fst _ _) i (by simp [condition])
        (by simp [condition])) :=
  IsPullback.of_iso_pullback ⟨by ext <;> simp [condition_assoc]⟩
    (pullbackDiagonalMapIso f i i₁ i₂).symm (pullbackDiagonalMapIso_inv_fst f i i₁ i₂)
    (by aesop_cat)

end

section

variable {S T : C} (f : X ⟶ T) (g : Y ⟶ T) (i : T ⟶ S)
variable [HasPullback i i] [HasPullback f g] [HasPullback (f ≫ i) (g ≫ i)]
variable
  [HasPullback (diagonal i)
      (pullback.map (f ≫ i) (g ≫ i) i i f g (𝟙 _) (Category.comp_id _) (Category.comp_id _))]

/-- This iso witnesses the fact that
given `f : X ⟶ T`, `g : Y ⟶ T`, and `i : T ⟶ S`, the diagram

```
X ×ₜ Y ⟶ X ×ₛ Y
  |         |
  |         |
  ↓         ↓
  T    ⟶  T ×ₛ T
```

is a pullback square.
Also see `pullback_map_diagonal_isPullback`.
-/
def pullbackDiagonalMapIdIso :
    pullback (diagonal i)
        (pullback.map (f ≫ i) (g ≫ i) i i f g (𝟙 _) (Category.comp_id _) (Category.comp_id _)) ≅
      pullback f g := by
  refine ?_ ≪≫
    pullbackDiagonalMapIso i (𝟙 _) (f ≫ inv (pullback.fst _ _)) (g ≫ inv (pullback.fst _ _)) ≪≫ ?_
  · refine @asIso _ _ _ _ (pullback.map _ _ _ _ (𝟙 T) ((pullback.congrHom ?_ ?_).hom) (𝟙 _) ?_ ?_)
      ?_
    · rw [← Category.comp_id (pullback.snd ..), ← condition, Category.assoc, IsIso.inv_hom_id_assoc]
    · rw [← Category.comp_id (pullback.snd ..), ← condition, Category.assoc, IsIso.inv_hom_id_assoc]
    · rw [Category.comp_id, Category.id_comp]
    · ext <;> simp
    · infer_instance
  · refine @asIso _ _ _ _ (pullback.map _ _ _ _ (𝟙 _) (𝟙 _) (pullback.fst _ _) ?_ ?_) ?_
    · rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id, Category.id_comp]
    · rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id, Category.id_comp]
    · infer_instance

@[reassoc (attr := simp)]
theorem pullbackDiagonalMapIdIso_hom_fst :
    (pullbackDiagonalMapIdIso f g i).hom ≫ pullback.fst _ _ =
      pullback.snd _ _ ≫ pullback.fst _ _ := by
  delta pullbackDiagonalMapIdIso
  simp

@[reassoc (attr := simp)]
theorem pullbackDiagonalMapIdIso_hom_snd :
    (pullbackDiagonalMapIdIso f g i).hom ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ pullback.snd _ _ := by
  delta pullbackDiagonalMapIdIso
  simp

@[reassoc (attr := simp)]
theorem pullbackDiagonalMapIdIso_inv_fst :
    (pullbackDiagonalMapIdIso f g i).inv ≫ pullback.fst _ _ = pullback.fst _ _ ≫ f := by
  rw [Iso.inv_comp_eq, ← Category.comp_id (pullback.fst _ _), ← diagonal_fst i,
    pullback.condition_assoc]
  simp

@[reassoc (attr := simp)]
theorem pullbackDiagonalMapIdIso_inv_snd_fst :
    (pullbackDiagonalMapIdIso f g i).inv ≫ pullback.snd _ _ ≫ pullback.fst _ _ =
      pullback.fst _ _ := by
  rw [Iso.inv_comp_eq]
  simp

@[reassoc (attr := simp)]
theorem pullbackDiagonalMapIdIso_inv_snd_snd :
    (pullbackDiagonalMapIdIso f g i).inv ≫ pullback.snd _ _ ≫ pullback.snd _ _ =
      pullback.snd _ _ := by
  rw [Iso.inv_comp_eq]
  simp

theorem pullback.diagonal_comp (f : X ⟶ Y) (g : Y ⟶ Z) [HasPullback f f] [HasPullback g g]
    [HasPullback (f ≫ g) (f ≫ g)] :
    diagonal (f ≫ g) = diagonal f ≫ (pullbackDiagonalMapIdIso f f g).inv ≫ pullback.snd _ _ := by
  ext <;> simp

theorem pullback_map_diagonal_isPullback :
    IsPullback (pullback.fst _ _ ≫ f)
      (pullback.map f g (f ≫ i) (g ≫ i) _ _ i (Category.id_comp _).symm (Category.id_comp _).symm)
      (diagonal i)
      (pullback.map (f ≫ i) (g ≫ i) i i f g (𝟙 _) (Category.comp_id _) (Category.comp_id _)) := by
  apply IsPullback.of_iso_pullback _ (pullbackDiagonalMapIdIso f g i).symm
  simp
  ext <;> simp
  constructor
  ext <;> simp [condition]

/-- The diagonal object of `X ×[Z] Y ⟶ X` is isomorphic to `Δ_{Y/Z} ×[Z] X`. -/
def diagonalObjPullbackFstIso {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) :
    diagonalObj (pullback.fst f g) ≅
      pullback (pullback.snd _ _ ≫ g : diagonalObj g ⟶ Z) f :=
  pullbackRightPullbackFstIso _ _ _ ≪≫
    pullback.congrHom pullback.condition rfl ≪≫
      pullbackAssoc _ _ _ _ ≪≫ pullbackSymmetry _ _ ≪≫ pullback.congrHom pullback.condition rfl

@[reassoc (attr := simp)]
theorem diagonalObjPullbackFstIso_hom_fst_fst {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) :
    (diagonalObjPullbackFstIso f g).hom ≫ pullback.fst _ _ ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ pullback.snd _ _ := by
  delta diagonalObjPullbackFstIso
  simp

@[reassoc (attr := simp)]
theorem diagonalObjPullbackFstIso_hom_fst_snd {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) :
    (diagonalObjPullbackFstIso f g).hom ≫ pullback.fst _ _ ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ pullback.snd _ _ := by
  delta diagonalObjPullbackFstIso
  simp

@[reassoc (attr := simp)]
theorem diagonalObjPullbackFstIso_hom_snd {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) :
    (diagonalObjPullbackFstIso f g).hom ≫ pullback.snd _ _ =
      pullback.fst _ _ ≫ pullback.fst _ _ := by
  delta diagonalObjPullbackFstIso
  simp

@[reassoc (attr := simp)]
theorem diagonalObjPullbackFstIso_inv_fst_fst {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) :
    (diagonalObjPullbackFstIso f g).inv ≫ pullback.fst _ _ ≫ pullback.fst _ _ =
      pullback.snd _ _ := by
  delta diagonalObjPullbackFstIso
  simp

@[reassoc (attr := simp)]
theorem diagonalObjPullbackFstIso_inv_fst_snd {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) :
    (diagonalObjPullbackFstIso f g).inv ≫ pullback.fst _ _ ≫ pullback.snd _ _ =
      pullback.fst _ _ ≫ pullback.fst _ _ := by
  delta diagonalObjPullbackFstIso
  simp

@[reassoc (attr := simp)]
theorem diagonalObjPullbackFstIso_inv_snd_fst {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) :
    (diagonalObjPullbackFstIso f g).inv ≫ pullback.snd _ _ ≫ pullback.fst _ _ =
      pullback.snd _ _ := by
  delta diagonalObjPullbackFstIso
  simp

@[reassoc (attr := simp)]
theorem diagonalObjPullbackFstIso_inv_snd_snd {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) :
    (diagonalObjPullbackFstIso f g).inv ≫ pullback.snd _ _ ≫ pullback.snd _ _ =
      pullback.fst _ _ ≫ pullback.snd _ _ := by
  delta diagonalObjPullbackFstIso
  simp

theorem diagonal_pullback_fst {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) :
    diagonal (pullback.fst f g) =
      (pullbackSymmetry _ _).hom ≫
        ((Over.pullback f).map
              (Over.homMk (diagonal g) : Over.mk g ⟶ Over.mk (pullback.snd _ _ ≫ g))).left ≫
          (diagonalObjPullbackFstIso f g).inv := by
  ext <;> dsimp <;> simp

end

/-- Given the following diagram with `S ⟶ S'` a monomorphism,

```
    X ⟶ X'
      ↘      ↘
        S ⟶ S'
      ↗      ↗
    Y ⟶ Y'
```

This iso witnesses the fact that

```
      X ×[S] Y ⟶ (X' ×[S'] Y') ×[Y'] Y
          |                  |
          |                  |
          ↓                  ↓
(X' ×[S'] Y') ×[X'] X ⟶ X' ×[S'] Y'
```

is a pullback square. The diagonal map of this square is `pullback.map`.
Also see `pullback_lift_map_is_pullback`.
-/
@[simps]
def pullbackFstFstIso {X Y S X' Y' S' : C} (f : X ⟶ S) (g : Y ⟶ S) (f' : X' ⟶ S') (g' : Y' ⟶ S')
    (i₁ : X ⟶ X') (i₂ : Y ⟶ Y') (i₃ : S ⟶ S') (e₁ : f ≫ i₃ = i₁ ≫ f') (e₂ : g ≫ i₃ = i₂ ≫ g')
    [Mono i₃] :
    pullback (pullback.fst _ _ : pullback (pullback.fst _ _ : pullback f' g' ⟶ _) i₁ ⟶ _)
        (pullback.fst _ _ : pullback (pullback.snd _ _ : pullback f' g' ⟶ _) i₂ ⟶ _) ≅
      pullback f g where
  hom :=
    pullback.lift (pullback.fst _ _ ≫ pullback.snd _ _) (pullback.snd _ _ ≫ pullback.snd _ _)
      (by
        rw [← cancel_mono i₃, Category.assoc, Category.assoc, Category.assoc, Category.assoc, e₁,
          e₂, ← pullback.condition_assoc, pullback.condition_assoc, pullback.condition,
          pullback.condition_assoc])
  inv :=
    pullback.lift
      (pullback.lift (pullback.map _ _ _ _ _ _ _ e₁ e₂) (pullback.fst _ _) (pullback.lift_fst ..))
      (pullback.lift (pullback.map _ _ _ _ _ _ _ e₁ e₂) (pullback.snd _ _) (pullback.lift_snd ..))
      (by rw [pullback.lift_fst, pullback.lift_fst])
  hom_inv_id := by
    -- We could use `ext` here to immediately descend to the leaf goals,
    -- but it only obscures the structure.
    apply pullback.hom_ext
    · apply pullback.hom_ext
      · apply pullback.hom_ext
        · simp only [Category.assoc, lift_fst, lift_fst_assoc, Category.id_comp]
          rw [condition]
        · simp [Category.assoc, lift_snd, condition_assoc, condition]
      · simp only [Category.assoc, lift_fst_assoc, lift_snd, lift_fst, Category.id_comp]
    · apply pullback.hom_ext
      · apply pullback.hom_ext
        · simp only [Category.assoc, lift_snd_assoc, lift_fst_assoc, lift_fst, Category.id_comp]
          rw [← condition_assoc, condition]
        · simp only [Category.assoc, lift_snd, lift_fst_assoc, lift_snd_assoc, Category.id_comp]
          rw [condition]
      · simp only [Category.assoc, lift_snd_assoc, lift_snd, Category.id_comp]
  inv_hom_id := by
    apply pullback.hom_ext
    · simp only [Category.assoc, lift_fst, lift_fst_assoc, lift_snd, Category.id_comp]
    · simp only [Category.assoc, lift_snd, lift_snd_assoc, Category.id_comp]

theorem pullback_map_eq_pullbackFstFstIso_inv {X Y S X' Y' S' : C} (f : X ⟶ S) (g : Y ⟶ S)
    (f' : X' ⟶ S') (g' : Y' ⟶ S') (i₁ : X ⟶ X') (i₂ : Y ⟶ Y') (i₃ : S ⟶ S')
    (e₁ : f ≫ i₃ = i₁ ≫ f') (e₂ : g ≫ i₃ = i₂ ≫ g') [Mono i₃] :
    pullback.map f g f' g' i₁ i₂ i₃ e₁ e₂ =
      (pullbackFstFstIso f g f' g' i₁ i₂ i₃ e₁ e₂).inv ≫ pullback.snd _ _ ≫ pullback.fst _ _ := by
  simp only [pullbackFstFstIso_inv, lift_snd_assoc, lift_fst]

theorem pullback_lift_map_isPullback {X Y S X' Y' S' : C} (f : X ⟶ S) (g : Y ⟶ S) (f' : X' ⟶ S')
    (g' : Y' ⟶ S') (i₁ : X ⟶ X') (i₂ : Y ⟶ Y') (i₃ : S ⟶ S') (e₁ : f ≫ i₃ = i₁ ≫ f')
    (e₂ : g ≫ i₃ = i₂ ≫ g') [Mono i₃] :
    IsPullback (pullback.lift (pullback.map f g f' g' i₁ i₂ i₃ e₁ e₂) (fst _ _) (lift_fst _ _ _))
      (pullback.lift (pullback.map f g f' g' i₁ i₂ i₃ e₁ e₂) (snd _ _) (lift_snd _ _ _))
      (pullback.fst _ _) (pullback.fst _ _) :=
  IsPullback.of_iso_pullback ⟨by rw [lift_fst, lift_fst]⟩
    (pullbackFstFstIso f g f' g' i₁ i₂ i₃ e₁ e₂).symm (by simp) (by simp)

end CategoryTheory.Limits
