import Mathlib.Tactic.Have
/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathlib.CategoryTheory.Sites.Sieves
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Mono

/-!
# The sheaf condition for a presieve

We define what it means for a presheaf `P : Cᵒᵖ ⥤ Type v` to be a sheaf *for* a particular
presieve `R` on `X`:
* A *family of elements* `x` for `P` at `R` is an element `x_f` of `P Y` for every `f : Y ⟶ X` in
  `R`. See `FamilyOfElements`.
* The family `x` is *compatible* if, for any `f₁ : Y₁ ⟶ X` and `f₂ : Y₂ ⟶ X` both in `R`,
  and any `g₁ : Z ⟶ Y₁` and `g₂ : Z ⟶ Y₂` such that `g₁ ≫ f₁ = g₂ ≫ f₂`, the restriction of
  `x_f₁` along `g₁` agrees with the restriction of `x_f₂` along `g₂`.
  See `FamilyOfElements.Compatible`.
* An *amalgamation* `t` for the family is an element of `P X` such that for every `f : Y ⟶ X` in
  `R`, the restriction of `t` on `f` is `x_f`.
  See `FamilyOfElements.IsAmalgamation`.
We then say `P` is *separated* for `R` if every compatible family has at most one amalgamation,
and it is a *sheaf* for `R` if every compatible family has a unique amalgamation.
See `IsSeparatedFor` and `IsSheafFor`.

In the special case where `R` is a sieve, the compatibility condition can be simplified:
* The family `x` is *compatible* if, for any `f : Y ⟶ X` in `R` and `g : Z ⟶ Y`, the restriction of
  `x_f` along `g` agrees with `x_(g ≫ f)` (which is well defined since `g ≫ f` is in `R`).
See `FamilyOfElements.SieveCompatible` and `compatible_iff_sieveCompatible`.

In the special case where `C` has pullbacks, the compatibility condition can be simplified:
* The family `x` is *compatible* if, for any `f : Y ⟶ X` and `g : Z ⟶ X` both in `R`,
  the restriction of `x_f` along `π₁ : pullback f g ⟶ Y` agrees with the restriction of `x_g`
  along `π₂ : pullback f g ⟶ Z`.
See `FamilyOfElements.PullbackCompatible` and `pullbackCompatible_iff`.

We also provide equivalent conditions to satisfy alternate definitions given in the literature.

* Stacks: The condition of https://stacks.math.columbia.edu/tag/00Z8 is virtually identical to the
  statement of `isSheafFor_iff_yonedaSheafCondition` (since the bijection described there carries
  the same information as the unique existence.)

* Maclane-Moerdijk [MM92]: Using `compatible_iff_sieveCompatible`, the definitions of `IsSheaf`
  are equivalent. There are also alternate definitions given:
  - Yoneda condition: Defined in `yonedaSheafCondition` and equivalence in
    `isSheafFor_iff_yonedaSheafCondition`.
  - Matching family for presieves with pullback: `pullbackCompatible_iff`.

## Implementation

The sheaf condition is given as a proposition, rather than a subsingleton in `Type (max u₁ v)`.
This doesn't seem to make a big difference, other than making a couple of definitions noncomputable,
but it means that equivalent conditions can be given as `↔` statements rather than `≃` statements,
which can be convenient.

## References

* [MM92]: *Sheaves in geometry and logic*, Saunders MacLane, and Ieke Moerdijk:
  Chapter III, Section 4.
* [Elephant]: *Sketches of an Elephant*, P. T. Johnstone: C2.1.
* https://stacks.math.columbia.edu/tag/00VL (sheaves on a pretopology or site)
* https://stacks.math.columbia.edu/tag/00ZB (sheaves on a topology)

-/


universe w v₁ v₂ u₁ u₂

namespace CategoryTheory

open Opposite CategoryTheory Category Limits Sieve

namespace Presieve

variable {C : Type u₁} [Category.{v₁} C]
variable {P Q U : Cᵒᵖ ⥤ Type w}
variable {X Y : C} {S : Sieve X} {R : Presieve X}

/-- A family of elements for a presheaf `P` given a collection of arrows `R` with fixed codomain `X`
consists of an element of `P Y` for every `f : Y ⟶ X` in `R`.
A presheaf is a sheaf (resp, separated) if every *compatible* family of elements has exactly one
(resp, at most one) amalgamation.

This data is referred to as a `family` in [MM92], Chapter III, Section 4. It is also a concrete
version of the elements of the middle object in https://stacks.math.columbia.edu/tag/00VM which is
more useful for direct calculations. It is also used implicitly in Definition C2.1.2 in [Elephant].
-/
def FamilyOfElements (P : Cᵒᵖ ⥤ Type w) (R : Presieve X) :=
  ∀ ⦃Y : C⦄ (f : Y ⟶ X), R f → P.obj (op Y)

instance : Inhabited (FamilyOfElements P (⊥ : Presieve X)) :=
  ⟨fun _ _ => False.elim⟩

/-- A family of elements for a presheaf on the presieve `R₂` can be restricted to a smaller presieve
`R₁`.
-/
def FamilyOfElements.restrict {R₁ R₂ : Presieve X} (h : R₁ ≤ R₂) :
    FamilyOfElements P R₂ → FamilyOfElements P R₁ := fun x _ f hf => x f (h _ hf)

/-- The image of a family of elements by a morphism of presheaves. -/
def FamilyOfElements.map (p : FamilyOfElements P R) (φ : P ⟶ Q) :
    FamilyOfElements Q R :=
  fun _ f hf => φ.app _ (p f hf)

@[simp]
lemma FamilyOfElements.map_apply
    (p : FamilyOfElements P R) (φ : P ⟶ Q) {Y : C} (f : Y ⟶ X) (hf : R f) :
    p.map φ f hf = φ.app _ (p f hf) := rfl

lemma FamilyOfElements.restrict_map
    (p : FamilyOfElements P R) (φ : P ⟶ Q) {R' : Presieve X} (h : R' ≤ R) :
    (p.restrict h).map φ = (p.map φ).restrict h := rfl

/-- A family of elements for the arrow set `R` is *compatible* if for any `f₁ : Y₁ ⟶ X` and
`f₂ : Y₂ ⟶ X` in `R`, and any `g₁ : Z ⟶ Y₁` and `g₂ : Z ⟶ Y₂`, if the square `g₁ ≫ f₁ = g₂ ≫ f₂`
commutes then the elements of `P Z` obtained by restricting the element of `P Y₁` along `g₁` and
restricting the element of `P Y₂` along `g₂` are the same.

In special cases, this condition can be simplified, see `pullbackCompatible_iff` and
`compatible_iff_sieveCompatible`.

This is referred to as a "compatible family" in Definition C2.1.2 of [Elephant], and on nlab:
https://ncatlab.org/nlab/show/sheaf#GeneralDefinitionInComponents

For a more explicit version in the case where `R` is of the form `Presieve.ofArrows`, see
`CategoryTheory.Presieve.Arrows.Compatible`.
-/
def FamilyOfElements.Compatible (x : FamilyOfElements P R) : Prop :=
  ∀ ⦃Y₁ Y₂ Z⦄ (g₁ : Z ⟶ Y₁) (g₂ : Z ⟶ Y₂) ⦃f₁ : Y₁ ⟶ X⦄ ⦃f₂ : Y₂ ⟶ X⦄ (h₁ : R f₁) (h₂ : R f₂),
    g₁ ≫ f₁ = g₂ ≫ f₂ → P.map g₁.op (x f₁ h₁) = P.map g₂.op (x f₂ h₂)

/--
If the category `C` has pullbacks, this is an alternative condition for a family of elements to be
compatible: For any `f : Y ⟶ X` and `g : Z ⟶ X` in the presieve `R`, the restriction of the
given elements for `f` and `g` to the pullback agree.
This is equivalent to being compatible (provided `C` has pullbacks), shown in
`pullbackCompatible_iff`.

This is the definition for a "matching" family given in [MM92], Chapter III, Section 4,
Equation (5). Viewing the type `FamilyOfElements` as the middle object of the fork in
https://stacks.math.columbia.edu/tag/00VM, this condition expresses that `pr₀* (x) = pr₁* (x)`,
using the notation defined there.

For a more explicit version in the case where `R` is of the form `Presieve.ofArrows`, see
`CategoryTheory.Presieve.Arrows.PullbackCompatible`.
-/
def FamilyOfElements.PullbackCompatible (x : FamilyOfElements P R) [R.hasPullbacks] : Prop :=
  ∀ ⦃Y₁ Y₂⦄ ⦃f₁ : Y₁ ⟶ X⦄ ⦃f₂ : Y₂ ⟶ X⦄ (h₁ : R f₁) (h₂ : R f₂),
    haveI := hasPullbacks.has_pullbacks h₁ h₂
    P.map (pullback.fst f₁ f₂).op (x f₁ h₁) = P.map (pullback.snd f₁ f₂).op (x f₂ h₂)

theorem pullbackCompatible_iff (x : FamilyOfElements P R) [R.hasPullbacks] :
    x.Compatible ↔ x.PullbackCompatible := by
  constructor
  intro t Y₁ Y₂ f₁ f₂ hf₁ hf₂
  apply t
  haveI := hasPullbacks.has_pullbacks hf₁ hf₂
  apply pullback.condition
  intro t Y₁ Y₂ Z g₁ g₂ f₁ f₂ hf₁ hf₂ comm
  haveI := hasPullbacks.has_pullbacks hf₁ hf₂
  rw [← pullback.lift_fst _ _ comm, op_comp, FunctorToTypes.map_comp_apply, t hf₁ hf₂,
    ← FunctorToTypes.map_comp_apply, ← op_comp, pullback.lift_snd]

/-- The restriction of a compatible family is compatible. -/
theorem FamilyOfElements.Compatible.restrict {R₁ R₂ : Presieve X} (h : R₁ ≤ R₂)
    {x : FamilyOfElements P R₂} : x.Compatible → (x.restrict h).Compatible :=
  fun q _ _ _ g₁ g₂ _ _ h₁ h₂ comm => q g₁ g₂ (h _ h₁) (h _ h₂) comm

/-- Extend a family of elements to the sieve generated by an arrow set.
This is the construction described as "easy" in Lemma C2.1.3 of [Elephant].
-/
noncomputable def FamilyOfElements.sieveExtend (x : FamilyOfElements P R) :
    FamilyOfElements P (generate R : Presieve X) := fun _ _ hf =>
  P.map hf.choose_spec.choose.op (x _ hf.choose_spec.choose_spec.choose_spec.1)

/-- The extension of a compatible family to the generated sieve is compatible. -/
theorem FamilyOfElements.Compatible.sieveExtend {x : FamilyOfElements P R} (hx : x.Compatible) :
    x.sieveExtend.Compatible := by
  intro _ _ _ _ _ _ _ h₁ h₂ comm
  iterate 2 erw [← FunctorToTypes.map_comp_apply]; rw [← op_comp]
  apply hx
  simp [comm, h₁.choose_spec.choose_spec.choose_spec.2, h₂.choose_spec.choose_spec.choose_spec.2]

/-- The extension of a family agrees with the original family. -/
theorem extend_agrees {x : FamilyOfElements P R} (t : x.Compatible) {f : Y ⟶ X} (hf : R f) :
    x.sieveExtend f (le_generate R Y hf) = x f hf := by
  have h := (le_generate R Y hf).choose_spec
  unfold FamilyOfElements.sieveExtend
  rw [t h.choose (𝟙 _) _ hf _]
  simp
  rw [id_comp]
  exact h.choose_spec.choose_spec.2

/-- The restriction of an extension is the original. -/
@[simp]
theorem restrict_extend {x : FamilyOfElements P R} (t : x.Compatible) :
    x.sieveExtend.restrict (le_generate R) = x := by
  funext Y f hf
  exact extend_agrees t hf

/--
If the arrow set for a family of elements is actually a sieve (i.e. it is downward closed) then the
consistency condition can be simplified.
This is an equivalent condition, see `compatible_iff_sieveCompatible`.

This is the notion of "matching" given for families on sieves given in [MM92], Chapter III,
Section 4, Equation 1, and nlab: https://ncatlab.org/nlab/show/matching+family.
See also the discussion before Lemma C2.1.4 of [Elephant].
-/
def FamilyOfElements.SieveCompatible (x : FamilyOfElements P (S : Presieve X)) : Prop :=
  ∀ ⦃Y Z⦄ (f : Y ⟶ X) (g : Z ⟶ Y) (hf), x (g ≫ f) (S.downward_closed hf g) = P.map g.op (x f hf)

theorem compatible_iff_sieveCompatible (x : FamilyOfElements P (S : Presieve X)) :
    x.Compatible ↔ x.SieveCompatible := by
  constructor
  intro h Y Z f g hf
  simpa using h (𝟙 _) g (S.downward_closed hf g) hf (id_comp _)
  intro h Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ k
  simp_rw [← h f₁ g₁ h₁, ← h f₂ g₂ h₂]
  congr

theorem FamilyOfElements.Compatible.to_sieveCompatible {x : FamilyOfElements P (S : Presieve X)}
    (t : x.Compatible) : x.SieveCompatible :=
  (compatible_iff_sieveCompatible x).1 t

/--
Given a family of elements `x` for the sieve `S` generated by a presieve `R`, if `x` is restricted
to `R` and then extended back up to `S`, the resulting extension equals `x`.
-/
@[simp]
theorem extend_restrict {x : FamilyOfElements P (generate R)} (t : x.Compatible) :
    (x.restrict (le_generate R)).sieveExtend = x := by
  rw [compatible_iff_sieveCompatible] at t
  funext _ _ h
  apply (t _ _ _).symm.trans
  congr
  exact h.choose_spec.choose_spec.choose_spec.2

/--
Two compatible families on the sieve generated by a presieve `R` are equal if and only if they are
equal when restricted to `R`.
-/
theorem restrict_inj {x₁ x₂ : FamilyOfElements P (generate R)} (t₁ : x₁.Compatible)
    (t₂ : x₂.Compatible) : x₁.restrict (le_generate R) = x₂.restrict (le_generate R) → x₁ = x₂ :=
  fun h => by
  rw [← extend_restrict t₁, ← extend_restrict t₂]
  -- Porting note: congr fails to make progress
  apply congr_arg
  exact h

/-- Compatible families of elements for a presheaf of types `P` and a presieve `R`
    are in 1-1 correspondence with compatible families for the same presheaf and
    the sieve generated by `R`, through extension and restriction. -/
@[simps]
noncomputable def compatibleEquivGenerateSieveCompatible :
    { x : FamilyOfElements P R // x.Compatible } ≃
      { x : FamilyOfElements P (generate R : Presieve X) // x.Compatible } where
  toFun x := ⟨x.1.sieveExtend, x.2.sieveExtend⟩
  invFun x := ⟨x.1.restrict (le_generate R), x.2.restrict _⟩
  left_inv x := Subtype.ext (restrict_extend x.2)
  right_inv x := Subtype.ext (extend_restrict x.2)

theorem FamilyOfElements.comp_of_compatible (S : Sieve X) {x : FamilyOfElements P S}
    (t : x.Compatible) {f : Y ⟶ X} (hf : S f) {Z} (g : Z ⟶ Y) :
    x (g ≫ f) (S.downward_closed hf g) = P.map g.op (x f hf) := by
  simpa using t (𝟙 _) g (S.downward_closed hf g) hf (id_comp _)

section FunctorPullback

variable {D : Type u₂} [Category.{v₂} D] (F : D ⥤ C) {Z : D}
variable {T : Presieve (F.obj Z)} {x : FamilyOfElements P T}

/--
Given a family of elements of a sieve `S` on `F(X)`, we can realize it as a family of elements of
`S.functorPullback F`.
-/
def FamilyOfElements.functorPullback (x : FamilyOfElements P T) :
    FamilyOfElements (F.op ⋙ P) (T.functorPullback F) := fun _ f hf => x (F.map f) hf

theorem FamilyOfElements.Compatible.functorPullback (h : x.Compatible) :
    (x.functorPullback F).Compatible := by
  intro Z₁ Z₂ W g₁ g₂ f₁ f₂ h₁ h₂ eq
  exact h (F.map g₁) (F.map g₂) h₁ h₂ (by simp only [← F.map_comp, eq])

end FunctorPullback

/-- Given a family of elements of a sieve `S` on `X` whose values factors through `F`, we can
realize it as a family of elements of `S.functorPushforward F`. Since the preimage is obtained by
choice, this is not well-defined generally.
-/
noncomputable def FamilyOfElements.functorPushforward {D : Type u₂} [Category.{v₂} D] (F : D ⥤ C)
    {X : D} {T : Presieve X} (x : FamilyOfElements (F.op ⋙ P) T) :
    FamilyOfElements P (T.functorPushforward F) := fun Y f h => by
  obtain ⟨Z, g, h, h₁, _⟩ := getFunctorPushforwardStructure h
  exact P.map h.op (x g h₁)

section Pullback

/-- Given a family of elements of a sieve `S` on `X`, and a map `Y ⟶ X`, we can obtain a
family of elements of `S.pullback f` by taking the same elements.
-/
def FamilyOfElements.pullback (f : Y ⟶ X) (x : FamilyOfElements P (S : Presieve X)) :
    FamilyOfElements P (S.pullback f : Presieve Y) := fun _ g hg => x (g ≫ f) hg

theorem FamilyOfElements.Compatible.pullback (f : Y ⟶ X) {x : FamilyOfElements P S}
    (h : x.Compatible) : (x.pullback f).Compatible := by
  simp only [compatible_iff_sieveCompatible] at h ⊢
  intro W Z f₁ f₂ hf
  unfold FamilyOfElements.pullback
  rw [← h (f₁ ≫ f) f₂ hf]
  congr 1
  simp only [assoc]

end Pullback

/-- Given a morphism of presheaves `f : P ⟶ Q`, we can take a family of elements valued in `P` to a
family of elements valued in `Q` by composing with `f`.
-/
def FamilyOfElements.compPresheafMap (f : P ⟶ Q) (x : FamilyOfElements P R) :
    FamilyOfElements Q R := fun Y g hg => f.app (op Y) (x g hg)

@[simp]
theorem FamilyOfElements.compPresheafMap_id (x : FamilyOfElements P R) :
    x.compPresheafMap (𝟙 P) = x :=
  rfl

@[simp]
theorem FamilyOfElements.compPresheafMap_comp (x : FamilyOfElements P R) (f : P ⟶ Q)
    (g : Q ⟶ U) : (x.compPresheafMap f).compPresheafMap g = x.compPresheafMap (f ≫ g) :=
  rfl

theorem FamilyOfElements.Compatible.compPresheafMap (f : P ⟶ Q) {x : FamilyOfElements P R}
    (h : x.Compatible) : (x.compPresheafMap f).Compatible := by
  intro Z₁ Z₂ W g₁ g₂ f₁ f₂ h₁ h₂ eq
  unfold FamilyOfElements.compPresheafMap
  rwa [← FunctorToTypes.naturality, ← FunctorToTypes.naturality, h]

/--
The given element `t` of `P.obj (op X)` is an *amalgamation* for the family of elements `x` if every
restriction `P.map f.op t = x_f` for every arrow `f` in the presieve `R`.

This is the definition given in https://ncatlab.org/nlab/show/sheaf#GeneralDefinitionInComponents,
and https://ncatlab.org/nlab/show/matching+family, as well as [MM92], Chapter III, Section 4,
equation (2).
-/
def FamilyOfElements.IsAmalgamation (x : FamilyOfElements P R) (t : P.obj (op X)) : Prop :=
  ∀ ⦃Y : C⦄ (f : Y ⟶ X) (h : R f), P.map f.op t = x f h

theorem FamilyOfElements.IsAmalgamation.compPresheafMap {x : FamilyOfElements P R} {t} (f : P ⟶ Q)
    (h : x.IsAmalgamation t) : (x.compPresheafMap f).IsAmalgamation (f.app (op X) t) := by
  intro Y g hg
  dsimp [FamilyOfElements.compPresheafMap]
  change (f.app _ ≫ Q.map _) _ = _
  rw [← f.naturality, types_comp_apply, h g hg]

theorem is_compatible_of_exists_amalgamation (x : FamilyOfElements P R)
    (h : ∃ t, x.IsAmalgamation t) : x.Compatible := by
  cases' h with t ht
  intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ comm
  rw [← ht _ h₁, ← ht _ h₂, ← FunctorToTypes.map_comp_apply, ← op_comp, comm]
  simp

theorem isAmalgamation_restrict {R₁ R₂ : Presieve X} (h : R₁ ≤ R₂) (x : FamilyOfElements P R₂)
    (t : P.obj (op X)) (ht : x.IsAmalgamation t) : (x.restrict h).IsAmalgamation t := fun Y f hf =>
  ht f (h Y hf)

theorem isAmalgamation_sieveExtend {R : Presieve X} (x : FamilyOfElements P R) (t : P.obj (op X))
    (ht : x.IsAmalgamation t) : x.sieveExtend.IsAmalgamation t := by
  intro Y f hf
  dsimp [FamilyOfElements.sieveExtend]
  rw [← ht _, ← FunctorToTypes.map_comp_apply, ← op_comp, hf.choose_spec.choose_spec.choose_spec.2]

/-- A presheaf is separated for a presieve if there is at most one amalgamation. -/
def IsSeparatedFor (P : Cᵒᵖ ⥤ Type w) (R : Presieve X) : Prop :=
  ∀ (x : FamilyOfElements P R) (t₁ t₂), x.IsAmalgamation t₁ → x.IsAmalgamation t₂ → t₁ = t₂

theorem IsSeparatedFor.ext {R : Presieve X} (hR : IsSeparatedFor P R) {t₁ t₂ : P.obj (op X)}
    (h : ∀ ⦃Y⦄ ⦃f : Y ⟶ X⦄ (_ : R f), P.map f.op t₁ = P.map f.op t₂) : t₁ = t₂ :=
  hR (fun _ f _ => P.map f.op t₂) t₁ t₂ (fun _ _ hf => h hf) fun _ _ _ => rfl

theorem isSeparatedFor_iff_generate :
    IsSeparatedFor P R ↔ IsSeparatedFor P (generate R : Presieve X) := by
  constructor
  intro h x t₁ t₂ ht₁ ht₂
  apply h (x.restrict (le_generate R)) t₁ t₂ _ _
  exact isAmalgamation_restrict _ x t₁ ht₁
  exact isAmalgamation_restrict _ x t₂ ht₂
  intro h x t₁ t₂ ht₁ ht₂
  apply h x.sieveExtend
  exact isAmalgamation_sieveExtend x t₁ ht₁
  exact isAmalgamation_sieveExtend x t₂ ht₂

theorem isSeparatedFor_top (P : Cᵒᵖ ⥤ Type w) : IsSeparatedFor P (⊤ : Presieve X) :=
  fun x t₁ t₂ h₁ h₂ => by
  have q₁ := h₁ (𝟙 X) (by tauto)
  have q₂ := h₂ (𝟙 X) (by tauto)
  simp only [op_id, FunctorToTypes.map_id_apply] at q₁ q₂
  rw [q₁, q₂]

/-- We define `P` to be a sheaf for the presieve `R` if every compatible family has a unique
amalgamation.

This is the definition of a sheaf for the given presieve given in C2.1.2 of [Elephant], and
https://ncatlab.org/nlab/show/sheaf#GeneralDefinitionInComponents.
Using `compatible_iff_sieveCompatible`,
this is equivalent to the definition of a sheaf in [MM92], Chapter III, Section 4.
-/
def IsSheafFor (P : Cᵒᵖ ⥤ Type w) (R : Presieve X) : Prop :=
  ∀ x : FamilyOfElements P R, x.Compatible → ∃! t, x.IsAmalgamation t

/-- This is an equivalent condition to be a sheaf, which is useful for the abstraction to local
operators on elementary toposes. However this definition is defined only for sieves, not presieves.
The equivalence between this and `IsSheafFor` is given in `isSheafFor_iff_yonedaSheafCondition`.
This version is also useful to establish that being a sheaf is preserved under isomorphism of
presheaves.

See the discussion before Equation (3) of [MM92], Chapter III, Section 4. See also C2.1.4 of
[Elephant]. This is also a direct reformulation of <https://stacks.math.columbia.edu/tag/00Z8>.
-/
def YonedaSheafCondition (P : Cᵒᵖ ⥤ Type v₁) (S : Sieve X) : Prop :=
  ∀ f : S.functor ⟶ P, ∃! g, S.functorInclusion ≫ g = f

-- TODO: We can generalize the universe parameter v₁ above by composing with
-- appropriate `ulift_functor`s.
/-- (Implementation). This is a (primarily internal) equivalence between natural transformations
and compatible families.

Cf the discussion after Lemma 7.47.10 in <https://stacks.math.columbia.edu/tag/00YW>. See also
the proof of C2.1.4 of [Elephant], and the discussion in [MM92], Chapter III, Section 4.
-/
def natTransEquivCompatibleFamily {P : Cᵒᵖ ⥤ Type v₁} :
    (S.functor ⟶ P) ≃ { x : FamilyOfElements P (S : Presieve X) // x.Compatible } where
  toFun α := by
    refine ⟨fun Y f hf => ?_, ?_⟩
    · apply α.app (op Y) ⟨_, hf⟩
    · rw [compatible_iff_sieveCompatible]
      intro Y Z f g hf
      dsimp
      rw [← FunctorToTypes.naturality _ _ α g.op]
      rfl
  invFun t :=
    { app := fun Y f => t.1 _ f.2
      naturality := fun Y Z g => by
        ext ⟨f, hf⟩
        apply t.2.to_sieveCompatible _ }
  left_inv α := by
    ext X ⟨_, _⟩
    rfl
  right_inv := by
    rintro ⟨x, hx⟩
    rfl

/-- (Implementation). A lemma useful to prove `isSheafFor_iff_yonedaSheafCondition`. -/
theorem extension_iff_amalgamation {P : Cᵒᵖ ⥤ Type v₁} (x : S.functor ⟶ P) (g : yoneda.obj X ⟶ P) :
    S.functorInclusion ≫ g = x ↔
      (natTransEquivCompatibleFamily x).1.IsAmalgamation (yonedaEquiv g) := by
  change _ ↔ ∀ ⦃Y : C⦄ (f : Y ⟶ X) (h : S f), P.map f.op (yonedaEquiv g) = x.app (op Y) ⟨f, h⟩
  constructor
  rintro rfl Y f hf
  rw [yonedaEquiv_naturality]
  dsimp
  simp [yonedaEquiv_apply]
  -- See note [dsimp, simp].
  intro h
  ext Y ⟨f, hf⟩
  convert h f hf
  rw [yonedaEquiv_naturality]
  dsimp [yonedaEquiv]
  simp

/-- The yoneda version of the sheaf condition is equivalent to the sheaf condition.

C2.1.4 of [Elephant].
-/
theorem isSheafFor_iff_yonedaSheafCondition {P : Cᵒᵖ ⥤ Type v₁} :
    IsSheafFor P (S : Presieve X) ↔ YonedaSheafCondition P S := by
  rw [IsSheafFor, YonedaSheafCondition]
  simp_rw [extension_iff_amalgamation]
  rw [Equiv.forall_congr_left natTransEquivCompatibleFamily]
  rw [Subtype.forall]
  exact forall₂_congr fun x hx ↦ by simp [Equiv.existsUnique_congr_right]

/--
If `P` is a sheaf for the sieve `S` on `X`, a natural transformation from `S` (viewed as a functor)
to `P` can be (uniquely) extended to all of `yoneda.obj X`.

      f
   S  →  P
   ↓  ↗
   yX

-/
noncomputable def IsSheafFor.extend {P : Cᵒᵖ ⥤ Type v₁} (h : IsSheafFor P (S : Presieve X))
    (f : S.functor ⟶ P) : yoneda.obj X ⟶ P :=
  (isSheafFor_iff_yonedaSheafCondition.1 h f).exists.choose

/--
Show that the extension of `f : S.functor ⟶ P` to all of `yoneda.obj X` is in fact an extension, ie
that the triangle below commutes, provided `P` is a sheaf for `S`

      f
   S  →  P
   ↓  ↗
   yX

-/
@[reassoc (attr := simp)]
theorem IsSheafFor.functorInclusion_comp_extend {P : Cᵒᵖ ⥤ Type v₁} (h : IsSheafFor P S)
    (f : S.functor ⟶ P) : S.functorInclusion ≫ h.extend f = f :=
  (isSheafFor_iff_yonedaSheafCondition.1 h f).exists.choose_spec

/-- The extension of `f` to `yoneda.obj X` is unique. -/
theorem IsSheafFor.unique_extend {P : Cᵒᵖ ⥤ Type v₁} (h : IsSheafFor P S) {f : S.functor ⟶ P}
    (t : yoneda.obj X ⟶ P) (ht : S.functorInclusion ≫ t = f) : t = h.extend f :=
  (isSheafFor_iff_yonedaSheafCondition.1 h f).unique ht (h.functorInclusion_comp_extend f)

/--
If `P` is a sheaf for the sieve `S` on `X`, then if two natural transformations from `yoneda.obj X`
to `P` agree when restricted to the subfunctor given by `S`, they are equal.
-/
theorem IsSheafFor.hom_ext {P : Cᵒᵖ ⥤ Type v₁} (h : IsSheafFor P (S : Presieve X))
    (t₁ t₂ : yoneda.obj X ⟶ P) (ht : S.functorInclusion ≫ t₁ = S.functorInclusion ≫ t₂) :
    t₁ = t₂ :=
  (h.unique_extend t₁ ht).trans (h.unique_extend t₂ rfl).symm

/-- `P` is a sheaf for `R` iff it is separated for `R` and there exists an amalgamation. -/
theorem isSeparatedFor_and_exists_isAmalgamation_iff_isSheafFor :
    (IsSeparatedFor P R ∧ ∀ x : FamilyOfElements P R, x.Compatible → ∃ t, x.IsAmalgamation t) ↔
      IsSheafFor P R := by
  rw [IsSeparatedFor, ← forall_and]
  apply forall_congr'
  intro x
  constructor
  intro z hx
  exact exists_unique_of_exists_of_unique (z.2 hx) z.1
  intro h
  refine ⟨?_, ExistsUnique.exists ∘ h⟩
  intro t₁ t₂ ht₁ ht₂
  apply (h _).unique ht₁ ht₂
  exact is_compatible_of_exists_amalgamation x ⟨_, ht₂⟩

/-- If `P` is separated for `R` and every family has an amalgamation, then `P` is a sheaf for `R`.
-/
theorem IsSeparatedFor.isSheafFor (t : IsSeparatedFor P R) :
    (∀ x : FamilyOfElements P R, x.Compatible → ∃ t, x.IsAmalgamation t) → IsSheafFor P R := by
  rw [← isSeparatedFor_and_exists_isAmalgamation_iff_isSheafFor]
  exact And.intro t

/-- If `P` is a sheaf for `R`, it is separated for `R`. -/
theorem IsSheafFor.isSeparatedFor : IsSheafFor P R → IsSeparatedFor P R := fun q =>
  (isSeparatedFor_and_exists_isAmalgamation_iff_isSheafFor.2 q).1

/-- Get the amalgamation of the given compatible family, provided we have a sheaf. -/
noncomputable def IsSheafFor.amalgamate (t : IsSheafFor P R) (x : FamilyOfElements P R)
    (hx : x.Compatible) : P.obj (op X) :=
  (t x hx).exists.choose

theorem IsSheafFor.isAmalgamation (t : IsSheafFor P R) {x : FamilyOfElements P R}
    (hx : x.Compatible) : x.IsAmalgamation (t.amalgamate x hx) :=
  (t x hx).exists.choose_spec

@[simp]
theorem IsSheafFor.valid_glue (t : IsSheafFor P R) {x : FamilyOfElements P R} (hx : x.Compatible)
    (f : Y ⟶ X) (Hf : R f) : P.map f.op (t.amalgamate x hx) = x f Hf :=
  t.isAmalgamation hx f Hf

/-- C2.1.3 in [Elephant] -/
theorem isSheafFor_iff_generate (R : Presieve X) :
    IsSheafFor P R ↔ IsSheafFor P (generate R : Presieve X) := by
  rw [← isSeparatedFor_and_exists_isAmalgamation_iff_isSheafFor]
  rw [← isSeparatedFor_and_exists_isAmalgamation_iff_isSheafFor]
  rw [← isSeparatedFor_iff_generate]
  apply and_congr (Iff.refl _)
  constructor
  intro q x hx
  apply Exists.imp _ (q _ (hx.restrict (le_generate R)))
  intro t ht
  simpa [hx] using isAmalgamation_sieveExtend _ _ ht
  intro q x hx
  apply Exists.imp _ (q _ hx.sieveExtend)
  intro t ht
  simpa [hx] using isAmalgamation_restrict (le_generate R) _ _ ht

/-- Every presheaf is a sheaf for the family {𝟙 X}.

[Elephant] C2.1.5(i)
-/
theorem isSheafFor_singleton_iso (P : Cᵒᵖ ⥤ Type w) : IsSheafFor P (Presieve.singleton (𝟙 X)) := by
  intro x _
  refine ⟨x _ (Presieve.singleton_self _), ?_, ?_⟩
  rintro _ _ ⟨rfl, rfl⟩
  simp
  intro t ht
  simpa using ht _ (Presieve.singleton_self _)

/-- Every presheaf is a sheaf for the maximal sieve.

[Elephant] C2.1.5(ii)
-/
theorem isSheafFor_top_sieve (P : Cᵒᵖ ⥤ Type w) : IsSheafFor P ((⊤ : Sieve X) : Presieve X) := by
  rw [← generate_of_singleton_isSplitEpi (𝟙 X)]
  rw [← isSheafFor_iff_generate]
  apply isSheafFor_singleton_iso

/-- If `P` is a sheaf for `S`, and it is iso to `P'`, then `P'` is a sheaf for `S`. This shows that
"being a sheaf for a presieve" is a mathematical or hygienic property.
-/
theorem isSheafFor_iso {P' : Cᵒᵖ ⥤ Type w} (i : P ≅ P') : IsSheafFor P R → IsSheafFor P' R := by
  intro h x hx
  let x' := x.compPresheafMap i.inv
  have : x'.Compatible := FamilyOfElements.Compatible.compPresheafMap i.inv hx
  obtain ⟨t, ht1, ht2⟩ := h x' this
  use i.hom.app _ t
  fconstructor
  convert FamilyOfElements.IsAmalgamation.compPresheafMap i.hom ht1
  simp [x']
  intro y hy
  rw [show y = (i.inv.app (op X) ≫ i.hom.app (op X)) y by simp]
  simp [ht2 (i.inv.app _ y) (FamilyOfElements.IsAmalgamation.compPresheafMap i.inv hy)]

/-- If a presieve `R` on `X` has a subsieve `S` such that:

* `P` is a sheaf for `S`.
* For every `f` in `R`, `P` is separated for the pullback of `S` along `f`,

then `P` is a sheaf for `R`.

This is closely related to [Elephant] C2.1.6(i).
-/
theorem isSheafFor_subsieve_aux (P : Cᵒᵖ ⥤ Type w) {S : Sieve X} {R : Presieve X}
    (h : (S : Presieve X) ≤ R) (hS : IsSheafFor P (S : Presieve X))
    (trans : ∀ ⦃Y⦄ ⦃f : Y ⟶ X⦄, R f → IsSeparatedFor P (S.pullback f : Presieve Y)) :
    IsSheafFor P R := by
  rw [← isSeparatedFor_and_exists_isAmalgamation_iff_isSheafFor]
  constructor
  intro x t₁ t₂ ht₁ ht₂
  exact
    hS.isSeparatedFor _ _ _ (isAmalgamation_restrict h x t₁ ht₁)
      (isAmalgamation_restrict h x t₂ ht₂)
  intro x hx
  use hS.amalgamate _ (hx.restrict h)
  intro W j hj
  apply (trans hj).ext
  intro Y f hf
  rw [← FunctorToTypes.map_comp_apply, ← op_comp, hS.valid_glue (hx.restrict h) _ hf,
    FamilyOfElements.restrict, ← hx (𝟙 _) f (h _ hf) _ (id_comp _)]
  simp

/--
If `P` is a sheaf for every pullback of the sieve `S`, then `P` is a sheaf for any presieve which
contains `S`.
This is closely related to [Elephant] C2.1.6.
-/
theorem isSheafFor_subsieve (P : Cᵒᵖ ⥤ Type w) {S : Sieve X} {R : Presieve X}
    (h : (S : Presieve X) ≤ R) (trans : ∀ ⦃Y⦄ (f : Y ⟶ X),
      IsSheafFor P (S.pullback f : Presieve Y)) :
    IsSheafFor P R :=
  isSheafFor_subsieve_aux P h (by simpa using trans (𝟙 _)) fun Y f _ => (trans f).isSeparatedFor

section Arrows

variable {B : C} {I : Type*} {X : I → C} (π : (i : I) → X i ⟶ B) (P)

/--
A more explicit version of `FamilyOfElements.Compatible` for a `Presieve.ofArrows`.
-/
def Arrows.Compatible (x : (i : I) → P.obj (op (X i))) : Prop :=
  ∀ i j Z (gi : Z ⟶ X i) (gj : Z ⟶ X j), gi ≫ π i = gj ≫ π j →
    P.map gi.op (x i) = P.map gj.op (x j)

lemma FamilyOfElements.isAmalgamation_iff_ofArrows (x : FamilyOfElements P (ofArrows X π))
    (t : P.obj (op B)) :
    x.IsAmalgamation t ↔ ∀ (i : I), P.map (π i).op t = x _ (ofArrows.mk i) :=
  ⟨fun h i ↦ h _ (ofArrows.mk i), fun h _ f ⟨i⟩ ↦ h i⟩

namespace Arrows.Compatible

variable {x : (i : I) → P.obj (op (X i))}
variable {P π}

theorem exists_familyOfElements (hx : Compatible P π x) :
    ∃ (x' : FamilyOfElements P (ofArrows X π)), ∀ (i : I), x' _ (ofArrows.mk i) = x i := by
  choose i h h' using @ofArrows_surj _ _ _ _ _ π
  exact ⟨fun Y f hf ↦ P.map (eqToHom (h f hf).symm).op (x _),
    fun j ↦ (hx _ j (X j) _ (𝟙 _) <| by rw [← h', id_comp]).trans <| by simp⟩

variable (hx : Compatible P π x)

/--
A `FamilyOfElements` associated to an explicit family of elements.
-/
noncomputable
def familyOfElements : FamilyOfElements P (ofArrows X π) :=
  (exists_familyOfElements hx).choose

@[simp]
theorem familyOfElements_ofArrows_mk (i : I) :
    hx.familyOfElements _ (ofArrows.mk i) = x i :=
  (exists_familyOfElements hx).choose_spec _

theorem familyOfElements_compatible : hx.familyOfElements.Compatible := by
  rintro Y₁ Y₂ Z g₁ g₂ f₁ f₂ ⟨i⟩ ⟨j⟩ hgf
  simp [hx i j Z g₁ g₂ hgf]

end Arrows.Compatible

theorem isSheafFor_arrows_iff : (ofArrows X π).IsSheafFor P ↔
    (∀ (x : (i : I) → P.obj (op (X i))), Arrows.Compatible P π x →
    ∃! t, ∀ i, P.map (π i).op t = x i) := by
  refine ⟨fun h x hx ↦ ?_, fun h x hx ↦ ?_⟩
  obtain ⟨t, ht₁, ht₂⟩ := h _ hx.familyOfElements_compatible
  refine ⟨t, fun i ↦ ?_, fun t' ht' ↦ ht₂ _ fun _ _ ⟨i⟩ ↦ ?_⟩
  rw [ht₁ _ (ofArrows.mk i), hx.familyOfElements_ofArrows_mk]
  rw [ht', hx.familyOfElements_ofArrows_mk]
  obtain ⟨t, hA, ht⟩ := h (fun i ↦ x (π i) (ofArrows.mk _))
    (fun i j Z gi gj ↦ hx gi gj (ofArrows.mk _) (ofArrows.mk _))
  exact ⟨t, fun Y f ⟨i⟩ ↦ hA i, fun y hy ↦ ht y (fun i ↦ hy (π i) (ofArrows.mk _))⟩

variable [(ofArrows X π).hasPullbacks]

/--
A more explicit version of `FamilyOfElements.PullbackCompatible` for a `Presieve.ofArrows`.
-/
def Arrows.PullbackCompatible (x : (i : I) → P.obj (op (X i))) : Prop :=
  ∀ i j, P.map (pullback.fst (π i) (π j)).op (x i) =
    P.map (pullback.snd (π i) (π j)).op (x j)

theorem Arrows.pullbackCompatible_iff (x : (i : I) → P.obj (op (X i))) :
    Compatible P π x ↔ PullbackCompatible P π x := by
  refine ⟨fun t i j ↦ ?_, fun t i j Z gi gj comm ↦ ?_⟩
  apply t
  exact pullback.condition
  rw [← pullback.lift_fst _ _ comm, op_comp, FunctorToTypes.map_comp_apply, t i j,
    ← FunctorToTypes.map_comp_apply, ← op_comp, pullback.lift_snd]

theorem isSheafFor_arrows_iff_pullbacks : (ofArrows X π).IsSheafFor P ↔
    (∀ (x : (i : I) → P.obj (op (X i))), Arrows.PullbackCompatible P π x →
    ∃! t, ∀ i, P.map (π i).op t = x i) := by
  simp_rw [← Arrows.pullbackCompatible_iff, isSheafFor_arrows_iff]

end Arrows

end Presieve

end CategoryTheory
