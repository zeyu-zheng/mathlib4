import Mathlib.Tactic.Have
/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Junyan Xu
-/
import Mathlib.Topology.Sheaves.PUnit
import Mathlib.Topology.Sheaves.Stalks
import Mathlib.Topology.Sheaves.Functors

/-!
# Skyscraper (pre)sheaves

A skyscraper (pre)sheaf `𝓕 : (Pre)Sheaf C X` is the (pre)sheaf with value `A` at point `p₀` that is
supported only at open sets contain `p₀`, i.e. `𝓕(U) = A` if `p₀ ∈ U` and `𝓕(U) = *` if `p₀ ∉ U`
where `*` is a terminal object of `C`. In terms of stalks, `𝓕` is supported at all specializations
of `p₀`, i.e. if `p₀ ⤳ x` then `𝓕ₓ ≅ A` and if `¬ p₀ ⤳ x` then `𝓕ₓ ≅ *`.

## Main definitions

* `skyscraperPresheaf`: `skyscraperPresheaf p₀ A` is the skyscraper presheaf at point `p₀` with
  value `A`.
* `skyscraperSheaf`: the skyscraper presheaf satisfies the sheaf condition.

## Main statements

* `skyscraperPresheafStalkOfSpecializes`: if `y ∈ closure {p₀}` then the stalk of
  `skyscraperPresheaf p₀ A` at `y` is `A`.
* `skyscraperPresheafStalkOfNotSpecializes`: if `y ∉ closure {p₀}` then the stalk of
  `skyscraperPresheaf p₀ A` at `y` is `*` the terminal object.

TODO: generalize universe level when calculating stalks, after generalizing universe level of stalk.
-/

noncomputable section

open TopologicalSpace TopCat CategoryTheory CategoryTheory.Limits Opposite

universe u v w

variable {X : TopCat.{u}} (p₀ : X) [∀ U : Opens X, Decidable (p₀ ∈ U)]

section

variable {C : Type v} [Category.{w} C] [HasTerminal C] (A : C)

/-- A skyscraper presheaf is a presheaf supported at a single point: if `p₀ ∈ X` is a specified
point, then the skyscraper presheaf `𝓕` with value `A` is defined by `U ↦ A` if `p₀ ∈ U` and
`U ↦ *` if `p₀ ∉ A` where `*` is some terminal object.
-/
@[simps]
def skyscraperPresheaf : Presheaf C X where
  obj U := if p₀ ∈ unop U then A else terminal C
  map {U V} i :=
    if h : p₀ ∈ unop V then eqToHom <| by dsimp; erw [if_pos h, if_pos (leOfHom i.unop h)]
    else ((if_neg h).symm.ndrec terminalIsTerminal).from _
  map_id U :=
    (em (p₀ ∈ U.unop)).elim (fun h => dif_pos h) fun h =>
      ((if_neg h).symm.ndrec terminalIsTerminal).hom_ext _ _
  map_comp {U V W} iVU iWV := by
    by_cases hW : p₀ ∈ unop W
    · have hV : p₀ ∈ unop V := leOfHom iWV.unop hW
      simp only [dif_pos hW, dif_pos hV, eqToHom_trans]
    · dsimp; rw [dif_neg hW]; apply ((if_neg hW).symm.ndrec terminalIsTerminal).hom_ext

theorem skyscraperPresheaf_eq_pushforward
    [hd : ∀ U : Opens (TopCat.of PUnit.{u + 1}), Decidable (PUnit.unit ∈ U)] :
    skyscraperPresheaf p₀ A =
      ContinuousMap.const (TopCat.of PUnit) p₀ _*
        skyscraperPresheaf (X := TopCat.of PUnit) PUnit.unit A := by
  convert_to @skyscraperPresheaf X p₀ (fun U => hd <| (Opens.map <| ContinuousMap.const _ p₀).obj U)
    C _ _ A = _ <;> congr

/-- Taking skyscraper presheaf at a point is functorial: `c ↦ skyscraper p₀ c` defines a functor by
sending every `f : a ⟶ b` to the natural transformation `α` defined as: `α(U) = f : a ⟶ b` if
`p₀ ∈ U` and the unique morphism to a terminal object in `C` if `p₀ ∉ U`.
-/
@[simps]
def SkyscraperPresheafFunctor.map' {a b : C} (f : a ⟶ b) :
    skyscraperPresheaf p₀ a ⟶ skyscraperPresheaf p₀ b where
  app U :=
    if h : p₀ ∈ U.unop then eqToHom (if_pos h) ≫ f ≫ eqToHom (if_pos h).symm
    else ((if_neg h).symm.ndrec terminalIsTerminal).from _
  naturality U V i := by
    simp only [skyscraperPresheaf_map]
    by_cases hV : p₀ ∈ V.unop
    · have hU : p₀ ∈ U.unop := leOfHom i.unop hV
      simp only [skyscraperPresheaf_obj, hU, hV, ↓reduceDIte, eqToHom_trans_assoc, Category.assoc,
        eqToHom_trans]
    · apply ((if_neg hV).symm.ndrec terminalIsTerminal).hom_ext

theorem SkyscraperPresheafFunctor.map'_id {a : C} :
    SkyscraperPresheafFunctor.map' p₀ (𝟙 a) = 𝟙 _ := by
  ext U
  simp only [SkyscraperPresheafFunctor.map'_app, NatTrans.id_app]; split_ifs <;> aesop_cat

theorem SkyscraperPresheafFunctor.map'_comp {a b c : C} (f : a ⟶ b) (g : b ⟶ c) :
    SkyscraperPresheafFunctor.map' p₀ (f ≫ g) =
      SkyscraperPresheafFunctor.map' p₀ f ≫ SkyscraperPresheafFunctor.map' p₀ g := by
  ext U
  simp only [SkyscraperPresheafFunctor.map'_app, NatTrans.comp_app]
  split_ifs with h <;> aesop_cat

/-- Taking skyscraper presheaf at a point is functorial: `c ↦ skyscraper p₀ c` defines a functor by
sending every `f : a ⟶ b` to the natural transformation `α` defined as: `α(U) = f : a ⟶ b` if
`p₀ ∈ U` and the unique morphism to a terminal object in `C` if `p₀ ∉ U`.
-/
@[simps]
def skyscraperPresheafFunctor : C ⥤ Presheaf C X where
  obj := skyscraperPresheaf p₀
  map := SkyscraperPresheafFunctor.map' p₀
  map_id _ := SkyscraperPresheafFunctor.map'_id p₀
  map_comp := SkyscraperPresheafFunctor.map'_comp p₀

end

section

-- In this section, we calculate the stalks for skyscraper presheaves.
-- We need to restrict universe level.
variable {C : Type v} [Category.{u} C] (A : C) [HasTerminal C]

/-- The cocone at `A` for the stalk functor of `skyscraperPresheaf p₀ A` when `y ∈ closure {p₀}`
-/
@[simps]
def skyscraperPresheafCoconeOfSpecializes {y : X} (h : p₀ ⤳ y) :
    Cocone ((OpenNhds.inclusion y).op ⋙ skyscraperPresheaf p₀ A) where
  pt := A
  ι :=
    { app := fun U => eqToHom <| if_pos <| h.mem_open U.unop.1.2 U.unop.2
      naturality := fun U V inc => by
        change dite _ _ _ ≫ _ = _; rw [dif_pos]
        swap -- Porting note: swap goal to prevent proving same thing twice
        · exact h.mem_open V.unop.1.2 V.unop.2
        · simp only [Functor.comp_obj, Functor.op_obj, skyscraperPresheaf_obj, unop_op,
            Functor.const_obj_obj, eqToHom_trans, Functor.const_obj_map, Category.comp_id] }

/--
The cocone at `A` for the stalk functor of `skyscraperPresheaf p₀ A` when `y ∈ closure {p₀}` is a
colimit
-/
noncomputable def skyscraperPresheafCoconeIsColimitOfSpecializes {y : X} (h : p₀ ⤳ y) :
    IsColimit (skyscraperPresheafCoconeOfSpecializes p₀ A h) where
  desc c := eqToHom (if_pos trivial).symm ≫ c.ι.app (op ⊤)
  fac c U := by
    dsimp -- Porting note (#11227):added a `dsimp`
    rw [← c.w (homOfLE <| (le_top : unop U ≤ _)).op]
    change _ ≫ _ ≫ dite _ _ _ ≫ _ = _
    rw [dif_pos]
    · simp only [skyscraperPresheafCoconeOfSpecializes_ι_app, eqToHom_trans_assoc,
        eqToHom_refl, Category.id_comp, unop_op, op_unop]
    · exact h.mem_open U.unop.1.2 U.unop.2
  uniq c f h := by
    dsimp -- Porting note (#11227):added a `dsimp`
    rw [← h, skyscraperPresheafCoconeOfSpecializes_ι_app, eqToHom_trans_assoc, eqToHom_refl,
      Category.id_comp]

/-- If `y ∈ closure {p₀}`, then the stalk of `skyscraperPresheaf p₀ A` at `y` is `A`.
-/
noncomputable def skyscraperPresheafStalkOfSpecializes [HasColimits C] {y : X} (h : p₀ ⤳ y) :
    (skyscraperPresheaf p₀ A).stalk y ≅ A :=
  colimit.isoColimitCocone ⟨_, skyscraperPresheafCoconeIsColimitOfSpecializes p₀ A h⟩

/-- The cocone at `*` for the stalk functor of `skyscraperPresheaf p₀ A` when `y ∉ closure {p₀}`
-/
@[simps]
def skyscraperPresheafCocone (y : X) :
    Cocone ((OpenNhds.inclusion y).op ⋙ skyscraperPresheaf p₀ A) where
  pt := terminal C
  ι :=
    { app := fun _ => terminal.from _
      naturality := fun _ _ _ => terminalIsTerminal.hom_ext _ _ }

/--
The cocone at `*` for the stalk functor of `skyscraperPresheaf p₀ A` when `y ∉ closure {p₀}` is a
colimit
-/
noncomputable def skyscraperPresheafCoconeIsColimitOfNotSpecializes {y : X} (h : ¬p₀ ⤳ y) :
    IsColimit (skyscraperPresheafCocone p₀ A y) :=
  let h1 : ∃ U : OpenNhds y, p₀ ∉ U.1 :=
    let ⟨U, ho, h₀, hy⟩ := not_specializes_iff_exists_open.mp h
    ⟨⟨⟨U, ho⟩, h₀⟩, hy⟩
  { desc := fun c => eqToHom (if_neg h1.choose_spec).symm ≫ c.ι.app (op h1.choose)
    fac := fun c U => by
      change _ = c.ι.app (op U.unop)
      simp only [← c.w (homOfLE <| @inf_le_left _ _ h1.choose U.unop).op, ←
        c.w (homOfLE <| @inf_le_right _ _ h1.choose U.unop).op, ← Category.assoc]
      congr 1
      refine ((if_neg ?_).symm.ndrec terminalIsTerminal).hom_ext _ _
      exact fun h => h1.choose_spec h.1
    uniq := fun c f H => by
      dsimp -- Porting note (#11227):added a `dsimp`
      rw [← Category.id_comp f, ← H, ← Category.assoc]
      congr 1; apply terminalIsTerminal.hom_ext }

/-- If `y ∉ closure {p₀}`, then the stalk of `skyscraperPresheaf p₀ A` at `y` is isomorphic to a
terminal object.
-/
noncomputable def skyscraperPresheafStalkOfNotSpecializes [HasColimits C] {y : X} (h : ¬p₀ ⤳ y) :
    (skyscraperPresheaf p₀ A).stalk y ≅ terminal C :=
  colimit.isoColimitCocone ⟨_, skyscraperPresheafCoconeIsColimitOfNotSpecializes _ A h⟩

/-- If `y ∉ closure {p₀}`, then the stalk of `skyscraperPresheaf p₀ A` at `y` is a terminal object
-/
def skyscraperPresheafStalkOfNotSpecializesIsTerminal [HasColimits C] {y : X} (h : ¬p₀ ⤳ y) :
    IsTerminal ((skyscraperPresheaf p₀ A).stalk y) :=
  IsTerminal.ofIso terminalIsTerminal <| (skyscraperPresheafStalkOfNotSpecializes _ _ h).symm

theorem skyscraperPresheaf_isSheaf : (skyscraperPresheaf p₀ A).IsSheaf := by
  classical exact
    (Presheaf.isSheaf_iso_iff (eqToIso <| skyscraperPresheaf_eq_pushforward p₀ A)).mpr <|
      (Sheaf.pushforward_sheaf_of_sheaf _
        (Presheaf.isSheaf_on_punit_of_isTerminal _ (by
          dsimp [skyscraperPresheaf]
          rw [if_neg]
          exact terminalIsTerminal
          #adaptation_note /-- 2024-03-24
          Previously the universe annotation was not needed here. -/
          exact Set.not_mem_empty PUnit.unit.{u+1})))

/--
The skyscraper presheaf supported at `p₀` with value `A` is the sheaf that assigns `A` to all opens
`U` that contain `p₀` and assigns `*` otherwise.
-/
def skyscraperSheaf : Sheaf C X :=
  ⟨skyscraperPresheaf p₀ A, skyscraperPresheaf_isSheaf _ _⟩

/-- Taking skyscraper sheaf at a point is functorial: `c ↦ skyscraper p₀ c` defines a functor by
sending every `f : a ⟶ b` to the natural transformation `α` defined as: `α(U) = f : a ⟶ b` if
`p₀ ∈ U` and the unique morphism to a terminal object in `C` if `p₀ ∉ U`.
-/
def skyscraperSheafFunctor : C ⥤ Sheaf C X where
  obj c := skyscraperSheaf p₀ c
  map f := Sheaf.Hom.mk <| (skyscraperPresheafFunctor p₀).map f
  map_id _ := Sheaf.Hom.ext _ _ <| (skyscraperPresheafFunctor p₀).map_id _
  map_comp _ _ := Sheaf.Hom.ext _ _ <| (skyscraperPresheafFunctor p₀).map_comp _ _

namespace StalkSkyscraperPresheafAdjunctionAuxs

variable [HasColimits C]

/-- If `f : 𝓕.stalk p₀ ⟶ c`, then a natural transformation `𝓕 ⟶ skyscraperPresheaf p₀ c` can be
defined by: `𝓕.germ p₀ ≫ f : 𝓕(U) ⟶ c` if `p₀ ∈ U` and the unique morphism to a terminal object
if `p₀ ∉ U`.
-/
@[simps]
def toSkyscraperPresheaf {𝓕 : Presheaf C X} {c : C} (f : 𝓕.stalk p₀ ⟶ c) :
    𝓕 ⟶ skyscraperPresheaf p₀ c where
  app U :=
    if h : p₀ ∈ U.unop then 𝓕.germ ⟨p₀, h⟩ ≫ f ≫ eqToHom (if_pos h).symm
    else ((if_neg h).symm.ndrec terminalIsTerminal).from _
  naturality U V inc := by
    -- Porting note: don't know why original proof fell short of working, add `aesop_cat` finished
    -- the proofs anyway
    dsimp
    by_cases hV : p₀ ∈ V.unop
    · have hU : p₀ ∈ U.unop := leOfHom inc.unop hV
      split_ifs
      erw [← Category.assoc, 𝓕.germ_res inc.unop, Category.assoc, Category.assoc, eqToHom_trans]
    · split_ifs
      exact ((if_neg hV).symm.ndrec terminalIsTerminal).hom_ext ..

/-- If `f : 𝓕 ⟶ skyscraperPresheaf p₀ c` is a natural transformation, then there is a morphism
`𝓕.stalk p₀ ⟶ c` defined as the morphism from colimit to cocone at `c`.
-/
def fromStalk {𝓕 : Presheaf C X} {c : C} (f : 𝓕 ⟶ skyscraperPresheaf p₀ c) : 𝓕.stalk p₀ ⟶ c :=
  let χ : Cocone ((OpenNhds.inclusion p₀).op ⋙ 𝓕) :=
    Cocone.mk c <|
      { app := fun U => f.app (op U.unop.1) ≫ eqToHom (if_pos U.unop.2)
        naturality := fun U V inc => by
          dsimp
          erw [Category.comp_id, ← Category.assoc, comp_eqToHom_iff, Category.assoc,
            eqToHom_trans, f.naturality, skyscraperPresheaf_map]
          -- Porting note: added this `dsimp` and `rfl` in the end
          dsimp only [skyscraperPresheaf_obj, unop_op, Eq.ndrec]
          have hV : p₀ ∈ (OpenNhds.inclusion p₀).obj V.unop := V.unop.2; split_ifs <;>
          simp only [comp_eqToHom_iff, Category.assoc, eqToHom_trans, eqToHom_refl,
            Category.comp_id] <;> rfl }
  colimit.desc _ χ

theorem to_skyscraper_fromStalk {𝓕 : Presheaf C X} {c : C} (f : 𝓕 ⟶ skyscraperPresheaf p₀ c) :
    toSkyscraperPresheaf p₀ (fromStalk _ f) = f := by
  apply NatTrans.ext
  ext U
  dsimp
  split_ifs with h
  erw [← Category.assoc, colimit.ι_desc, Category.assoc, eqToHom_trans, eqToHom_refl,
    Category.comp_id]
  exact ((if_neg h).symm.ndrec terminalIsTerminal).hom_ext ..

theorem fromStalk_to_skyscraper {𝓕 : Presheaf C X} {c : C} (f : 𝓕.stalk p₀ ⟶ c) :
    fromStalk p₀ (toSkyscraperPresheaf _ f) = f :=
  colimit.hom_ext fun U => by
    erw [colimit.ι_desc]; dsimp; rw [dif_pos U.unop.2]
    rw [Category.assoc, Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id,
      Presheaf.germ]
    congr 3

/-- The unit in `Presheaf.stalkFunctor ⊣ skyscraperPresheafFunctor`
-/
@[simps]
protected def unit :
    𝟭 (Presheaf C X) ⟶ Presheaf.stalkFunctor C p₀ ⋙ skyscraperPresheafFunctor p₀ where
  app 𝓕 := toSkyscraperPresheaf _ <| 𝟙 _
  naturality 𝓕 𝓖 f := by
    ext U; dsimp
    split_ifs with h
    · simp only [Category.id_comp, ← Category.assoc]; rw [comp_eqToHom_iff]
      simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
      erw [colimit.ι_map]; rfl
    · apply ((if_neg h).symm.ndrec terminalIsTerminal).hom_ext

/-- The counit in `Presheaf.stalkFunctor ⊣ skyscraperPresheafFunctor`
-/
@[simps]
protected def counit :
    skyscraperPresheafFunctor p₀ ⋙ (Presheaf.stalkFunctor C p₀ : Presheaf C X ⥤ C) ⟶ 𝟭 C where
  app c := (skyscraperPresheafStalkOfSpecializes p₀ c specializes_rfl).hom
  naturality x y f := colimit.hom_ext fun U => by
    erw [← Category.assoc, colimit.ι_map, colimit.isoColimitCocone_ι_hom_assoc,
      skyscraperPresheafCoconeOfSpecializes_ι_app (h := specializes_rfl), Category.assoc,
      colimit.ι_desc, whiskeringLeft_obj_map, whiskerLeft_app, SkyscraperPresheafFunctor.map'_app,
      dif_pos U.unop.2, skyscraperPresheafCoconeOfSpecializes_ι_app (h := specializes_rfl),
      comp_eqToHom_iff, Category.assoc, eqToHom_comp_iff, ← Category.assoc, eqToHom_trans,
      eqToHom_refl, Category.id_comp, comp_eqToHom_iff, Category.assoc, eqToHom_trans, eqToHom_refl,
      Category.comp_id, CategoryTheory.Functor.id_map]

end StalkSkyscraperPresheafAdjunctionAuxs

section

open StalkSkyscraperPresheafAdjunctionAuxs

/-- `skyscraperPresheafFunctor` is the right adjoint of `Presheaf.stalkFunctor`
-/
def skyscraperPresheafStalkAdjunction [HasColimits C] :
    (Presheaf.stalkFunctor C p₀ : Presheaf C X ⥤ C) ⊣ skyscraperPresheafFunctor p₀ where
  homEquiv c 𝓕 :=
    { toFun := toSkyscraperPresheaf _
      invFun := fromStalk _
      left_inv := fromStalk_to_skyscraper _
      right_inv := to_skyscraper_fromStalk _ }
  unit := StalkSkyscraperPresheafAdjunctionAuxs.unit _
  counit := StalkSkyscraperPresheafAdjunctionAuxs.counit _
  homEquiv_unit {𝓕} c α := by
    ext U
    -- Porting note: `NatTrans.comp_app` is not picked up by `simp`
    rw [NatTrans.comp_app]
    simp only [Equiv.coe_fn_mk, toSkyscraperPresheaf_app, SkyscraperPresheafFunctor.map'_app,
      skyscraperPresheafFunctor_map, unit_app]
    split_ifs with h
    · erw [Category.id_comp, ← Category.assoc, comp_eqToHom_iff, Category.assoc, Category.assoc,
        Category.assoc, Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id, ←
        Category.assoc _ _ α, eqToHom_trans, eqToHom_refl, Category.id_comp]
    · apply ((if_neg h).symm.ndrec terminalIsTerminal).hom_ext
  homEquiv_counit {𝓕} c α := by
    -- Porting note: added a `dsimp`
    dsimp; ext U; simp only [Equiv.coe_fn_symm_mk, counit_app]
    erw [colimit.ι_desc, ← Category.assoc, colimit.ι_map, whiskerLeft_app, Category.assoc,
      colimit.ι_desc]
    rfl

instance [HasColimits C] : (skyscraperPresheafFunctor p₀ : C ⥤ Presheaf C X).IsRightAdjoint  :=
  (skyscraperPresheafStalkAdjunction _).isRightAdjoint

instance [HasColimits C] : (Presheaf.stalkFunctor C p₀).IsLeftAdjoint  :=
  -- Use a classical instance instead of the one from `variable`s
  have : ∀ U : Opens X, Decidable (p₀ ∈ U) := fun _ ↦ Classical.dec _
  (skyscraperPresheafStalkAdjunction _).isLeftAdjoint

/-- Taking stalks of a sheaf is the left adjoint functor to `skyscraperSheafFunctor`
-/
def stalkSkyscraperSheafAdjunction [HasColimits C] :
    Sheaf.forget C X ⋙ Presheaf.stalkFunctor _ p₀ ⊣ skyscraperSheafFunctor p₀ where
  -- Porting note (#11041): `ext1` is changed to `Sheaf.Hom.ext`,
  homEquiv 𝓕 c :=
    ⟨fun f => ⟨toSkyscraperPresheaf p₀ f⟩, fun g => fromStalk p₀ g.1, fromStalk_to_skyscraper p₀,
      fun g => Sheaf.Hom.ext _ _ <| to_skyscraper_fromStalk _ _⟩
  unit :=
    { app := fun 𝓕 => ⟨(StalkSkyscraperPresheafAdjunctionAuxs.unit p₀).app 𝓕.1⟩
      naturality := fun 𝓐 𝓑 f => Sheaf.Hom.ext _ _ <| by
        apply (StalkSkyscraperPresheafAdjunctionAuxs.unit p₀).naturality }
  counit := StalkSkyscraperPresheafAdjunctionAuxs.counit p₀
  homEquiv_unit {𝓐} c f := Sheaf.Hom.ext _ _ (skyscraperPresheafStalkAdjunction p₀).homEquiv_unit
  homEquiv_counit {𝓐} c f := (skyscraperPresheafStalkAdjunction p₀).homEquiv_counit

instance [HasColimits C] : (skyscraperSheafFunctor p₀ : C ⥤ Sheaf C X).IsRightAdjoint  :=
  (stalkSkyscraperSheafAdjunction _).isRightAdjoint

end

end
