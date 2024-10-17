/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Mario Carneiro, Johan Commelin, Amelia Livingston, Anne Baanen
-/
import Mathlib.Algebra.Algebra.Tower
import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
import Mathlib.GroupTheory.MonoidLocalization.MonoidWithZero
import Mathlib.RingTheory.OreLocalization.Ring
import Mathlib.RingTheory.Ideal.Basic
import Mathlib.RingTheory.Localization.Defs

/-!
# Localizations of commutative rings

This file contains various basic results on localizations.

We characterize the localization of a commutative ring `R` at a submonoid `M` up to
isomorphism; that is, a commutative ring `S` is the localization of `R` at `M` iff we can find a
ring homomorphism `f : R →+* S` satisfying 3 properties:
1. For all `y ∈ M`, `f y` is a unit;
2. For all `z : S`, there exists `(x, y) : R × M` such that `z * f y = f x`;
3. For all `x, y : R` such that `f x = f y`, there exists `c ∈ M` such that `x * c = y * c`.
   (The converse is a consequence of 1.)

In the following, let `R, P` be commutative rings, `S, Q` be `R`- and `P`-algebras
and `M, T` be submonoids of `R` and `P` respectively, e.g.:
```
variable (R S P Q : Type*) [CommRing R] [CommRing S] [CommRing P] [CommRing Q]
variable [Algebra R S] [Algebra P Q] (M : Submonoid R) (T : Submonoid P)
```

## Main definitions

 * `IsLocalization.algEquiv`: if `Q` is another localization of `R` at `M`, then `S` and `Q`
   are isomorphic as `R`-algebras

## Implementation notes

In maths it is natural to reason up to isomorphism, but in Lean we cannot naturally `rewrite` one
structure with an isomorphic one; one way around this is to isolate a predicate characterizing
a structure up to isomorphism, and reason about things that satisfy the predicate.

A previous version of this file used a fully bundled type of ring localization maps,
then used a type synonym `f.codomain` for `f : LocalizationMap M S` to instantiate the
`R`-algebra structure on `S`. This results in defining ad-hoc copies for everything already
defined on `S`. By making `IsLocalization` a predicate on the `algebraMap R S`,
we can ensure the localization map commutes nicely with other `algebraMap`s.

To prove most lemmas about a localization map `algebraMap R S` in this file we invoke the
corresponding proof for the underlying `CommMonoid` localization map
`IsLocalization.toLocalizationMap M S`, which can be found in `GroupTheory.MonoidLocalization`
and the namespace `Submonoid.LocalizationMap`.

To reason about the localization as a quotient type, use `mk_eq_of_mk'` and associated lemmas.
These show the quotient map `mk : R → M → Localization M` equals the surjection
`LocalizationMap.mk'` induced by the map `algebraMap : R →+* Localization M`.
The lemma `mk_eq_of_mk'` hence gives you access to the results in the rest of the file,
which are about the `LocalizationMap.mk'` induced by any localization map.

The proof that "a `CommRing` `K` which is the localization of an integral domain `R` at `R \ {0}`
is a field" is a `def` rather than an `instance`, so if you want to reason about a field of
fractions `K`, assume `[Field K]` instead of just `[CommRing K]`.

## Tags
localization, ring localization, commutative ring localization, characteristic predicate,
commutative ring, field of fractions
-/


open Function

section CommSemiring

variable {R : Type*} [CommSemiring R] {M : Submonoid R} {S : Type*} [CommSemiring S]
variable [Algebra R S] {P : Type*} [CommSemiring P]

namespace IsLocalization

section IsLocalization

variable [IsLocalization M S]

theorem mk'_mem_iff {x} {y : M} {I : Ideal S} : mk' S x y ∈ I ↔ algebraMap R S x ∈ I := by
  constructor <;> intro h
  · rw [← mk'_spec S x y, mul_comm]
    exact I.mul_mem_left ((algebraMap R S) y) h
  · rw [← mk'_spec S x y] at h
    obtain ⟨b, hb⟩ := isUnit_iff_exists_inv.1 (map_units S y)
    have := I.mul_mem_left b h
    rwa [mul_comm, mul_assoc, hb, mul_one] at this

variable {g : R →+* P} (hg : ∀ y : M, IsUnit (g y))

variable (M) in
include M in
/- This is not an instance because the submonoid `M` would become a metavariable
  in typeclass search. -/
theorem algHom_subsingleton [Algebra R P] : Subsingleton (S →ₐ[R] P) :=
  ⟨fun f g =>
    AlgHom.coe_ringHom_injective <|
      IsLocalization.ringHom_ext M <| by rw [f.comp_algebraMap, g.comp_algebraMap]⟩

/-- To show `j` and `k` agree on the whole localization, it suffices to show they agree
on the image of the base ring, if they preserve `1` and `*`. -/
protected theorem ext (j k : S → P) (hj1 : j 1 = 1) (hk1 : k 1 = 1)
    (hjm : ∀ a b, j (a * b) = j a * j b) (hkm : ∀ a b, k (a * b) = k a * k b)
    (h : ∀ a, j (algebraMap R S a) = k (algebraMap R S a)) : j = k :=
  let j' : MonoidHom S P :=
    { toFun := j, map_one' := hj1, map_mul' := hjm }
  let k' : MonoidHom S P :=
    { toFun := k, map_one' := hk1, map_mul' := hkm }
  have : j' = k' := monoidHom_ext M (MonoidHom.ext h)
  show j'.toFun = k'.toFun by rw [this]
end

variable {M}

theorem lift_unique {j : S →+* P} (hj : ∀ x, j ((algebraMap R S) x) = g x) : lift hg = j :=
  RingHom.ext <|
    (DFunLike.ext_iff (F := MonoidHom _ _)).1 <|
      Submonoid.LocalizationMap.lift_unique (toLocalizationMap M S) (g := g.toMonoidHom) hg
        (j := j.toMonoidHom) hj

@[simp]
theorem lift_id (x) : lift (map_units S : ∀ _ : M, IsUnit _) x = x :=
  (toLocalizationMap M S).lift_id _

theorem lift_surjective_iff :
    Surjective (lift hg : S → P) ↔ ∀ v : P, ∃ x : R × M, v * g x.2 = g x.1 :=
  (toLocalizationMap M S).lift_surjective_iff hg

theorem lift_injective_iff :
    Injective (lift hg : S → P) ↔ ∀ x y, algebraMap R S x = algebraMap R S y ↔ g x = g y :=
  (toLocalizationMap M S).lift_injective_iff hg

section Map

variable {T : Submonoid P} {Q : Type*} [CommSemiring Q]
variable [Algebra P Q] [IsLocalization T Q]

section

variable (Q)

/-- Map a homomorphism `g : R →+* P` to `S →+* Q`, where `S` and `Q` are
localizations of `R` and `P` at `M` and `T` respectively,
such that `g(M) ⊆ T`.

We send `z : S` to `algebraMap P Q (g x) * (algebraMap P Q (g y))⁻¹`, where
`(x, y) : R × M` are such that `z = f x * (f y)⁻¹`. -/
noncomputable def map (g : R →+* P) (hy : M ≤ T.comap g) : S →+* Q :=
  lift (M := M) (g := (algebraMap P Q).comp g) fun y => map_units _ ⟨g y, hy y.2⟩

end

section
variable (hy : M ≤ T.comap g)
include hy

-- Porting note: added `simp` attribute, since it proves very similar lemmas marked `simp`
@[simp]
theorem map_eq (x) : map Q g hy ((algebraMap R S) x) = algebraMap P Q (g x) :=
  lift_eq (fun y => map_units _ ⟨g y, hy y.2⟩) x

@[simp]
theorem map_comp : (map Q g hy).comp (algebraMap R S) = (algebraMap P Q).comp g :=
  lift_comp fun y => map_units _ ⟨g y, hy y.2⟩

theorem map_mk' (x) (y : M) : map Q g hy (mk' S x y) = mk' Q (g x) ⟨g y, hy y.2⟩ :=
  Submonoid.LocalizationMap.map_mk' (toLocalizationMap M S) (g := g.toMonoidHom)
    (fun y => hy y.2) (k := toLocalizationMap T Q) ..

theorem map_unique (j : S →+* Q) (hj : ∀ x : R, j (algebraMap R S x) = algebraMap P Q (g x)) :
    map Q g hy = j :=
  lift_unique (fun y => map_units _ ⟨g y, hy y.2⟩) hj

/-- If `CommSemiring` homs `g : R →+* P, l : P →+* A` induce maps of localizations, the composition
of the induced maps equals the map of localizations induced by `l ∘ g`. -/
theorem map_comp_map {A : Type*} [CommSemiring A] {U : Submonoid A} {W} [CommSemiring W]
    [Algebra A W] [IsLocalization U W] {l : P →+* A} (hl : T ≤ U.comap l) :
    (map W l hl).comp (map Q g hy : S →+* _) = map W (l.comp g) fun _ hx => hl (hy hx) :=
  RingHom.ext fun x =>
    Submonoid.LocalizationMap.map_map (P := P) (toLocalizationMap M S) (fun y => hy y.2)
      (toLocalizationMap U W) (fun w => hl w.2) x

/-- If `CommSemiring` homs `g : R →+* P, l : P →+* A` induce maps of localizations, the composition
of the induced maps equals the map of localizations induced by `l ∘ g`. -/
theorem map_map {A : Type*} [CommSemiring A] {U : Submonoid A} {W} [CommSemiring W] [Algebra A W]
    [IsLocalization U W] {l : P →+* A} (hl : T ≤ U.comap l) (x : S) :
    map W l hl (map Q g hy x) = map W (l.comp g) (fun _ hx => hl (hy hx)) x := by
  rw [← map_comp_map (Q := Q) hy hl]; rfl

theorem map_smul (x : S) (z : R) : map Q g hy (z • x : S) = g z • map Q g hy x := by
  rw [Algebra.smul_def, Algebra.smul_def, RingHom.map_mul, map_eq]

end

@[simp]
theorem map_id_mk' {Q : Type*} [CommSemiring Q] [Algebra R Q] [IsLocalization M Q] (x) (y : M) :
    map Q (RingHom.id R) (le_refl M) (mk' S x y) = mk' Q x y :=
  map_mk' ..

@[simp]
theorem map_id (z : S) (h : M ≤ M.comap (RingHom.id R) := le_refl M) :
    map S (RingHom.id _) h z = z :=
  lift_id _

section

variable (S Q)

/-- If `S`, `Q` are localizations of `R` and `P` at submonoids `M, T` respectively, an
isomorphism `j : R ≃+* P` such that `j(M) = T` induces an isomorphism of localizations
`S ≃+* Q`. -/
@[simps]
noncomputable def ringEquivOfRingEquiv (h : R ≃+* P) (H : M.map h.toMonoidHom = T) : S ≃+* Q :=
  have H' : T.map h.symm.toMonoidHom = M := by
    rw [← M.map_id, ← H, Submonoid.map_map]
    congr
    ext
    apply h.symm_apply_apply
  { map Q (h : R →+* P) (M.le_comap_of_map_le (le_of_eq H)) with
    toFun := map Q (h : R →+* P) (M.le_comap_of_map_le (le_of_eq H))
    invFun := map S (h.symm : P →+* R) (T.le_comap_of_map_le (le_of_eq H'))
    left_inv := fun x => by
      rw [map_map, map_unique _ (RingHom.id _), RingHom.id_apply]
      simp
    right_inv := fun x => by
      rw [map_map, map_unique _ (RingHom.id _), RingHom.id_apply]
      simp }

end

theorem ringEquivOfRingEquiv_eq_map {j : R ≃+* P} (H : M.map j.toMonoidHom = T) :
    (ringEquivOfRingEquiv S Q j H : S →+* Q) =
      map Q (j : R →+* P) (M.le_comap_of_map_le (le_of_eq H)) :=
  rfl

-- Porting note (#10618): removed `simp`, `simp` can prove it
theorem ringEquivOfRingEquiv_eq {j : R ≃+* P} (H : M.map j.toMonoidHom = T) (x) :
    ringEquivOfRingEquiv S Q j H ((algebraMap R S) x) = algebraMap P Q (j x) := by
  simp

theorem ringEquivOfRingEquiv_mk' {j : R ≃+* P} (H : M.map j.toMonoidHom = T) (x : R) (y : M) :
    ringEquivOfRingEquiv S Q j H (mk' S x y) =
      mk' Q (j x) ⟨j y, show j y ∈ T from H ▸ Set.mem_image_of_mem j y.2⟩ := by
  simp [map_mk']

end Map

section AlgEquiv

variable {Q : Type*} [CommSemiring Q] [Algebra R Q] [IsLocalization M Q]

section

variable (M S Q)

/-- If `S`, `Q` are localizations of `R` at the submonoid `M` respectively,
there is an isomorphism of localizations `S ≃ₐ[R] Q`. -/
@[simps!]
noncomputable def algEquiv : S ≃ₐ[R] Q :=
  { ringEquivOfRingEquiv S Q (RingEquiv.refl R) M.map_id with
    commutes' := ringEquivOfRingEquiv_eq _ }

end

-- Porting note (#10618): removed `simp`, `simp` can prove it
theorem algEquiv_mk' (x : R) (y : M) : algEquiv M S Q (mk' S x y) = mk' Q x y := by
  simp

-- Porting note (#10618): removed `simp`, `simp` can prove it
theorem algEquiv_symm_mk' (x : R) (y : M) : (algEquiv M S Q).symm (mk' Q x y) = mk' S x y := by simp

variable (M) in
include M in
protected lemma bijective (f : S →+* Q) (hf : f.comp (algebraMap R S) = algebraMap R Q) :
    Function.Bijective f :=
  (show f = IsLocalization.algEquiv M S Q by
    apply IsLocalization.ringHom_ext M; rw [hf]; ext; simp) ▸
    (IsLocalization.algEquiv M S Q).toEquiv.bijective

end AlgEquiv

section at_units

variable (R M)

/-- The localization at a module of units is isomorphic to the ring. -/
noncomputable def atUnits (H : M ≤ IsUnit.submonoid R) : R ≃ₐ[R] S := by
  refine AlgEquiv.ofBijective (Algebra.ofId R S) ⟨?_, ?_⟩
  · intro x y hxy
    obtain ⟨c, eq⟩ := (IsLocalization.eq_iff_exists M S).mp hxy
    obtain ⟨u, hu⟩ := H c.prop
    rwa [← hu, Units.mul_right_inj] at eq
  · intro y
    obtain ⟨⟨x, s⟩, eq⟩ := IsLocalization.surj M y
    obtain ⟨u, hu⟩ := H s.prop
    use x * u.inv
    dsimp [Algebra.ofId, RingHom.toFun_eq_coe, AlgHom.coe_mks]
    rw [RingHom.map_mul, ← eq, ← hu, mul_assoc, ← RingHom.map_mul]
    simp

end at_units

end IsLocalization

section

variable (M)

theorem isLocalization_of_algEquiv [Algebra R P] [IsLocalization M S] (h : S ≃ₐ[R] P) :
    IsLocalization M P := by
  constructor
  · intro y
    convert (IsLocalization.map_units S y).map h.toAlgHom.toRingHom.toMonoidHom
    exact (h.commutes y).symm
  · intro y
    obtain ⟨⟨x, s⟩, e⟩ := IsLocalization.surj M (h.symm y)
    apply_fun (show S → P from h) at e
    simp only [map_mul, h.apply_symm_apply, h.commutes] at e
    exact ⟨⟨x, s⟩, e⟩
  · intro x y
    rw [← h.symm.toEquiv.injective.eq_iff, ← IsLocalization.eq_iff_exists M S, ← h.symm.commutes, ←
      h.symm.commutes]
    exact id

theorem isLocalization_iff_of_algEquiv [Algebra R P] (h : S ≃ₐ[R] P) :
    IsLocalization M S ↔ IsLocalization M P :=
  ⟨fun _ => isLocalization_of_algEquiv M h, fun _ => isLocalization_of_algEquiv M h.symm⟩

theorem isLocalization_iff_of_ringEquiv (h : S ≃+* P) :
    IsLocalization M S ↔
      haveI := (h.toRingHom.comp <| algebraMap R S).toAlgebra; IsLocalization M P :=
  letI := (h.toRingHom.comp <| algebraMap R S).toAlgebra
  isLocalization_iff_of_algEquiv M { h with commutes' := fun _ => rfl }

end

variable (M)

/-- If `S₁` is the localization of `R` at `M₁` and `S₂` is the localization of
`R` at `M₂`, then every localization `T` of `S₂` at `M₁` is also a localization of
`S₁` at `M₂`, in other words `M₁⁻¹M₂⁻¹R` can be identified with `M₂⁻¹M₁⁻¹R`. -/
lemma commutes (S₁ S₂ T : Type*) [CommSemiring S₁]
    [CommSemiring S₂] [CommSemiring T] [Algebra R S₁] [Algebra R S₂] [Algebra R T] [Algebra S₁ T]
    [Algebra S₂ T] [IsScalarTower R S₁ T] [IsScalarTower R S₂ T] (M₁ M₂ : Submonoid R)
    [IsLocalization M₁ S₁] [IsLocalization M₂ S₂]
    [IsLocalization (Algebra.algebraMapSubmonoid S₂ M₁) T] :
    IsLocalization (Algebra.algebraMapSubmonoid S₁ M₂) T where
  map_units' := by
    rintro ⟨m, ⟨a, ha, rfl⟩⟩
    rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply R S₂ T]
    exact IsUnit.map _ (IsLocalization.map_units' ⟨a, ha⟩)
  surj' a := by
    obtain ⟨⟨y, -, m, hm, rfl⟩, hy⟩ := surj (M := Algebra.algebraMapSubmonoid S₂ M₁) a
    rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply R S₁ T] at hy
    obtain ⟨⟨z, n, hn⟩, hz⟩ := IsLocalization.surj (M := M₂) y
    have hunit : IsUnit (algebraMap R S₁ m) := map_units' ⟨m, hm⟩
    use ⟨algebraMap R S₁ z * hunit.unit⁻¹, ⟨algebraMap R S₁ n, n, hn, rfl⟩⟩
    rw [map_mul, ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply R S₂ T]
    conv_rhs => rw [← IsScalarTower.algebraMap_apply]
    rw [IsScalarTower.algebraMap_apply R S₂ T, ← hz, map_mul, ← hy]
    convert_to _ = a * (algebraMap S₂ T) ((algebraMap R S₂) n) *
        (algebraMap S₁ T) (((algebraMap R S₁) m) * hunit.unit⁻¹.val)
    · rw [map_mul]
      ring
    simp
  exists_of_eq {x y} hxy := by
    obtain ⟨r, s, d, hr, hs⟩ := IsLocalization.surj₂ M₁ S₁ x y
    apply_fun (· * algebraMap S₁ T (algebraMap R S₁ d)) at hxy
    simp_rw [← map_mul, hr, hs, ← IsScalarTower.algebraMap_apply,
      IsScalarTower.algebraMap_apply R S₂ T] at hxy
    obtain ⟨⟨-, c, hmc, rfl⟩, hc⟩ := exists_of_eq (M := Algebra.algebraMapSubmonoid S₂ M₁) hxy
    simp_rw [← map_mul] at hc
    obtain ⟨a, ha⟩ := IsLocalization.exists_of_eq (M := M₂) hc
    use ⟨algebraMap R S₁ a, a, a.property, rfl⟩
    apply (map_units S₁ d).mul_right_cancel
    rw [mul_assoc, hr, mul_assoc, hs]
    apply (map_units S₁ ⟨c, hmc⟩).mul_right_cancel
    rw [← map_mul, ← map_mul, mul_assoc, mul_comm _ c, ha, map_mul, map_mul]
    ring

end IsLocalization

namespace Localization

open IsLocalization

theorem mk_natCast (m : ℕ) : (mk m 1 : Localization M) = m := by
  simpa using mk_algebraMap (R := R) (A := ℕ) _

@[deprecated (since := "2024-04-17")]
alias mk_nat_cast := mk_natCast

variable [IsLocalization M S]

section

variable (S) (M)

/-- The localization of `R` at `M` as a quotient type is isomorphic to any other localization. -/
@[simps!]
noncomputable def algEquiv : Localization M ≃ₐ[R] S :=
  IsLocalization.algEquiv M _ _

/-- The localization of a singleton is a singleton. Cannot be an instance due to metavariables. -/
noncomputable def _root_.IsLocalization.unique (R Rₘ) [CommSemiring R] [CommSemiring Rₘ]
    (M : Submonoid R) [Subsingleton R] [Algebra R Rₘ] [IsLocalization M Rₘ] : Unique Rₘ :=
  have : Inhabited Rₘ := ⟨1⟩
  (algEquiv M Rₘ).symm.injective.unique

end

-- Porting note (#10618): removed `simp`, `simp` can prove it
nonrec theorem algEquiv_mk' (x : R) (y : M) : algEquiv M S (mk' (Localization M) x y) = mk' S x y :=
  algEquiv_mk' _ _

-- Porting note (#10618): removed `simp`, `simp` can prove it
nonrec theorem algEquiv_symm_mk' (x : R) (y : M) :
    (algEquiv M S).symm (mk' S x y) = mk' (Localization M) x y :=
  algEquiv_symm_mk' _ _

theorem algEquiv_mk (x y) : algEquiv M S (mk x y) = mk' S x y := by rw [mk_eq_mk', algEquiv_mk']

theorem algEquiv_symm_mk (x : R) (y : M) : (algEquiv M S).symm (mk' S x y) = mk x y := by
  rw [mk_eq_mk', algEquiv_symm_mk']

lemma coe_algEquiv :
    (Localization.algEquiv M S : Localization M →+* S) =
    IsLocalization.map (M := M) (T := M) _ (RingHom.id R) le_rfl := rfl

lemma coe_algEquiv_symm :
    ((Localization.algEquiv M S).symm : S →+* Localization M) =
    IsLocalization.map (M := M) (T := M) _ (RingHom.id R) le_rfl := rfl

end Localization

end CommSemiring

section CommRing

variable {R : Type*} [CommRing R] {M : Submonoid R} (S : Type*) [CommRing S]
variable [Algebra R S] {P : Type*} [CommRing P]

namespace Localization

theorem mk_intCast (m : ℤ) : (mk m 1 : Localization M) = m := by
  simpa using mk_algebraMap (R := R) (A := ℤ) _

@[deprecated (since := "2024-04-17")]
alias mk_int_cast := mk_intCast

end Localization

open IsLocalization

/-- If `R` is a field, then localizing at a submonoid not containing `0` adds no new elements. -/
theorem IsField.localization_map_bijective {R Rₘ : Type*} [CommRing R] [CommRing Rₘ]
    {M : Submonoid R} (hM : (0 : R) ∉ M) (hR : IsField R) [Algebra R Rₘ] [IsLocalization M Rₘ] :
    Function.Bijective (algebraMap R Rₘ) := by
  letI := hR.toField
  replace hM := le_nonZeroDivisors_of_noZeroDivisors hM
  refine ⟨IsLocalization.injective _ hM, fun x => ?_⟩
  obtain ⟨r, ⟨m, hm⟩, rfl⟩ := mk'_surjective M x
  obtain ⟨n, hn⟩ := hR.mul_inv_cancel (nonZeroDivisors.ne_zero <| hM hm)
  exact ⟨r * n, by rw [eq_mk'_iff_mul_eq, ← map_mul, mul_assoc, _root_.mul_comm n, hn, mul_one]⟩

/-- If `R` is a field, then localizing at a submonoid not containing `0` adds no new elements. -/
theorem Field.localization_map_bijective {K Kₘ : Type*} [Field K] [CommRing Kₘ] {M : Submonoid K}
    (hM : (0 : K) ∉ M) [Algebra K Kₘ] [IsLocalization M Kₘ] :
    Function.Bijective (algebraMap K Kₘ) :=
  (Field.toIsField K).localization_map_bijective hM

-- this looks weird due to the `letI` inside the above lemma, but trying to do it the other
-- way round causes issues with defeq of instances, so this is actually easier.
section Algebra

variable {S} {Rₘ Sₘ : Type*} [CommRing Rₘ] [CommRing Sₘ]
variable [Algebra R Rₘ] [IsLocalization M Rₘ]
variable [Algebra S Sₘ] [i : IsLocalization (Algebra.algebraMapSubmonoid S M) Sₘ]
include S
section

variable (S M)

/-- Definition of the natural algebra induced by the localization of an algebra.
Given an algebra `R → S`, a submonoid `R` of `M`, and a localization `Rₘ` for `M`,
let `Sₘ` be the localization of `S` to the image of `M` under `algebraMap R S`.
Then this is the natural algebra structure on `Rₘ → Sₘ`, such that the entire square commutes,
where `localization_map.map_comp` gives the commutativity of the underlying maps.

This instance can be helpful if you define `Sₘ := Localization (Algebra.algebraMapSubmonoid S M)`,
however we will instead use the hypotheses `[Algebra Rₘ Sₘ] [IsScalarTower R Rₘ Sₘ]` in lemmas
since the algebra structure may arise in different ways.
-/
noncomputable def localizationAlgebra : Algebra Rₘ Sₘ :=
  (map Sₘ (algebraMap R S)
        (show _ ≤ (Algebra.algebraMapSubmonoid S M).comap _ from M.le_comap_map) :
      Rₘ →+* Sₘ).toAlgebra

end

section

variable [Algebra Rₘ Sₘ] [Algebra R Sₘ] [IsScalarTower R Rₘ Sₘ] [IsScalarTower R S Sₘ]
variable (S Rₘ Sₘ)

theorem IsLocalization.map_units_map_submonoid (y : M) : IsUnit (algebraMap R Sₘ y) := by
  rw [IsScalarTower.algebraMap_apply _ S]
  exact IsLocalization.map_units Sₘ ⟨algebraMap R S y, Algebra.mem_algebraMapSubmonoid_of_mem y⟩

-- can't be simp, as `S` only appears on the RHS
theorem IsLocalization.algebraMap_mk' (x : R) (y : M) :
    algebraMap Rₘ Sₘ (IsLocalization.mk' Rₘ x y) =
      IsLocalization.mk' Sₘ (algebraMap R S x)
        ⟨algebraMap R S y, Algebra.mem_algebraMapSubmonoid_of_mem y⟩ := by
  rw [IsLocalization.eq_mk'_iff_mul_eq, Subtype.coe_mk, ← IsScalarTower.algebraMap_apply, ←
    IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply R Rₘ Sₘ,
    IsScalarTower.algebraMap_apply R Rₘ Sₘ, ← _root_.map_mul, mul_comm,
    IsLocalization.mul_mk'_eq_mk'_of_mul]
  exact congr_arg (algebraMap Rₘ Sₘ) (IsLocalization.mk'_mul_cancel_left x y)

variable (M)

/-- If the square below commutes, the bottom map is uniquely specified:
```
R  →  S
↓     ↓
Rₘ → Sₘ
```
-/
theorem IsLocalization.algebraMap_eq_map_map_submonoid :
    algebraMap Rₘ Sₘ =
      map Sₘ (algebraMap R S)
        (show _ ≤ (Algebra.algebraMapSubmonoid S M).comap _ from M.le_comap_map) :=
  Eq.symm <|
    IsLocalization.map_unique _ (algebraMap Rₘ Sₘ) fun x => by
      rw [← IsScalarTower.algebraMap_apply R S Sₘ, ← IsScalarTower.algebraMap_apply R Rₘ Sₘ]

/-- If the square below commutes, the bottom map is uniquely specified:
```
R  →  S
↓     ↓
Rₘ → Sₘ
```
-/
theorem IsLocalization.algebraMap_apply_eq_map_map_submonoid (x) :
    algebraMap Rₘ Sₘ x =
      map Sₘ (algebraMap R S)
        (show _ ≤ (Algebra.algebraMapSubmonoid S M).comap _ from M.le_comap_map) x :=
  DFunLike.congr_fun (IsLocalization.algebraMap_eq_map_map_submonoid _ _ _ _) x

theorem IsLocalization.lift_algebraMap_eq_algebraMap :
    IsLocalization.lift (M := M) (IsLocalization.map_units_map_submonoid S Sₘ) =
      algebraMap Rₘ Sₘ :=
  IsLocalization.lift_unique _ fun _ => (IsScalarTower.algebraMap_apply _ _ _ _).symm

end

variable (Rₘ Sₘ)

/-- Injectivity of the underlying `algebraMap` descends to the algebra induced by localization. -/
theorem localizationAlgebra_injective (hRS : Function.Injective (algebraMap R S)) :
    Function.Injective (@algebraMap Rₘ Sₘ _ _ (localizationAlgebra M S)) :=
  have : IsLocalization (M.map (algebraMap R S)) Sₘ := i
  IsLocalization.map_injective_of_injective _ _ _ hRS

end Algebra

end CommRing
