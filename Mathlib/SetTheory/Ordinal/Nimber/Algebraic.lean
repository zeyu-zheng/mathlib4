/-
Copyright (c) 2024 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios, Daniel Weber
-/

import Mathlib.Data.Finsupp.WellFounded
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.SetTheory.Ordinal.Nimber.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Algebra.CharP.Subring

universe u v

open Function Order Ordinal Polynomial Set

noncomputable section

-- Not all needed, but still could be PR'd.
section MissingPolynomialStuff

variable {R : Type*} [Semiring R]

@[simp]
theorem coeffs_zero : coeffs (0 : R[X]) = ∅ := by
  simp

@[simp]
theorem coeff_monomial_same (n : ℕ) {c : R} : (monomial n c).coeff n = c :=
  Finsupp.single_eq_same

theorem coeffs_monomial (n : ℕ) {c : R} (hc : c ≠ 0) : (monomial n c).coeffs = {c} := by
  rw [coeffs, support_monomial n hc]
  simp

theorem X_ne_C [Nontrivial R] (c : R) : X ≠ C c := by
  intro h
  apply_fun natDegree at h
  simp at h

theorem coeff_X_mem (R : Type*) [Semiring R] (n : ℕ) :
    coeff (X : R[X]) n = 0 ∨ coeff (X : R[X]) n = 1 := by
  rw [coeff_X]
  obtain rfl | hn := eq_or_ne 1 n
  · simp
  · simp [hn]

variable {F : Type*} [Field F]

theorem Irreducible.degree_pos {f : Polynomial F} (h : Irreducible f) :
    0 < f.degree :=
  natDegree_pos_iff_degree_pos.1 h.natDegree_pos

end MissingPolynomialStuff

section MissingOrdinalStuff

protected theorem Ordinal.csSup_le_csSup {s t : Set Ordinal} (ht : BddAbove t) (h : s ⊆ t) :
    sSup s ≤ sSup t := by
  obtain rfl | hs := Set.eq_empty_or_nonempty s
  · simp
  · exact csSup_le_csSup ht hs h

theorem Ordinal.sSup_empty : sSup (∅ : Set Ordinal) = 0 :=
  csSup_empty

theorem Ordinal.sSup_eq_zero {s : Set Ordinal} (hs : BddAbove s) : sSup s = 0 ↔ s ⊆ {0} := by
  constructor
  · intro h a ha
    have := le_csSup hs ha
    rw [h, Ordinal.le_zero] at this
    exact this
  · intro hs'
    rw [← Ordinal.le_zero]
    apply csSup_le'
    intro a ha
    rw [Ordinal.le_zero]
    rw [Set.subset_singleton_iff] at hs'
    exact hs' a ha

/-- The zero element on `o.toType` is the bottom element. -/
def zero_toType {o : Ordinal} (ho : o ≠ 0) : Zero o.toType :=
  ⟨enumIsoToType o ⟨0, Ordinal.pos_iff_ne_zero.2 ho⟩⟩

end MissingOrdinalStuff

instance (o : Nimber.{u}) : Small.{u} (Iio o) :=
  inferInstanceAs (Small.{u} (Iio (Nimber.toOrdinal o)))

-- I'll PR this soon.
attribute [-simp] enumIsoToType_apply

namespace Nimber

instance : CharP Nimber 2 where
  cast_eq_zero_iff' x := by
    rcases Nat.even_or_odd x with ⟨r, rfl⟩ | ⟨r, rfl⟩
    · simp only [Nat.cast_add, add_self, true_iff]
      omega
    · simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one, add_eq_zero_iff,
      Nat.not_two_dvd_bit1, iff_false]
      simp only [two_mul, add_self, zero_ne_one, not_false_eq_true]

/-- Add nimbers as ordinals. We introduce the notation `a +ₒ b` for this. -/
abbrev ordinalAdd (a b : Nimber) : Nimber := toNimber (toOrdinal a + toOrdinal b)
/-- Multiply nimbers as ordinals. We introduce the notation `a *ₒ b` for this. -/
abbrev ordinalMul (a b : Nimber) : Nimber := toNimber (toOrdinal a * toOrdinal b)
/-- Divide nimbers as ordinals. We introduce the notation `a /ₒ b` for this. -/
abbrev ordinalDiv (a b : Nimber) : Nimber := toNimber (toOrdinal a / toOrdinal b)
/-- Take moduli of nimbers as ordinals. We introduce the notation `a %ₒ b` for this. -/
abbrev ordinalMod (a b : Nimber) : Nimber := toNimber (toOrdinal a % toOrdinal b)
/-- Exponent of nimbers as ordinals. We introduce the notation `a ^ₒ b` for this. -/
abbrev ordinalPow (a : Nimber) (b : ℕ) : Nimber := toNimber (toOrdinal a ^ b)

local infixl:65 " +ₒ " => ordinalAdd
local infixl:70 " *ₒ " => ordinalMul
local infixl:70 " /ₒ " => ordinalDiv
local infixl:70 " %ₒ " => ordinalMod
local infixr:80 " ^ₒ " => ordinalPow

lemma lt_ordinalAdd_iff (a b c : Nimber) : a < b +ₒ c ↔ a < b ∨ ∃ d < c, b +ₒ d = a :=
  lt_add_iff a b c

lemma ordinalDiv_ordinalAdd_ordinalMod (a b : Nimber) : b *ₒ (a /ₒ b) +ₒ a %ₒ b = a :=
  div_add_mod a b

lemma ordinalMod_lt (a : Nimber) {b : Nimber} (hb : b ≠ 0) : a %ₒ b < b :=
  Ordinal.mod_lt a hb

@[simp]
lemma ordinalPow_zero (a : Nimber) : a ^ₒ 0 = 1 := by simp

@[simp]
lemma one_ordinalMul (a : Nimber) : 1 *ₒ a = a := by simp [ordinalMul]

@[simp]
lemma ordinalMul_one (a : Nimber) : a *ₒ 1 = a := by simp [ordinalMul]

theorem ordinalDiv_lt {a b c : Nimber} (b0 : b ≠ 0) : a /ₒ b < c ↔ a < b *ₒ c :=
  Ordinal.div_lt b0

/-- We consider a nimber to be a group when nimbers less than it are closed under addition. Note we
don't actually require `0 < x`. -/
structure IsGroup (x : Nimber) : Prop :=
  add_lt : ∀ y < x, ∀ z < x, y + z < x

@[simp]
lemma IsGroup_one : IsGroup 1 := by constructor; intro _ _ _ _; simp_all [lt_one_iff_zero]

/-- We consider a nimber to be a ring when it is a group, and nimbers less than it are closed under
multiplication. -/
structure IsRing (x : Nimber) extends IsGroup x : Prop :=
  mul_lt : ∀ y < x, ∀ z < x, y * z < x

/-- We consider a nimber to be a prefield when it is a ring, and nimbers less than it are closed
under inverses. -/
structure IsPrefield (x : Nimber) extends IsRing x : Prop :=
  inv_lt : ∀ y < x, y⁻¹ < x

/-- We consider a nimber to be a field when it is a prefield which contains 0 and 1. -/
structure IsField (x : Nimber) extends IsPrefield x : Prop :=
  one_lt : 1 < x

theorem IsField.ne_zero {x : Nimber} (hx : IsField x) : x ≠ 0 :=
  fun h => zero_lt_one.asymm (h ▸ hx.one_lt)

def IsField.toSubfield {x : Nimber} (hx : IsField x) : Subfield Nimber where
  carrier := Set.Iio x
  mul_mem' {a b} (ha hb) := hx.mul_lt a ha b hb
  add_mem' {a b} (ha hb) := hx.add_lt a ha b hb
  inv_mem' := hx.inv_lt
  one_mem' := hx.one_lt
  zero_mem' := zero_lt_one.trans hx.one_lt
  neg_mem' := id

@[simp]
lemma algebraMap_subfield {α : Type*} [Field α] {f : Subfield α} (x : f) :
    algebraMap f α x = x :=
  rfl

/-- The smallest nimber containing all additions of nimbers less than `x`. -/
def addify (x : Nimber.{u}) : Nimber.{u} :=
  ⨆ p : Iio x × Iio x, succ (p.1 + p.2)

theorem bddAbove_addify (x : Nimber.{u}) :
    BddAbove (range fun p : Iio x × Iio x => succ (p.1.1 + p.2)) :=
  bddAbove_of_small _

lemma mem_addify {x y z : Nimber} (hy : y < x) (hz : z < x) : y + z < x.addify := by
  rw [← succ_le_iff]
  exact le_ciSup (bddAbove_addify _) (⟨y, hy⟩, ⟨z, hz⟩)

theorem addify_mono : Monotone addify := by
  intro x y h
  apply Ordinal.csSup_le_csSup (bddAbove_addify _)
  rintro a ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, rfl⟩
  simpa using ⟨a, ha.trans_le h, b, hb.trans_le h, rfl⟩

/-- The smallest nimber containing all products of nimbers less than `x`. -/
def mulify (x : Nimber.{u}) : Nimber.{u} :=
  ⨆ p : Iio x × Iio x, succ (p.1 * p.2)

theorem bddAbove_mulify (x : Nimber.{u}) :
    BddAbove (range fun p : Iio x × Iio x => succ (p.1.1 * p.2)) :=
  bddAbove_of_small _

lemma mem_mulify {x y z : Nimber} (hy : y < x) (hz : z < x) : y * z < x.mulify := by
  rw [← succ_le_iff]
  exact le_ciSup (bddAbove_mulify _) (⟨y, hy⟩, ⟨z, hz⟩)

theorem mulify_mono : Monotone mulify := by
  intro x y h
  apply Ordinal.csSup_le_csSup (bddAbove_mulify _)
  rintro a ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, rfl⟩
  simpa using ⟨a, ha.trans_le h, b, hb.trans_le h, rfl⟩

/-- The smallest nimber containing all inverses of nimbers less than `x`. -/
def invify (x : Nimber.{u}) : Nimber.{u} :=
  ⨆ a : Iio x, succ (a⁻¹)

theorem bddAbove_invify (x : Nimber.{u}) :
    BddAbove (range fun a : Iio x  => succ (a.1⁻¹)) :=
  bddAbove_of_small _

lemma mem_invify {x y : Nimber} (hy : y < x) : y⁻¹ < x.invify := by
  rw [← succ_le_iff, invify]
  exact le_ciSup (bddAbove_invify _) ⟨y, hy⟩

theorem invify_mono : Monotone invify := by
  intro x y h
  apply Ordinal.csSup_le_csSup (bddAbove_invify _)
  rintro a ⟨⟨a, ha⟩, rfl⟩
  simpa using ⟨a, ha.trans_le h, rfl⟩

/-- The smallest nimber containing all the roots of polynomials with coefficients less than `x`. -/
def algify (x : Nimber.{u}) : Nimber.{u} :=
  ⨆ p : {p : Polynomial Nimber // ∀ c ∈ p.coeffs, c < x},
    succ (p.1.roots.toFinset.max.recOn 0 id)

open Classical in
/-- Enumerates the polynomials in the definition of `algify x` by a type in the same universe. -/
def algify_enum {x : Nimber.{u}} (hx : x ≠ 0) (f : ℕ → (toOrdinal x).toType) : Nimber.{u}[X] :=
  let H : Zero (toOrdinal x).toType := zero_toType hx
  if hf : (Function.support f).Finite then Polynomial.ofFinsupp <| Finsupp.mk
    hf.toFinset
    (fun n => toNimber <| (enumIsoToType _).symm (f n))
    (by
      have : toNimber ((enumIsoToType _).symm H.zero) = 0 :=
        Subtype.ext_iff.1 <| (enumIsoToType _).symm_apply_apply _
      dsimp
      rw [← this]
      intro a
      simp [← Subtype.ext_iff]
      rfl
    )
  else 0

instance small_algify (x : Nimber.{u}) :
    Small.{u} {p : Polynomial Nimber.{u} // ∀ c ∈ p.coeffs, c < x} := by
  obtain rfl | hx := eq_or_ne x 0
  · simp_rw [Nimber.not_lt_zero, imp_false, ← Finset.eq_empty_iff_forall_not_mem, coeffs_eq_empty]
    exact small_subsingleton _
  · apply small_subset (s := Set.range <| algify_enum hx)
    intro p (hp : ∀ c ∈ p.coeffs, _)
    let H : Zero (toOrdinal x).toType := zero_toType hx
    use Finsupp.mk
      p.support
      (fun n => enumIsoToType _ ⟨toOrdinal <| p.coeff n, by
        obtain hn | hn := eq_or_ne (p.coeff n) 0
        · rw [hn]
          exact Nimber.pos_iff_ne_zero.2 hx
        · exact hp _ <| coeff_mem_coeffs p n hn
      ⟩)
      (by
        intro a
        change _ ↔ _ ≠ enumIsoToType (toOrdinal x) _
        simp
      )
    ext
    simp_rw [algify_enum, Finsupp.finite_support]
    simp

/-- The function in the definition of `algify` has a range bounded above. -/
lemma bddAbove_algify (x : Nimber) : BddAbove <| Set.range
    fun p : {p : Polynomial Nimber // ∀ c ∈ p.coeffs, c < x} =>
      (succ (p.1.roots.toFinset.max.recOn 0 id) : Nimber) :=
  bddAbove_of_small _

lemma mem_algify {x y : Nimber} {p : Nimber[X]}
    (hp : ∀ c ∈ p.coeffs, c < x) (hy : y ∈ p.roots) : y < x.algify := by
  rw [← succ_le_iff]
  have : succ y ≤ succ (p.roots.toFinset.max.recOn 0 id) := by
    rw [succ_le_succ_iff]
    rw [← Multiset.mem_toFinset] at hy
    obtain ⟨m, hm⟩ := Finset.max_of_mem hy
    rw [hm]
    change y ≤ m
    rw [← WithBot.coe_le_coe, ← hm]
    exact Finset.le_max hy
  exact this.trans <| le_ciSup (bddAbove_algify x) ⟨p, hp⟩

theorem self_le_algify {x : Nimber} : x ≤ algify x := by
  obtain hx' | hx' := le_or_lt x 1
  · rw [le_one_iff] at hx'
    obtain rfl | rfl := hx'
    · exact Nimber.zero_le _
    · rw [algify]
      convert le_ciSup (bddAbove_algify 1) ⟨0, by simp⟩
      simp
      exact succ_zero.symm
  · apply le_of_forall_lt
    intro c hc
    apply mem_algify (p := X + C c)
    · intro a ha
      rw [coeffs] at ha
      simp only [coeff_add, Finset.mem_image, mem_support_iff, ne_eq, add_eq_zero_iff] at ha
      obtain ⟨n, hn₁, hn₂⟩ := ha
      cases n with
      | zero =>
        simp at hn₂
        rwa [← hn₂]
      | succ n =>
        simp at hn₂
        obtain hX | hX := coeff_X_mem Nimber (n + 1) <;>
        rw [hX] at hn₂ <;>
        rw [← hn₂]
        · exact zero_lt_one.trans hx'
        · exact hx'
    · simp
      rw [← add_left_inj (C c), add_assoc, ← C_add, add_self, map_zero, add_zero, zero_add]
      exact X_ne_C c

theorem algify_mono : Monotone algify := by
  intro x y h
  rw [algify, algify]
  apply Ordinal.csSup_le_csSup (bddAbove_algify _)
  rintro a ⟨p, rfl⟩
  have : ∀ c ∈ p.1.coeffs, c < y := by
    intro c hc
    exact (p.2 c hc).trans_le h
  simp
  use p.1

/-- The smallest nimber containing all sums, products, and inverses of nimbers less than `x`, as
well as roots of polynomials with coefficients less than `x`. -/
@[reducible]
def fieldify (x : Nimber) : Nimber :=
  x ⊔ addify x ⊔ mulify x ⊔ invify x ⊔ algify x

lemma le_fieldify (x : Nimber) : x ≤ fieldify x := by simp

lemma add_mem_fieldify {x y z : Nimber} (hy : y < x) (hz : z < x) : y + z < x.fieldify :=
  (mem_addify hy hz).trans_le (by simp)

lemma mul_mem_fieldify {x y z : Nimber} (hy : y < x) (hz : z < x) : y * z < x.fieldify :=
  (mem_mulify hy hz).trans_le (by simp)

lemma inv_mem_fieldify {x y : Nimber} (hy : y < x) : y⁻¹ < x.fieldify :=
  (mem_invify hy).trans_le (by simp)

lemma root_mem_fieldify {x y : Nimber} {p : Nimber[X]}
    (hp : ∀ c ∈ p.coeffs, c < x) (hy : y ∈ p.roots) : y < x.fieldify :=
  (mem_algify hp hy).trans_le (by simp)

/-- The next fixed point of the `fieldify` function, which is the smallest field containing `x`, as
well as all the roots for the polynomials within it. This will be an algebraically closed field,
though we don't know it yet. -/
def nextField (x : Nimber) : Nimber :=
  nfp fieldify x

lemma isPrefield_nextField (x : Nimber) : IsPrefield (nextField x) := by
  refine ⟨⟨⟨?_⟩, ?_⟩, ?_⟩
  iterate 2 {
    intro y hy z hz
    rw [nextField, lt_nfp] at *
    obtain ⟨yi, hy⟩ := hy
    obtain ⟨zi, hz⟩ := hz
    replace hy := hy.trans_le (monotone_iterate_of_id_le le_fieldify (le_max_left yi zi) x)
    replace hz := hz.trans_le (monotone_iterate_of_id_le le_fieldify (le_max_right yi zi) x)
    use max yi zi + 1
    rw [iterate_succ']
    try exact add_mem_fieldify hy hz
    try exact mul_mem_fieldify hy hz
  }
  intro y hy
  rw [nextField, lt_nfp] at *
  obtain ⟨yi, hy⟩ := hy
  use yi + 1
  rw [iterate_succ']
  exact inv_mem_fieldify hy

lemma isField_nextField {x : Nimber} (hx : 1 < x) : IsField (nextField x) :=
  ⟨isPrefield_nextField x, hx.trans_le (le_nfp _ _)⟩

theorem fieldify_mono : Monotone fieldify := by
  intro x y h
  apply_rules [sup_le_sup]
  · exact addify_mono h
  · exact mulify_mono h
  · exact invify_mono h
  · exact algify_mono h

lemma root_mem_nextField {x y : Nimber} {p : Nimber[X]}
    (hp : ∀ c ∈ p.coeffs, c < nextField x) (hy : y ∈ p.roots) : y < nextField x := by
  -- Why can't simp_rw do this the other way around?
  have : ∀ c ∈ p.coeffs, ∃ n : ℕ, c < fieldify^[n] x := by
    simp_rw [← lt_nfp]
    exact hp
  choose f hf using this
  rw [nextField, lt_nfp]
  let s := p.coeffs.attach.image (fun x => f x.1 x.2)
  have hs : s.Nonempty := by simpa [s] using ne_zero_of_mem_roots hy
  use (s.max' hs).succ
  rw [iterate_succ_apply']
  apply root_mem_fieldify _ hy
  intro c hc
  apply (hf c hc).trans_le <| fieldify_mono.monotone_iterate_of_le_map (le_fieldify _) <|
    Finset.le_max' _ _ _
  simpa [s] using ⟨c, hc, rfl⟩

lemma one_lt_two : (1 : Nimber) < toNimber 2 := by
  change (1 : Ordinal) < (2 : Ordinal)
  norm_cast

/-- The nimbers that form fields are a proper class. -/
-- Lemma 3
lemma unbounded_isField : Set.Unbounded (· < ·) {x | IsField x} := by
  intro x
  refine ⟨nextField (max (toNimber 2) x), isField_nextField (lt_max_of_lt_left one_lt_two), ?_⟩
  rw [not_lt]
  exact (le_max_right _ x).trans (le_nfp _ _)

-- Lemma 1
lemma ordinalMul_add_of_isGroup {x z : Nimber} (hx : IsGroup x) (y : Nimber) (hz : z < x) :
    x *ₒ y + z = x *ₒ y +ₒ z := by
  have xne : x ≠ 0 := fun nh ↦ Nimber.not_lt_zero _ <| nh ▸ hz
  have add_lt_of_lt (w : Nimber) (h : w < x *ₒ y) : w + z < x *ₒ y := by
    have h₁ : w /ₒ x < y := (div_lt xne).mpr h
    have h₂ : w %ₒ x < x := mod_lt w xne
    have h₃ : w %ₒ x + z < x := hx.add_lt _ h₂ z hz
    rw [← ordinalDiv_ordinalAdd_ordinalMod w x, ← ordinalMul_add_of_isGroup hx _ h₂, add_assoc,
      ordinalMul_add_of_isGroup hx _ h₃]
    apply lt_of_lt_of_le
    · rwa [OrderIso.lt_iff_lt, add_lt_add_iff_left, OrderIso.lt_iff_lt]
    · simp only [toNimber_toOrdinal, map_le_map_iff]
      rwa [← mul_succ, mul_le_mul_iff_left, succ_le_iff]
      rwa [Ordinal.pos_iff_ne_zero, ne_eq, toOrdinal_eq_zero]
  rw [add_def]
  trans sInf {w | w < x *ₒ y +ₒ z}ᶜ
  · congr! with w
    rw [lt_ordinalAdd_iff]
    congr! 3 with d
    · simp_rw [add_eq_iff_eq_add, exists_eq_right]
      constructor
      · convert add_lt_of_lt (w + z)
        rw [add_assoc, add_self, add_zero]
      · exact add_lt_of_lt _
    · rw [and_congr_right_iff]
      intro hd
      congr! 1
      exact ordinalMul_add_of_isGroup hx _ (hd.trans hz)
  · simp [Set.Iio_def]
termination_by (y, z)

lemma degree_erase_lt_of_degree_le {R : Type u} [Semiring R] (p : Polynomial R) {n : ℕ}
    (hp : p.degree ≤ n) : (p.erase n).degree < n := by
  rcases lt_or_eq_of_le hp with hp | hp
  · exact (degree_erase_le _ _).trans_lt hp
  · rw [← hp, ← natDegree_eq_of_degree_eq_some hp]
    apply Polynomial.degree_erase_lt
    intro nh
    simp [nh] at hp

lemma degree_C_mul_le {R : Type u} [Semiring R] (p : Polynomial R) (x : R) :
    (C x * p).degree ≤ p.degree := calc
  (C x * p).degree ≤ (C x).degree + p.degree := degree_mul_le (C x) p
  _ ≤ 0 + p.degree := add_le_add_right degree_C_le p.degree
  _ = p.degree := zero_add _

private lemma pow_excluded_eq_aeval {x : Nimber} {n : ℕ} (hx : x.IsField)
    (h : ∀ p : hx.toSubfield[X], 0 < p.degree → p.degree ≤ ↑n → ∃ y, p.IsRoot y) {m : ℕ}
    (hm : m + 1 ≤ n)
    (psl2 : ∀ p : hx.toSubfield[X], p.degree < ↑m → aeval x p < x ^ₒ m)
    (psl4 : x ^ m = x ^ₒ m)
    (p : hx.toSubfield[X]) (pd : p.degree < m + 1) :
    ∃ a' < x ^ m, ∃ b' < x, a' * x + x ^ m * b' + a' * b' = aeval x p := by
  have : CharP hx.toSubfield 2 := inferInstance
  let f := X ^ (m + 1) + p
  have pf : p = f + X ^ (m + 1) := by
    rw [add_assoc, add_comm, add_assoc, CharTwo.add_self_eq_zero, add_zero]
  have xd : ((X : hx.toSubfield[X]) ^ (m + 1)).degree = m + 1 := by simp
  have fdeg : f.degree = m + 1 := by
    rwa [degree_add_eq_left_of_degree_lt]
    rwa [xd]
  have fmonic : f.Monic := by
    apply Monic.add_of_left (monic_X_pow _)
    rwa [xd]
  obtain ⟨r, hr⟩ := h f (by rw [fdeg]; exact_mod_cast Nat.succ_pos m)
    (by rw [fdeg]; exact_mod_cast hm)
  rw [← mul_div_eq_iff_isRoot] at hr
  generalize hg : f / (X - C r) = g at hr
  have hdeg : (X - C r).degree ≤ f.degree := by
    rw [degree_X_sub_C, fdeg]
    exact_mod_cast self_le_add_left 1 m
  have gmonic : g.Monic := by
    rwa [← hg, Monic.def, leadingCoeff_div hdeg, leadingCoeff_X_sub_C, Monic.leadingCoeff,
      _root_.div_one]
  have gdeg : g.degree = m := by
    apply_fun degree at hr
    apply WithBot.add_right_cancel WithBot.one_ne_bot
    rwa [degree_mul, degree_X_sub_C, fdeg, add_comm] at hr
  use aeval x (g + X ^ m), ?_, r, r.2
  · rw [pf, ← hr]
    simp only [map_add, map_pow, aeval_X, map_mul, map_sub, aeval_C, algebraMap_subfield,
      Nimber.sub_eq]
    ring_nf
    rw [CharTwo.two_eq_zero, mul_zero, add_zero]
  · rw [psl4]
    apply psl2
    rw [← gdeg]
    convert degree_eraseLead_lt gmonic.ne_zero using 2
    rw [← self_sub_C_mul_X_pow, gmonic, map_one, one_mul, CharTwo.sub_eq_add,
      ← natDegree_eq_of_degree_eq_some gdeg]

private lemma pow_mul_of_isField' {x : Nimber} {n m : ℕ} (hx : IsField x) (hm : m ≤ n)
    (h : ∀ p : hx.toSubfield[X], 0 < p.degree → p.degree ≤ n → ∃ y, p.IsRoot y) :
    (∀ y < x ^ₒ m, ∃ p : hx.toSubfield[X], p.degree < m ∧ aeval x p = y) ∧
    (∀ p : hx.toSubfield[X], p.degree < m → aeval x p < x ^ₒ m) ∧
    (x ^ₒ m).IsGroup ∧
    ∀ y < x, x ^ m * y = x ^ₒ m *ₒ y := by
  have xne : x ≠ 0 := hx.ne_zero
  induction m with
  | zero => simp [lt_one_iff_zero]
  | succ m hind =>
  obtain ⟨psl1, psl2, pg, pindl⟩ := hind ((le_succ m).trans hm)
  clear hind
  have sl1 : ∀ y < x ^ₒ (m + 1), ∃ p : hx.toSubfield[X], p.degree < m + 1 ∧ aeval x p = y := by
    intro y hy
    have := ordinalDiv_ordinalAdd_ordinalMod y (x ^ₒ m)
    have b0 : toOrdinal x ^ m ≠ 0 := pow_ne_zero _ xne
    have b1 : y /ₒ x ^ₒ m < x := by
      apply_fun toOrdinal
      rwa [toNimber_toOrdinal, toNimber_toOrdinal, Ordinal.div_lt b0, ← pow_succ]
    have b2 : y %ₒ x ^ₒ m < x ^ₒ m := mod_lt _ b0
    rw [← ordinalMul_add_of_isGroup pg _ b2, ← pindl _ b1] at this
    obtain ⟨q, hq, h⟩ := psl1 (y %ₒ x ^ₒ m) b2
    use X ^ m * C ⟨_, b1⟩ + q, ?_, ?_
    · change _ < Order.succ (m : WithBot ℕ)
      rw [lt_succ_iff]
      apply degree_add_le_of_degree_le
      · rw [mul_comm]
        apply degree_C_mul_X_pow_le
      · exact hq.le
    simp only [map_add, map_mul, aeval_C, map_pow, aeval_X, h]
    conv =>
      rhs; rw [← this]
    simp only [add_left_inj]
    rfl
  use sl1
  have sl2 : ∀ p : hx.toSubfield[X], p.degree < m + 1 → aeval x p < x ^ₒ (m + 1) := by
    intro p hp
    change _ < Order.succ (m : WithBot ℕ) at hp
    rw [lt_succ_iff] at hp
    rw [← monomial_add_erase p m]
    simp only [map_add, aeval_monomial]
    have : (aeval x) (erase m p) < x ^ₒ m := by
      apply psl2
      apply degree_erase_lt_of_degree_le _ hp
    rw [mul_comm, pindl, ordinalMul_add_of_isGroup pg _ this]
    · apply lt_of_lt_of_le
        (b := x ^ₒ m *ₒ (algebraMap (↥hx.toSubfield) Nimber) (p.coeff m) +ₒ x ^ₒ m)
      · simp only [OrderIso.lt_iff_lt, add_lt_add_iff_left, this]
      · simp only [toNimber_toOrdinal, OrderIso.le_iff_le,
          ← Ordinal.mul_succ, pow_succ]
        rw [Ordinal.mul_le_mul_iff_left]
        · simp only [succ_le_iff, OrderIso.lt_iff_lt]
          exact (p.coeff m).2
        · simp [Ordinal.pos_iff_ne_zero, xne]
    exact (p.coeff m).2
  use sl2
  have slg : (x ^ₒ (m + 1)).IsGroup := by
    constructor
    intro a ha b hb
    obtain ⟨ap, apd, rfl⟩ := sl1 a ha
    obtain ⟨bp, bpd, rfl⟩ := sl1 b hb
    rw [← map_add]
    apply sl2
    apply degree_add_lt_of_degree_lt apd bpd
  use slg
  have sl3 : ∀ y < x ^ₒ (m + 1), ∀ a < x, y * a < x ^ₒ (m + 1) := by
    intro y hy a ha
    obtain ⟨p, pd, rfl⟩ := sl1 y hy
    convert_to aeval x (C ⟨a, ha⟩ * p) < _
    · simp [mul_comm]
    apply sl2
    exact (degree_C_mul_le _ _).trans_lt pd
  have sl4 : x ^ₒ (m + 1) = x ^ (m + 1) := by
    have psl4 := pindl 1 hx.2
    simp only [mul_one, ordinalMul_one] at psl4
    rw [pow_succ, mul_def]
    trans sInf (Set.Iio (x ^ₒ (m + 1)))ᶜ
    · simp only [Set.compl_Iio, csInf_Ici]
    congr
    ext y
    rw [Set.mem_Iio, Set.mem_setOf_eq]
    constructor
    · intro hy
      obtain ⟨p, pd, rfl⟩ := sl1 y hy
      exact pow_excluded_eq_aeval hx h hm psl2 psl4 p pd
    · rintro ⟨a, ha, b, hb, rfl⟩
      rw [psl4] at ha
      obtain ⟨p, pdeg, rfl⟩ := psl1 a ha
      convert_to aeval x (p * X + X ^ m * C ⟨b, hb⟩ + p * C ⟨b, hb⟩) < _
      · simp
        rw [mul_comm]
      apply sl2
      change _ < Order.succ (m : WithBot ℕ)
      rw [lt_succ_iff]
      compute_degree
      simp
      constructor
      constructor
      · generalize p.degree = pd at pdeg ⊢
        cases pd
        · simp
        · exact pdeg.succ_le
      · rfl
      · exact pdeg.le
  intro y hy
  rw [← sl4]
  induction' y using induction with y hind
  rw [mul_def]
  trans sInf (Set.Iio (x ^ₒ (m + 1) *ₒ y))ᶜ
  · congr
    ext z
    rw [Set.mem_setOf_eq, Set.mem_Iio]
    constructor
    · rintro ⟨a, ha, b, hb, rfl⟩
      have : a * (y + b) < x ^ₒ (m + 1) := sl3 a ha _ (hx.add_lt _ hy _ (hb.trans hy))
      calc
        a * y + x ^ₒ (m + 1) * b + a * b = x ^ₒ (m + 1) * b + a * (y + b) := by ring
        _ = x ^ₒ (m + 1) *ₒ b + a * (y + b) := by rw [hind b hb (hb.trans hy)]
        _ = x ^ₒ (m + 1) *ₒ b +ₒ a * (y + b) := by rw [ordinalMul_add_of_isGroup slg _ this]
        _ < x ^ₒ (m + 1) *ₒ b +ₒ x ^ₒ (m + 1) := by simpa
        _ = x ^ₒ (m + 1) *ₒ (b +ₒ 1) := by simp [Ordinal.mul_succ]
        _ ≤ x ^ₒ (m + 1) *ₒ y := by
          simp only [map_le_map_iff]
          gcongr
          exact hb.succ_le
    · intro hz
      let b := z /ₒ (x ^ₒ (m + 1))
      have hb : b < y := by
        rw [ordinalDiv_lt]
        exact hz
        simp [xne]
      use (z %ₒ (x ^ₒ (m + 1))) / (b + y), ?_, b, hb
      · have : b + y ≠ 0 := by simp; intro nh; simp [nh] at hb
        have : z = x ^ₒ (m + 1) *ₒ (z /ₒ (x ^ₒ (m + 1))) +ₒ z %ₒ (x ^ₒ (m + 1)) :=
          (ordinalDiv_ordinalAdd_ordinalMod z (x ^ₒ (m + 1))).symm
        rw [← ordinalMul_add_of_isGroup slg _ (ordinalMod_lt _ (by simp [ordinalPow, xne])),
          ← hind _ hb (hb.trans hy)] at this
        nth_rw 3 [this]
        field_simp
        unfold_let b
        ring
      · rw [div_eq_mul_inv]
        apply sl3
        · apply ordinalMod_lt
          simp [xne]
        · apply hx.inv_lt
          apply hx.add_lt _ (hb.trans hy) _ hy
  · simp

lemma pow_mul_of_isField {x : Nimber} {n m : ℕ} (hx : IsField x) (hm : m ≤ n)
    (h : ∀ p : hx.toSubfield[X], 0 < p.degree → p.degree ≤ n → ∃ y, p.IsRoot y) :
    ∀ y < x, x ^ m * y = x ^ₒ m *ₒ y :=
  (pow_mul_of_isField' hx hm h).2.2.2

#print axioms pow_mul_of_isField

/-- The lexicographic ordering on polynomials. -/
def polynomial_LT (p q : Nimber[X]) : Prop :=
  (toLex <| p.toFinsupp.equivMapDomain OrderDual.toDual) <
  (toLex <| q.toFinsupp.equivMapDomain OrderDual.toDual)

local infixl:50 " ≺ " => polynomial_LT

theorem _root_.InvImage.isTrichotomous {α : Sort u} {β : Sort v} {r : β → β → Prop}
    {f : α → β} (hf : Injective f) [h : IsTrichotomous β r] : IsTrichotomous α (InvImage r f) := by
  constructor
  intros
  rw [← hf.eq_iff]
  exact h.trichotomous _ _

theorem _root_.InvImage.isTrans {α : Sort u} {β : Sort v} {r : β → β → Prop}
    (f : α → β) [h : IsTrans β r] : IsTrans α (InvImage r f) := by
  constructor
  intro a b c
  exact h.trans _ _ _

instance isWellOrder_polynomial_LT : IsWellOrder _ (· ≺ ·) where
  wf := by
    apply InvImage.wf
    exact Finsupp.Lex.wellFounded' Nimber.not_lt_zero lt_wf Nat.lt_wfRel.wf
  trichotomous := by
    apply (InvImage.isTrichotomous _).trichotomous
    intro p q h
    dsimp at h
    rw [toLex_inj, Finsupp.ext_iff] at h
    rw [← toFinsupp_inj, Finsupp.ext_iff]
    exact fun a => h a
  trans := (InvImage.isTrans _).trans

/-- For a nimber `x`, the set of non-constant polynomials with coefficients less than `x`, without a
root less than `x`. -/
def noRoots (x : Nimber) : Set Nimber[X] :=
  {p | 0 < p.degree ∧ (∀ c ∈ p.coeffs, c < x) ∧ ∀ r ∈ p.roots, x ≤ r}

theorem roots_of_mem_noRoots_nextField {x : Nimber} {p : Nimber[X]}
    (hp : p ∈ noRoots (nextField x)) : p.roots = 0 := by
  apply (Multiset.empty_or_exists_mem _).resolve_right
  rintro ⟨r, hr⟩
  exact (hp.2.2 r hr).not_lt <| root_mem_nextField hp.2.1 hr

-- Lemma 4
lemma mem_min_roots_of_isField {x : Nimber} (hx : IsField x) (hp : (noRoots x).Nonempty) :
    x ∈ (isWellOrder_polynomial_LT.wf.min _ hp).roots :=
  sorry

theorem ne_zero_of_mem_coeffs {R : Type*} [Semiring R] {x : R} {p : R[X]}
   (hx : x ∈ p.coeffs) : x ≠ 0 := by
  rw [mem_coeffs_iff] at hx
  obtain ⟨n, hn, rfl⟩ := hx
  exact mem_support_iff.1 hn

theorem exists_root_of_degree_pos {p : Nimber[X]} : 0 < p.degree → ∃ r, p.eval r = 0 := by
  apply isWellOrder_polynomial_LT.wf.induction p
  intro p IH hd
  obtain hr | hr := p.roots.toFinset.eq_empty_or_nonempty
  · have hc : p.coeffs.Nonempty := by
      rw [coeffs_nonempty]
      rintro rfl
      rw [degree_zero] at hd
      exact not_lt_bot hd
    let x := p.coeffs.max' hc
    use nextField (succ x)
    apply (mem_roots'.1 _).2
    have hx : 1 < succ x := by
      rw [← succ_zero, succ_lt_succ_iff]
      have := ne_zero_of_mem_coeffs (p.coeffs.max'_mem hc)
      rwa [Nimber.pos_iff_ne_zero]
    have H : p ∈ noRoots (nextField (succ x)) := by
      refine ⟨hd, ?_, ?_⟩
      · intro c hc
        apply (Finset.le_max' _ _ hc).trans_lt
        rw [← succ_le_iff]
        exact le_nfp _ _
      · intro x hx
        rw [Multiset.toFinset_eq_empty] at hr
        rw [hr] at hx
        exact (Multiset.not_mem_zero x hx).elim
    have := mem_min_roots_of_isField (isField_nextField hx) ⟨p, H⟩
    convert this
    apply ((trichotomous_of (· ≺ ·) _ _).resolve_left _).resolve_right
    · intro hlt
      have hm := (isWellOrder_polynomial_LT.wf.min_mem _ ⟨p, H⟩)
      obtain ⟨r, hr⟩ := IH _ hlt hm.1
      rw [← IsRoot.def] at hr
      have := (mem_roots (ne_zero_of_degree_gt hm.1)).2 hr
      rw [roots_of_mem_noRoots_nextField hm] at this
      exact Multiset.not_mem_zero r this
    · exact isWellOrder_polynomial_LT.wf.not_lt_min _ _ H
  · obtain ⟨x, hx⟩ := hr
    rw [Multiset.mem_toFinset, mem_roots'] at hx
    exact ⟨x, hx.2⟩

/-- The nimbers are algebraically closed. -/
instance : IsAlgClosed Nimber :=
  IsAlgClosed.of_exists_root _ fun _ _ hp => exists_root_of_degree_pos hp.degree_pos

end Nimber
