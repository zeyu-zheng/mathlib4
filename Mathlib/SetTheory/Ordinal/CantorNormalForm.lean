/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Violeta Hernández Palacios
-/
import Mathlib.Data.Finsupp.AList
import Mathlib.Data.Nat.Bitwise
import Mathlib.SetTheory.Ordinal.Principal

/-!
# Cantor Normal Form

The Cantor normal form of an ordinal is generally defined as its base `ω` expansion, with its
non-zero exponents in decreasing order. Here, we more generally define a base `b` expansion
`Ordinal.CNF` in this manner, which is well-behaved for any `b ≥ 2`. From it, we define
`Ordinal.CNF_coeff`, which represents the Cantor normal form as a finsupp `Ordinal →₀ Ordinal`. This
is then further specialized to `Ordinal.CNF_coeff_omega : Ordinal → ℕ`.

# Implementation notes

We implement `Ordinal.CNF` as an association list, where keys are exponents and values are
coefficients. This is because this structure intrinsically reflects two key properties of the Cantor
normal form:

- It is ordered.
- It has finitely many entries.
-/

noncomputable section

universe u

open List

namespace Ordinal

variable {b : Ordinal}

/-! ### Recursion principles -/


/-- Inducts on the base `b` expansion of an ordinal. -/
@[elab_as_elim]
noncomputable def CNFRec (b : Ordinal) {C : Ordinal → Sort*} (H0 : C 0)
    (H : ∀ o, o ≠ 0 → C (o % b ^ log b o) → C o) (o : Ordinal) : C o :=
  if h : o = 0 then h ▸ H0 else H o h (CNFRec _ H0 H (o % b ^ log b o))
termination_by o
decreasing_by exact mod_opow_log_lt_self b h

@[simp]
theorem CNFRec_zero {C : Ordinal → Sort*} (b : Ordinal) (H0 : C 0)
    (H : ∀ o, o ≠ 0 → C (o % b ^ log b o) → C o) : CNFRec b H0 H 0 = H0 := by
  rw [CNFRec, dif_pos rfl]

theorem CNFRec_pos (b : Ordinal) {o : Ordinal} {C : Ordinal → Sort*} (ho : o ≠ 0) (H0 : C 0)
    (H : ∀ o, o ≠ 0 → C (o % b ^ log b o) → C o) :
    CNFRec b H0 H o = H o ho (@CNFRec b C H0 H _) := by
  rw [CNFRec, dif_neg ho]

/-- Inducts on the base `ω` expansion of an ordinal.

This differs from `CNFRec` in that every instance of `ω ^ a` is considered separately. -/
@[elab_as_elim]
noncomputable def CNFRec_omega {C : Ordinal → Sort*} (H0 : C 0)
    (H : ∀ o, o ≠ 0 → C (o - ω ^ log ω o) → C o) (o : Ordinal) : C o :=
  if h : o = 0 then h ▸ H0 else H o h (CNFRec_omega H0 H (o - ω ^ log ω o))
termination_by o
decreasing_by exact sub_opow_log_omega_lt h

@[simp]
theorem CNFRec_omega_zero {C : Ordinal → Sort*} (H0 : C 0)
    (H : ∀ o, o ≠ 0 → C (o - ω ^ log ω o) → C o) : CNFRec_omega H0 H 0 = H0 := by
  rw [CNFRec_omega, dif_pos rfl]

theorem CNFRec_omega_pos {o : Ordinal} {C : Ordinal → Sort*} (ho : o ≠ 0) (H0 : C 0)
    (H : ∀ o, o ≠ 0 → C (o - ω ^ log ω o) → C o) :
    CNFRec_omega H0 H o = H o ho (@CNFRec_omega C H0 H _) := by
  rw [CNFRec_omega, dif_neg ho]

/-! ### Cantor normal form as a list -/


/-- The Cantor normal form of an ordinal `o` is the list of coefficients and exponents in the
base-`b` expansion of `o`.

We special-case `CNF 0 o = CNF 1 o = [⟨0, o⟩]` for `o ≠ 0`.

`CNF b (b ^ u₁ * v₁ + b ^ u₂ * v₂) = [⟨u₁, v₁⟩, ⟨u₂, v₂⟩]` -/
@[pp_nodot]
def CNF (b o : Ordinal) : List (Σ _ : Ordinal, Ordinal) :=
  CNFRec b [] (fun o _ho IH ↦ ⟨log b o, o / b ^ log b o⟩::IH) o

/-- The exponents of the Cantor normal form are stored in the first entries. -/
def CNF.exponents (b o : Ordinal) := (CNF b o).keys
/-- The coefficients of the Cantor normal form are stored in the second entries. -/
def CNF.coefficients (b o : Ordinal) := (CNF b o).map Sigma.snd

@[simp]
theorem CNF_zero (b : Ordinal) : CNF b 0 = [] :=
  CNFRec_zero b _ _

@[simp]
theorem CNF.exponents_zero (b : Ordinal) : CNF.exponents b 0 = [] := by
  rw [exponents, CNF_zero, keys_nil]

theorem mem_CNF_exponents_iff {o e : Ordinal} : e ∈ CNF.exponents b o ↔ ∃ c, ⟨e, c⟩ ∈ CNF b o :=
  mem_keys

theorem mem_CNF_exponents_of_mem {o e c : Ordinal} (h : ⟨e, c⟩ ∈ CNF b o) :
    e ∈ CNF.exponents b o :=
  mem_CNF_exponents_iff.2 ⟨c, h⟩

@[simp]
theorem CNF.coefficients_zero (b : Ordinal) : CNF.coefficients b 0 = [] := by
  rw [coefficients, CNF_zero, map_nil]

theorem mem_CNF_coefficients_iff {o c : Ordinal} :
    c ∈ CNF.coefficients b o ↔ ∃ e, ⟨e, c⟩ ∈ CNF b o := by
  simp [CNF.coefficients]

theorem mem_CNF_coefficients_of_mem {o e c : Ordinal} (h : ⟨e, c⟩ ∈ CNF b o) :
    c ∈ CNF.coefficients b o :=
  mem_CNF_coefficients_iff.2 ⟨e, h⟩

/-- Recursive definition for the Cantor normal form. -/
theorem CNF_ne_zero {o : Ordinal} (ho : o ≠ 0) :
    CNF b o = ⟨log b o, o / b ^ log b o⟩::CNF b (o % b ^ log b o) :=
  CNFRec_pos b ho _ _

@[simp]
theorem CNF_eq_nil {o : Ordinal} : CNF b o = [] ↔ o = 0 := by
  constructor
  · intro h
    by_contra ho
    rw [CNF_ne_zero ho] at h
    exact cons_ne_nil _ _ h
  · rintro rfl
    exact CNF_zero b

theorem zero_CNF {o : Ordinal} (ho : o ≠ 0) : CNF 0 o = [⟨0, o⟩] := by
  simp [CNF_ne_zero ho]

theorem one_CNF {o : Ordinal} (ho : o ≠ 0) : CNF 1 o = [⟨0, o⟩] := by
  simp [CNF_ne_zero ho]

theorem CNF_of_le_one {o : Ordinal} (hb : b ≤ 1) (ho : o ≠ 0) : CNF b o = [⟨0, o⟩] := by
  rcases le_one_iff.1 hb with (rfl | rfl)
  · exact zero_CNF ho
  · exact one_CNF ho

theorem CNF_of_lt_self {o : Ordinal} (ho : o ≠ 0) (hb : o < b) : CNF b o = [⟨0, o⟩] := by
  simp only [CNF_ne_zero ho, log_eq_zero hb, opow_zero, div_one, mod_one, CNF_zero]

theorem CNF_opow (hb : 1 < b) (e : Ordinal) : CNF b (b ^ e) = [⟨e, 1⟩] := by
  have H := (opow_pos e (zero_le_one.trans_lt hb)).ne'
  rw [CNF_ne_zero H]
  simpa [log_opow hb e] using div_self H

theorem CNF_one (hb : 1 < b) : CNF b 1 = [⟨0, 1⟩] := by
  convert CNF_opow hb 0
  exact (opow_zero b).symm

theorem CNF_self (hb : 1 < b) : CNF b b = [⟨1, 1⟩] := by
  convert CNF_opow hb 1
  exact (opow_one b).symm

theorem CNF_opow_mul (hb : 1 < b) (o x : Ordinal) :
    CNF b (b ^ x * o) = (CNF b o).map (fun y => ⟨x + y.1, y.2⟩) := by
  refine CNFRec b ?_ ?_ o
  · simp
  · intro o ho IH
    have hx := opow_ne_zero x (zero_lt_one.trans hb).ne'
    rw [CNF_ne_zero ho, CNF_ne_zero (mul_ne_zero hx ho), log_opow_mul hb x ho, opow_add,
      map_cons, cons.injEq]
    constructor
    · rw [mul_div_mul_cancel hx]
    · rw [mul_mod_mul, IH]

theorem CNF_opow_mul_add {b x o₂ : Ordinal} (o₁ : Ordinal) (ho₂ : o₂ < b ^ x) :
    CNF b (b ^ x * o₁ + o₂) = CNF b (b ^ x * o₁) ++ CNF b o₂ := by
  obtain hb | hb := le_or_lt b 1
  · obtain rfl := Ordinal.lt_one_iff_zero.1 <| ho₂.trans_le (opow_le_one hb x)
    simp
  · refine CNFRec b ?_ ?_ o₁
    · simp
    · intro o₁ ho₁ IH
      have h₁ : b ^ x ≠ 0 := opow_ne_zero x (zero_lt_one.trans hb).ne'
      have h₂ : b ^ x * o₁ ≠ 0 := mul_ne_zero h₁ ho₁
      rw [CNF_ne_zero (add_ne_zero_of_left h₂ o₂), CNF_ne_zero h₂]
      simp [log_opow_mul hb _ ho₁, log_opow_mul_add hb ho₁ ho₂]
      constructor
      · rwa [opow_add, mul_div_mul_cancel, mul_add_div_mul ho₂]
      · rw [opow_add, mul_mod_mul, ← IH, mul_add_mod_mul ho₂]

theorem CNF_opow_mul_add' {b x o₂ : Ordinal} (hb : 1 < b) (o₁ : Ordinal) (ho₂ : o₂ < b ^ x) :
    CNF b (b ^ x * o₁ + o₂) = (CNF b o₁).map (fun y => ⟨x + y.1, y.2⟩) ++ CNF b o₂ := by
  rw [CNF_opow_mul_add o₁ ho₂, CNF_opow_mul hb]

/-- Every exponent in the Cantor normal form `CNF b o` is less or equal to `log b o`. -/
theorem le_log_of_mem_CNF_exponents {b o : Ordinal.{u}} {x : Ordinal} :
    x ∈ CNF.exponents b o → x ≤ log b o := by
  rw [CNF.exponents]
  refine CNFRec b ?_ ?_ o
  · simp
  · intro o ho H
    rw [CNF_ne_zero ho, keys_cons, mem_cons]
    rintro (rfl | h)
    · exact le_rfl
    · exact (H h).trans (log_mono_right _ (mod_opow_log_lt_self b ho).le)

/-- Every coefficient in a Cantor normal form is positive. -/
theorem pos_of_mem_CNF_coefficients {b o : Ordinal.{u}} {x : Ordinal} :
    x ∈ CNF.coefficients b o → 0 < x := by
  rw [CNF.coefficients]
  refine CNFRec b ?_ ?_ o
  · simp
  · intro o ho IH
    rw [CNF_ne_zero ho]
    rintro (h | ⟨_, h⟩)
    · exact div_opow_log_pos b ho
    · exact IH h

/-- Every coefficient in the Cantor normal form `CNF b o` is less than `b`. -/
theorem lt_of_mem_CNF_coefficients {b o : Ordinal.{u}} (hb : 1 < b) {x : Ordinal} :
    x ∈ CNF.coefficients b o → x < b := by
  rw [CNF.coefficients]
  refine CNFRec b ?_ ?_ o
  · simp
  · intro o ho IH h
    rw [CNF_ne_zero ho] at h
    obtain rfl | h := mem_cons.mp h
    · simpa only using div_opow_log_lt o hb
    · exact IH h

/-- The exponents of the `CNF` are a decreasing sequence. -/
theorem CNF_exponents_sorted (b o : Ordinal) : (CNF.exponents b o).Sorted (· > ·) := by
  rw [CNF.exponents]
  refine CNFRec b ?_ ?_ o
  · simp
  · intro o ho IH
    obtain hb | hb := le_or_gt b 1
    · rw [CNF_of_le_one hb ho]
      exact sorted_singleton _
    · obtain hob | hbo := lt_or_le o b
      · rw [CNF_of_lt_self ho hob]
        exact sorted_singleton _
      · rw [CNF_ne_zero ho, keys_cons, sorted_cons]
        refine ⟨?_, IH⟩
        intro a H
        exact (le_log_of_mem_CNF_exponents H).trans_lt <| log_mod_opow_log_lt_log_self hb hbo

theorem CNF_nodupKeys (b o : Ordinal) : (CNF b o).NodupKeys :=
  (CNF_exponents_sorted b o).nodup

/-- Evaluating the Cantor normal form of an ordinal returns the ordinal. -/
theorem CNF_foldr (b o : Ordinal) : (CNF b o).foldr (fun p r ↦ b ^ p.1 * p.2 + r) 0 = o := by
  refine CNFRec b ?_ ?_ o
  · rw [CNF_zero]
    rfl
  · intro o ho IH
    rw [CNF_ne_zero ho, foldr_cons, IH, div_add_mod]

theorem CNF_injective (b : Ordinal) : Function.Injective (CNF b) :=
  Function.LeftInverse.injective (CNF_foldr b)

@[simp]
theorem CNF_inj {b o₁ o₂ : Ordinal} : CNF b o₁ = CNF b o₂ ↔ o₁ = o₂ :=
  (CNF_injective b).eq_iff

theorem foldr_lt {x} {l : List (Σ _ : Ordinal, Ordinal)}
    (h_sort : (x :: l).keys.Sorted (· > ·))
    (h_lt : ∀ p ∈ x :: l, p.2 < b) :
    l.foldr (fun p r ↦ b ^ p.1 * p.2 + r) 0 < b ^ x.1 := by
  have hb := (Ordinal.zero_le _).trans_lt <| h_lt _ (mem_cons_self x l)
  revert x
  induction' l with a l IH
  · intros
    rw [foldr_nil]
    exact opow_pos _ hb
  · intro x h_sort h_lt
    rw [foldr_cons]
    apply (opow_mul_add_lt_opow_succ (h_lt a _) _).trans_le
    · apply opow_le_opow_right hb <| Order.succ_le_of_lt _
      exact rel_of_sorted_cons h_sort _ (mem_cons_self _ _)
    · exact mem_cons_of_mem _ (mem_cons_self a l)
    · apply IH h_sort.of_cons
      intro p hp
      exact h_lt p (mem_cons_of_mem x hp)

/-- The cantor normal form of an ordinal is unique. -/
theorem CNF_eq (hb : 1 < b) (l : List (Σ _ : Ordinal, Ordinal))
    (h_sort : l.keys.Sorted (· > ·))
    (h_lt : ∀ p ∈ l, p.2 ≠ 0 ∧ p.2 < b) :
    CNF b (l.foldr (fun p r ↦ b ^ p.1 * p.2 + r) 0) = l := by
  have hb' : b ≠ 0 := (zero_lt_one.trans hb).ne'
  induction' l with a l IH
  · rw [foldr_nil, CNF_zero]
  · have ha := h_lt a (mem_cons_self a l)
    have H := foldr_lt h_sort (fun p hp => (h_lt p hp).2)
    have H' := log_opow_mul_add' hb ha.1 ha.2 H
    rw [CNF_ne_zero, foldr_cons, cons.injEq, H', Sigma.mk.inj_iff]
    refine ⟨⟨rfl, ?_⟩, ?_⟩
    · rw [mul_add_div _ (opow_ne_zero _ hb'), div_eq_zero_of_lt H, add_zero]
    · convert IH (h_sort.of_cons) _
      · rw [mul_add_mod_self]
        exact mod_eq_of_lt H
      · intro p hp
        exact h_lt p <| mem_cons_of_mem a hp
    · intro h
      obtain (h | h) := mul_eq_zero.1 <| left_eq_zero_of_add_eq_zero h
      · exact opow_ne_zero _ hb' h
      · exact ha.1 h

/-! ### Cantor normal form as a finsupp -/


open Finsupp

/-- `CNF_coeff b o` is the finitely supported function, returning the coefficient of `b ^ e` in the
`CNF` of `o`, for each `e`. -/
@[pp_nodot]
def CNF_coeff (b o : Ordinal) : Ordinal →₀ Ordinal :=
  AList.lookupFinsupp ⟨_, CNF_nodupKeys b o⟩

theorem CNF_coeff_def (b o e : Ordinal) : CNF_coeff b o e = ((CNF b o).dlookup e).getD 0 := by
  rw [CNF_coeff, AList.lookupFinsupp_apply]
  rfl

theorem support_CNF_coeff (b o : Ordinal) :
    (CNF_coeff b o).support = (CNF.exponents b o).toFinset := by
  rw [CNF_coeff, AList.lookupFinsupp_support]
  congr
  apply List.filter_eq_self.2
  intro a h
  exact decide_eq_true (pos_of_mem_CNF_coefficients (mem_map_of_mem _ h)).ne'

theorem CNF_coeff_of_mem_CNF {o e c : Ordinal} (h : ⟨e, c⟩ ∈ CNF b o) :
    CNF_coeff b o e = c := by
  rw [CNF_coeff, AList.lookupFinsupp_apply, AList.mem_lookup_iff.2 h]
  rfl

theorem CNF_coeff_eq_pos_iff {o e c : Ordinal} (hc : c ≠ 0) :
    CNF_coeff b o e = c ↔ ⟨e, c⟩ ∈ CNF b o := by
  rw [CNF_coeff, AList.lookupFinsupp_eq_iff_of_ne_zero hc]
  exact AList.mem_lookup_iff

theorem CNF_coeff_eq_zero_iff {o e : Ordinal} : CNF_coeff b o e = 0 ↔ e ∉ CNF.exponents b o := by
  rw [CNF_coeff, AList.lookupFinsupp_eq_zero_iff]
  constructor
  · rintro (h | h)
    · exact h
    · exact (lt_irrefl 0 <| pos_of_mem_CNF_coefficients <|
        mem_map_of_mem Sigma.snd <| AList.mem_lookup_iff.1 h).elim
  · exact Or.inl

alias ⟨_, CNF_coeff_of_not_mem_CNF⟩ := CNF_coeff_eq_zero_iff

theorem CNF_coeff_ne_zero {o e : Ordinal} (h : e ∈ CNF.exponents b o) : CNF_coeff b o e ≠ 0 := by
  intro h
  rw [CNF_coeff_eq_zero_iff] at h
  contradiction

theorem CNF_coeff_zero_apply (b e : Ordinal) : CNF_coeff b 0 e = 0 := by
  rw [CNF_coeff_eq_zero_iff, CNF.exponents_zero]
  exact not_mem_nil e

@[simp]
theorem CNF_coeff_zero (b : Ordinal) : CNF_coeff b 0 = 0 := by
  ext e
  exact CNF_coeff_zero_apply b e

theorem CNF_coeff_of_le_one (hb : b ≤ 1) (o : Ordinal) : CNF_coeff b o = single 0 o := by
  ext a
  obtain rfl | ho := eq_or_ne o 0
  · simp
  · obtain rfl | ha := eq_or_ne a 0
    · apply CNF_coeff_of_mem_CNF
      rw [CNF_of_le_one hb ho]
      simp
    · rw [single_eq_of_ne ha.symm, CNF_coeff_eq_zero_iff, CNF.exponents, CNF_of_le_one hb ho]
      simpa using ha

theorem CNF_coeff_lt (hb : 1 < b) (o e : Ordinal) : CNF_coeff b o e < b := by
  by_cases h : e ∈ CNF.exponents b o
  · obtain ⟨c, hc⟩ := mem_CNF_exponents_iff.1 h
    rw [CNF_coeff_of_mem_CNF hc]
    exact lt_of_mem_CNF_coefficients hb <| mem_CNF_coefficients_of_mem hc
  · rw [CNF_coeff_of_not_mem_CNF h]
    exact zero_lt_one.trans hb

@[simp]
theorem zero_CNF_coeff (o : Ordinal) : CNF_coeff 0 o = single 0 o :=
  CNF_coeff_of_le_one zero_le_one o

@[simp]
theorem one_CNF_coeff (o : Ordinal) : CNF_coeff 1 o = single 0 o :=
  CNF_coeff_of_le_one le_rfl o

theorem CNF_coeff_opow (hb : 1 < b) (e : Ordinal) :
    CNF_coeff b (b ^ e) = single e 1 := by
  ext a
  obtain rfl | ha := eq_or_ne e a
  · rw [single_eq_same]
    apply CNF_coeff_of_mem_CNF
    rw [CNF_opow hb]
    exact mem_cons_self _ _
  · rw [single_eq_of_ne ha, CNF_coeff_eq_zero_iff, CNF.exponents, CNF_opow hb,
      List.keys_singleton, mem_singleton]
    exact ha.symm

theorem CNF_coeff_one (hb : 1 < b) : CNF_coeff b 1 = single 0 1 := by
  convert CNF_coeff_opow hb 0
  exact (opow_zero b).symm

theorem CNF_coeff_self (hb : 1 < b) : CNF_coeff b b = single 1 1 := by
  convert CNF_coeff_opow hb 1
  exact (opow_one b).symm

theorem CNF_coeff_of_lt_self {o : Ordinal} (ho : o < b) : CNF_coeff b o = single 0 o := by
  obtain rfl | ho' := eq_or_ne o 0
  · simp
  · ext e
    obtain rfl | he := eq_or_ne e 0
    · rw [single_eq_same]
      apply CNF_coeff_of_mem_CNF
      rw [CNF_of_lt_self ho' ho, mem_singleton]
    · rw [single_eq_of_ne he.symm, CNF_coeff_eq_zero_iff, mem_CNF_exponents_iff]
      rintro ⟨c, hc⟩
      rw [CNF_of_lt_self ho' ho, mem_singleton, Sigma.mk.inj_iff] at hc
      exact he hc.1

theorem CNF_coeff_of_gt {o e : Ordinal} (he : o < b ^ e) : CNF_coeff b o e = 0 := by
  obtain hb | hb := le_or_lt b 1
  · rw [CNF_coeff_of_le_one hb, Ordinal.lt_one_iff_zero.1 <| he.trans_le (opow_le_one hb e)]
    simp
  · obtain rfl | ho := eq_or_ne o 0
    · simp
    · rw [CNF_coeff_eq_zero_iff, mem_CNF_exponents_iff]
      rintro ⟨c, hc⟩
      rw [lt_opow_iff_log_lt hb ho] at he
      exact (le_log_of_mem_CNF_exponents (mem_CNF_exponents_of_mem hc)).not_lt he

theorem CNF_coeff_opow_mul_of_ge (hb : 1 < b) (o x e : Ordinal) :
    CNF_coeff b (b ^ x * o) (x + e) = CNF_coeff b o e := by
  rw [CNF_coeff_def, CNF_coeff_def, CNF_opow_mul hb, dlookup_map₁]
  intro a b h
  rwa [add_left_cancel] at h

theorem CNF_coeff_opow_mul_of_lt {b e x : Ordinal} (hb : 1 < b) (o : Ordinal) (he : e < x) :
    CNF_coeff b (b ^ x * o) e = 0 := by
  rw [CNF_coeff_eq_zero_iff, mem_CNF_exponents_iff, CNF_opow_mul hb]
  simp_rw [mem_map]
  push_neg
  rintro c _ _ ⟨rfl, rfl⟩
  exact (le_add_right _ _).not_lt he

/-- The function `CNF_coeff b (b ^ x * o)` is the translation of `CNF_coeff b o` by `x`. -/
theorem CNF_coeff_opow_mul (hb : 1 < b) (o x : Ordinal) :
    (CNF_coeff b (b ^ x * o)).comapDomain (x + ·)
      (fun _ _ _ _ => (add_left_cancel x).1) = CNF_coeff b o := by
  ext e
  exact CNF_coeff_opow_mul_of_ge hb o x e

theorem CNF_coeff_opow_mul_of_lt_self {x o : Ordinal} (hb : 1 < b) (ho : o < b) :
    CNF_coeff b (b ^ x * o) = single x o := by
  ext e
  obtain he | he := lt_or_le e x
  · rw [CNF_coeff_opow_mul_of_lt hb o he, single_eq_of_ne he.ne']
  · conv_lhs => rw [← Ordinal.add_sub_cancel_of_le he]
    rw [CNF_coeff_opow_mul_of_ge hb, CNF_coeff_of_lt_self ho]
    obtain rfl | he := he.eq_or_lt
    · simp
    · rw [single_eq_of_ne, single_eq_of_ne he.ne]
      rwa [Ne.eq_def, Eq.comm, Ordinal.sub_eq_zero_iff_le, not_le]

theorem CNF_coeff_opow_mul_add_of_lt {x o₂ e : Ordinal} (hb : 1 < b) (o₁ : Ordinal)
    (ho₂ : o₂ < b ^ x) (he : e < x) : CNF_coeff b (b ^ x * o₁ + o₂) e = CNF_coeff b o₂ e := by
  rw [CNF_coeff_def, CNF_opow_mul_add' hb _ ho₂, dlookup_append_of_not_mem_left]
  · rw [CNF_coeff_def]
  · simp_rw [List.mem_keys, mem_map]
    rintro ⟨_, _, ⟨_, ⟨h, _⟩⟩⟩
    exact (le_add_right _ _).not_lt he

theorem CNF_coeff_opow_mul_add_of_ge {x o₂ e : Ordinal} (o₁ : Ordinal) (ho₂ : o₂ < b ^ x)
    (he : x ≤ e) : CNF_coeff b (b ^ x * o₁ + o₂) e = CNF_coeff b (b ^ x * o₁) e := by
  obtain hb | hb := le_or_lt b 1
  · obtain rfl := Ordinal.lt_one_iff_zero.1 <| ho₂.trans_le (opow_le_one hb x)
    simp
  · rw [CNF_coeff_def, CNF_opow_mul_add _ ho₂, dlookup_append_of_not_mem_right]
    · rw [CNF_coeff_def]
    · obtain rfl | ho := eq_or_ne o₂ 0
      · simp
      · intro h
        rw [lt_opow_iff_log_lt hb ho] at ho₂
        exact ((le_log_of_mem_CNF_exponents h).trans_lt ho₂).not_le he

theorem CNF_coeff_opow_mul_add {x o₂ : Ordinal} (o₁ : Ordinal) (ho₂ : o₂ < b ^ x) :
    CNF_coeff b (b ^ x * o₁ + o₂) = CNF_coeff b (b ^ x * o₁) + CNF_coeff b o₂ := by
  obtain hb | hb := le_or_lt b 1
  · obtain rfl := Ordinal.lt_one_iff_zero.1 <| ho₂.trans_le (opow_le_one hb x)
    simp
  · ext e
    dsimp
    obtain he | he := lt_or_le e x
    · rw [CNF_coeff_opow_mul_add_of_lt hb _ ho₂ he, CNF_coeff_opow_mul_of_lt hb _ he, zero_add]
    · rw [CNF_coeff_opow_mul_add_of_ge _ ho₂ he,
        CNF_coeff_of_gt <| ho₂.trans_le <| opow_le_opow_right (zero_lt_one.trans hb) he, add_zero]

theorem CNF_coeff_opow_mul_add_apply {x o₂ : Ordinal} (o₁ : Ordinal) (ho₂ : o₂ < b ^ x) (e) :
    CNF_coeff b (b ^ x * o₁ + o₂) e = CNF_coeff b (b ^ x * o₁) e + CNF_coeff b o₂ e := by
  rw [CNF_coeff_opow_mul_add _ ho₂]
  rfl

theorem CNF_coeff_apply_zero (hb : b ≠ 1) (o : Ordinal) :
    CNF_coeff b o 0 = o % b := by
  obtain hb | hb' := le_or_lt b 1
  · obtain rfl | rfl := Ordinal.le_one_iff.1 hb
    · simp
    · contradiction
  · rw [CNF_coeff_def]
    refine CNFRec b ?_ ?_ o
    · simp
    · intro o ho IH
      rw [CNF_ne_zero ho]
      obtain h | h := eq_or_ne (log b o) 0
      · rw [h, dlookup_cons_eq, Option.getD_some, opow_zero, div_one,
          mod_eq_of_lt <| (log_eq_zero_iff hb').1 h]
      · rw [dlookup_cons_ne _ _ h.symm, IH, mod_mod_of_dvd o (dvd_opow b h)]

theorem CNF_coeff_apply (hb : 1 < b) (o e : Ordinal) :
    CNF_coeff b o e = o / b ^ e % b := by
  have h := mod_lt o (opow_ne_zero e (zero_lt_one.trans hb).ne')
  conv_lhs => rw [← div_add_mod o (b ^ e)]
  rw [CNF_coeff_opow_mul_add_apply _ h]
  have H := CNF_coeff_opow_mul_of_ge hb (o / b ^ e) e 0
  rw [add_zero] at H
  rw [H, CNF_coeff_apply_zero hb.ne', CNF_coeff_of_gt h, add_zero]

theorem CNF_coeff_opow_div_apply (hb : 1 < b) (o x e : Ordinal) :
    CNF_coeff b (o / b ^ x) e = CNF_coeff b o (x + e) := by
  conv_rhs => rw [← div_add_mod o (b ^ x)]
  rw [CNF_coeff_opow_mul_add_of_ge, CNF_coeff_opow_mul_of_ge hb ]
  · exact mod_lt o (opow_ne_zero x (zero_lt_one.trans hb).ne')
  · exact le_add_right x e

/-- The function `CNF_coeff b (o / b ^ x)` is the translation of `CNF_coeff b o` by `x`. -/
theorem CNF_coeff_opow_div (hb : 1 < b) (o x : Ordinal) :
    CNF_coeff b (o / b ^ x) = (CNF_coeff b o).comapDomain (x + ·)
      (fun _ _ _ _ => (add_left_cancel x).1) := by
  ext e
  exact CNF_coeff_opow_div_apply hb o x e

theorem CNF_coeff_mod_opow_of_lt {x e : Ordinal} (hb : 1 < b) (o : Ordinal) (he : e < x) :
    CNF_coeff b (o % b ^ x) e = CNF_coeff b o e := by
  conv_rhs => rw [← div_add_mod o (b ^ x),
    CNF_coeff_opow_mul_add_of_lt hb _ (mod_lt _ (opow_ne_zero x (zero_lt_one.trans hb).ne')) he]

theorem CNF_coeff_mod_opow_of_ge {x e : Ordinal} (hb : b ≠ 0) (o : Ordinal) (he : x ≤ e) :
    CNF_coeff b (o % b ^ x) e = 0 :=
  CNF_coeff_of_gt <| (mod_lt _ (opow_ne_zero x hb)).trans_le <|
    opow_le_opow_right (Ordinal.pos_iff_ne_zero.2 hb) he

/-! ### Characterization of addition -/


theorem CNF_coeff_add_of_gt {o₂ e : Ordinal} (hp : Principal (· + ·) b) (o₁ : Ordinal)
    (he : log b o₂ < e) : CNF_coeff b (o₁ + o₂) e = CNF_coeff b o₁ e := by
  obtain hb | hb := le_or_lt b 1
  · rw [log_of_left_le_one hb] at he
    iterate 2 rw [CNF_coeff_of_le_one hb, single_eq_of_ne he.ne]
  · rw [CNF_coeff_apply hb, CNF_coeff_apply hb, add_div_of_lt_of_principal_add (hp.opow e)]
    apply lt_opow_of_log_lt hb he

theorem CNF_coeff_add_of_eq (hp : Principal (· + ·) b) (o₁ o₂ : Ordinal) :
    CNF_coeff b (o₁ + o₂) (log b o₂) = CNF_coeff b o₁ (log b o₂) + CNF_coeff b o₂ (log b o₂) := by
  obtain rfl | ho₂ := eq_or_ne o₂ 0
  · simp
  · obtain hb | hb := le_or_lt b 1
    · iterate 3 rw [CNF_coeff_of_le_one hb]
      rw [single_add]
      rfl
    · have ho₂' := div_opow_log_lt o₂ hb
      iterate 3 rw [CNF_coeff_apply hb]
      rw [add_div_of_ge_of_principal_add (hp.opow _), add_mod_of_lt_of_principal_add hp ho₂',
        mod_eq_of_lt ho₂']
      exact opow_log_le_self b ho₂

theorem CNF_coeff_add_of_eq' {e o₂ : Ordinal} (hp : Principal (· + ·) b) (o₁ : Ordinal)
    (he : log b o₂ = e) : CNF_coeff b (o₁ + o₂) e = CNF_coeff b o₁ e + CNF_coeff b o₂ e := by
  obtain rfl := he
  exact CNF_coeff_add_of_eq hp o₁ o₂

theorem CNF_coeff_add_of_lt {o₂ e : Ordinal} (hp : Principal (· + ·) b) (o₁ : Ordinal)
    (he : e < log b o₂) : CNF_coeff b (o₁ + o₂) e = CNF_coeff b o₂ e := by
  have ho₂ : o₂ ≠ 0 := by
    rintro rfl
    rw [log_zero_right] at he
    exact Ordinal.not_lt_zero e he
  obtain hb | hb := le_or_lt b 1
  · rw [log_of_left_le_one hb] at he
    exact (Ordinal.not_lt_zero e he).elim
  · conv_lhs => rw [← div_add_mod o₁ (b ^ log b o₂)]
    have h := opow_ne_zero (log b o₂) (zero_lt_one.trans hb).ne'
    rw [add_assoc, (hp.opow _).add_absorp_of_ge (mod_lt o₁ h) (opow_log_le_self _ ho₂)]
    conv_lhs => left; right; right; rw [← div_add_mod o₂ (b ^ log b o₂)]
    rw [← add_assoc, ← mul_add, CNF_coeff_opow_mul_add_of_lt hb _
      (mod_lt o₂ h) he, CNF_coeff_mod_opow_of_lt hb _ he]

theorem CNF_coeff_opow_mul_add_of_principal_add_apply {b x o₂ : Ordinal} (hp : Principal (· + ·) b)
    (o₁ : Ordinal) (ho₂ : o₂ < b ^ Order.succ x) (e) :
    CNF_coeff b (b ^ x * o₁ + o₂) e = CNF_coeff b (b ^ x * o₁) e + CNF_coeff b o₂ e := by
  obtain hb | hb := le_or_lt b 1
  · obtain rfl := Ordinal.lt_one_iff_zero.1 <| ho₂.trans_le (opow_le_one hb _)
    simp
  · have hb₀ := (zero_lt_one.trans hb).ne'
    have hbx := opow_ne_zero x hb₀
    obtain ho₂' | ho₂' := lt_or_le o₂ (b ^ x)
    · rw [CNF_coeff_opow_mul_add o₁ ho₂']
      rfl
    · have H₁ : o₂ % b ^ x < b ^ x := mod_lt o₂ hbx
      rw [← div_add_mod o₂ (b ^ x), ← add_assoc, ← mul_add, CNF_coeff_opow_mul_add_apply _ H₁,
        CNF_coeff_opow_mul_add_apply _ H₁, ← add_assoc]
      obtain he | he := lt_or_le e x
      · iterate 3 rw [CNF_coeff_opow_mul_of_lt hb _ he]
        simp
      · rw [mul_add]
        have H₂ := ((div_pos hbx).2 ho₂').ne'
        have H₃ : log b (b ^ x * (o₂ / b ^ x)) = x := by
          rw [log_opow_mul hb _ H₂, log_eq_zero, add_zero]
          rwa [div_lt hbx, ← opow_succ]
        obtain rfl | he := he.eq_or_lt
        · rw [CNF_coeff_add_of_eq' hp _ H₃]
        · have H₄ : b ^ x * (o₂ / b ^ x) < b ^ e := by
            rwa [lt_opow_iff_log_lt hb (mul_ne_zero hbx H₂), H₃]
          rw [← H₃] at he
          rw [CNF_coeff_add_of_gt hp _ he, CNF_coeff_of_gt H₄, add_zero]

theorem CNF_coeff_opow_mul_add_of_principal_add {b x o₂ : Ordinal} (hp : Principal (· + ·) b)
    (o₁ : Ordinal) (ho₂ : o₂ < b ^ Order.succ x) :
    CNF_coeff b (b ^ x * o₁ + o₂) = CNF_coeff b (b ^ x * o₁) + CNF_coeff b o₂ := by
  ext e
  exact CNF_coeff_opow_mul_add_of_principal_add_apply hp o₁ ho₂ e

theorem CNF_coeff_opow_add_of_principal_add_apply {b x o : Ordinal} (hp : Principal (· + ·) b)
    (ho₂ : o < b ^ Order.succ x) (e) :
    CNF_coeff b (b ^ x + o) e = CNF_coeff b (b ^ x) e + CNF_coeff b o e := by
  convert CNF_coeff_opow_mul_add_of_principal_add_apply hp 1 ho₂ e using 1 <;>
  rw [mul_one]

theorem CNF_coeff_opow_add_of_principal_add {b x o : Ordinal} (hp : Principal (· + ·) b)
    (ho₂ : o < b ^ Order.succ x) :
    CNF_coeff b (b ^ x + o) = CNF_coeff b (b ^ x) + CNF_coeff b o := by
  ext e
  exact CNF_coeff_opow_add_of_principal_add_apply hp ho₂ e

/-! ### Base ω -/

/-- A specialization of `CNF_coeff` to base `ω`, which takes advantage of knowing all coefficients
are less than `ω` and thus natural numbers. -/
@[pp_nodot]
def CNF_coeff_omega (o : Ordinal) : Ordinal →₀ ℕ :=
  (CNF_coeff ω o).mapRange _ toNat_zero

@[simp]
theorem natCast_CNF_coeff_omega (o e : Ordinal) : CNF_coeff_omega o e = CNF_coeff ω o e := by
  rw [CNF_coeff_omega, mapRange_apply, natCast_toNat (CNF_coeff_lt one_lt_omega o e)]

theorem CNF_coeff_omega_eq_iff {o e : Ordinal} {x : ℕ} :
    CNF_coeff_omega o e = x ↔ CNF_coeff ω o e = x := by
  rw [← @Nat.cast_inj Ordinal, natCast_CNF_coeff_omega]

theorem CNF_coeff_omega_mapRange (o : Ordinal) :
    (CNF_coeff_omega o).mapRange _ Nat.cast_zero = CNF_coeff ω o := by
  ext e
  rw [mapRange_apply, natCast_CNF_coeff_omega]

theorem support_CNF_coeff_omega (o : Ordinal) :
    (CNF_coeff_omega o).support = (CNF.exponents ω o).toFinset := by
  rw [← support_CNF_coeff, ← CNF_coeff_omega_mapRange,
    support_mapRange_of_injective _ _ Nat.cast_injective]

theorem CNF_coeff_omega_of_mem_CNF {o e : Ordinal} {c : ℕ} (h : ⟨e, c⟩ ∈ CNF ω o) :
    CNF_coeff_omega o e = c := by
  rw [CNF_coeff_omega_eq_iff]
  exact CNF_coeff_of_mem_CNF h

theorem CNF_coeff_omega_eq_pos_iff {o e : Ordinal} {c : ℕ} (hc : c ≠ 0) :
    CNF_coeff_omega o e = c ↔ ⟨e, c⟩ ∈ CNF ω o := by
  rw [CNF_coeff_omega_eq_iff]
  rw [← (@Nat.cast_injective Ordinal).ne_iff] at hc
  exact CNF_coeff_eq_pos_iff hc

theorem CNF_coeff_omega_eq_zero_iff {o e : Ordinal} :
    CNF_coeff_omega o e = 0 ↔ e ∉ CNF.exponents ω o := by
  rw [CNF_coeff_omega_eq_iff, Nat.cast_zero, CNF_coeff_eq_zero_iff]

alias ⟨_, CNF_omega_coeff_of_not_mem_CNF⟩ := CNF_coeff_omega_eq_zero_iff

theorem CNF_coeff_omega_ne_zero {o e : Ordinal} (h : e ∈ CNF.exponents ω o) :
    CNF_coeff_omega o e ≠ 0 := by
  intro h
  rw [CNF_coeff_omega_eq_zero_iff] at h
  contradiction

theorem CNF_coeff_omega_zero_apply (e : Ordinal) : CNF_coeff_omega 0 e = 0 := by
  rw [CNF_coeff_omega_eq_iff, Nat.cast_zero, CNF_coeff_zero_apply]

@[simp]
theorem CNF_coeff_omega_zero : CNF_coeff_omega 0 = 0 := by
  ext e
  exact CNF_coeff_omega_zero_apply e

theorem CNF_coeff_omega_opow (e : Ordinal) : CNF_coeff_omega (ω ^ e) = single e 1 := by
  ext a
  rw [CNF_coeff_omega_eq_iff, CNF_coeff_opow one_lt_omega]
  convert (apply_single' _ _ e 1 a).symm <;>
  simp

@[simp]
theorem CNF_coeff_omega_one : CNF_coeff_omega 1 = single 0 1 := by
  convert CNF_coeff_omega_opow 0
  exact (opow_zero ω).symm

@[simp]
theorem CNF_coeff_omega_omega : CNF_coeff_omega ω = single 1 1 := by
  convert CNF_coeff_omega_opow 1
  exact (opow_one ω).symm

@[simp]
theorem CNF_coeff_omega_natCast {n : ℕ} : CNF_coeff_omega n = single 0 n := by
  ext e
  rw [CNF_coeff_omega_eq_iff, CNF_coeff_of_lt_self (nat_lt_omega n)]
  exact (apply_single' _ rfl 0 n e).symm

theorem CNF_coeff_omega_of_gt {o e : Ordinal} (he : o < ω ^ e) : CNF_coeff_omega o e = 0 := by
  rw [CNF_coeff_omega_eq_iff, Nat.cast_zero, CNF_coeff_of_gt he]

theorem CNF_coeff_omega_opow_mul_of_ge (o x e : Ordinal) :
    CNF_coeff_omega (ω ^ x * o) (x + e) = CNF_coeff_omega o e := by
  rw [CNF_coeff_omega_eq_iff, CNF_coeff_opow_mul_of_ge one_lt_omega, natCast_CNF_coeff_omega]

theorem CNF_coeff_omega_opow_mul_of_lt {e x : Ordinal} (o : Ordinal) (he : e < x) :
    CNF_coeff_omega (ω ^ x * o) e = 0 := by
  rw [CNF_coeff_omega_eq_iff, Nat.cast_zero, CNF_coeff_opow_mul_of_lt one_lt_omega o he]

/-- The function `CNF_coeff_omega (ω ^ x * o)` is the translation of `CNF_coeff_omega o` by `x`. -/
theorem CNF_coeff_omega_opow_mul (o x : Ordinal) :
    (CNF_coeff_omega (ω ^ x * o)).comapDomain (x + ·)
      (fun _ _ _ _ => (add_left_cancel x).1) = CNF_coeff_omega o := by
  ext e
  exact CNF_coeff_omega_opow_mul_of_ge o x e

theorem CNF_coeff_omega_opow_mul_nat {x : Ordinal} (n : ℕ) :
    CNF_coeff_omega (ω ^ x * n) = single x n := by
  ext e
  rw [CNF_coeff_omega_eq_iff, CNF_coeff_opow_mul_of_lt_self one_lt_omega (nat_lt_omega n)]
  exact (apply_single' _ rfl _ _ _).symm

theorem CNF_coeff_omega_opow_mul_add_of_lt {x o₂ e : Ordinal} (o₁ : Ordinal) (ho₂ : o₂ < ω ^ x)
    (he : e < x) : CNF_coeff_omega (ω ^ x * o₁ + o₂) e = CNF_coeff_omega o₂ e := by
  rw [CNF_coeff_omega_eq_iff, CNF_coeff_opow_mul_add_of_lt one_lt_omega o₁ ho₂ he,
    natCast_CNF_coeff_omega]

theorem CNF_coeff_omega_opow_mul_add_of_ge {x o₂ e : Ordinal} (o₁ : Ordinal) (ho₂ : o₂ < ω ^ x)
    (he : x ≤ e) : CNF_coeff_omega (ω ^ x * o₁ + o₂) e = CNF_coeff_omega (ω ^ x * o₁) e := by
  rw [CNF_coeff_omega_eq_iff, CNF_coeff_opow_mul_add_of_ge o₁ ho₂ he, natCast_CNF_coeff_omega]

theorem CNF_coeff_omega_opow_mul_add_apply {x o₂ : Ordinal} (o₁ : Ordinal)
    (ho₂ : o₂ < ω ^ x) (e) : CNF_coeff_omega (ω ^ x * o₁ + o₂) e =
      CNF_coeff_omega (ω ^ x * o₁) e + CNF_coeff_omega o₂ e := by
  rw [CNF_coeff_omega_eq_iff, CNF_coeff_opow_mul_add_apply o₁ ho₂ e, Nat.cast_add,
    natCast_CNF_coeff_omega, natCast_CNF_coeff_omega]

theorem CNF_coeff_omega_opow_mul_add {x o₂ : Ordinal} (o₁ : Ordinal) (ho₂ : o₂ < ω ^ x) :
    CNF_coeff_omega (ω ^ x * o₁ + o₂) = CNF_coeff_omega (ω ^ x * o₁) + CNF_coeff_omega o₂ := by
  ext e
  rw [coe_add, Pi.add_apply, CNF_coeff_omega_opow_mul_add_apply o₁ ho₂]

theorem CNF_coeff_omega_apply_zero (o : Ordinal) : CNF_coeff_omega o 0 = o % ω := by
  rw [natCast_CNF_coeff_omega, CNF_coeff_apply_zero omega_ne_one]

theorem CNF_coeff_omega_apply (o e : Ordinal) : CNF_coeff_omega o e = o / ω ^ e % ω := by
  rw [natCast_CNF_coeff_omega, CNF_coeff_apply one_lt_omega]

theorem CNF_coeff_omega_opow_div_apply (o x e : Ordinal) :
    CNF_coeff_omega (o / ω ^ x) e = CNF_coeff_omega o (x + e) := by
  rw [CNF_coeff_omega_eq_iff, CNF_coeff_opow_div_apply one_lt_omega, natCast_CNF_coeff_omega]

/-- The function `CNF_coeff b (o / b ^ x)` is the translation of `CNF_coeff b o` by `x`. -/
theorem CNF_omega_coeff_opow_div (o x : Ordinal) :
    CNF_coeff_omega (o / ω ^ x) = (CNF_coeff_omega o).comapDomain (x + ·)
      (fun _ _ _ _ => (add_left_cancel x).1) := by
  ext e
  exact CNF_coeff_omega_opow_div_apply o x e

theorem CNF_coeff_omega_mod_opow_of_lt {x e : Ordinal} (o : Ordinal) (he : e < x) :
    CNF_coeff_omega (o % ω ^ x) e = CNF_coeff_omega o e := by
  rw [CNF_coeff_omega_eq_iff, CNF_coeff_mod_opow_of_lt one_lt_omega o he, natCast_CNF_coeff_omega]

theorem CNF_coeff_omega_mod_opow_of_ge {x e : Ordinal} (o : Ordinal) (he : x ≤ e) :
    CNF_coeff_omega (o % ω ^ x) e = 0 := by
  rw [CNF_coeff_omega_eq_iff, Nat.cast_zero, CNF_coeff_mod_opow_of_ge omega_ne_zero o he]

theorem CNF_coeff_omega_add_of_gt {o₂ e : Ordinal} (o₁ : Ordinal) (he : log ω o₂ < e) :
    CNF_coeff_omega (o₁ + o₂) e = CNF_coeff_omega o₁ e := by
  rw [CNF_coeff_omega_eq_iff, CNF_coeff_add_of_gt principal_add_omega o₁ he,
    natCast_CNF_coeff_omega]

theorem CNF_coeff_omega_add_of_eq (o₁ o₂ : Ordinal) : CNF_coeff_omega (o₁ + o₂) (log ω o₂) =
    CNF_coeff_omega o₁ (log ω o₂) + CNF_coeff_omega o₂ (log ω o₂) := by
  rw [CNF_coeff_omega_eq_iff, CNF_coeff_add_of_eq principal_add_omega, Nat.cast_add,
    natCast_CNF_coeff_omega, natCast_CNF_coeff_omega]

theorem CNF_coeff_omega_add_of_eq' {e o₂ : Ordinal} (o₁ : Ordinal) (he : log ω o₂ = e) :
    CNF_coeff_omega (o₁ + o₂) e = CNF_coeff_omega o₁ e + CNF_coeff_omega o₂ e := by
  obtain rfl := he
  exact CNF_coeff_omega_add_of_eq o₁ o₂

theorem CNF_coeff_omega_add_of_lt {o₂ e : Ordinal} (o₁ : Ordinal) (he : e < log ω o₂) :
    CNF_coeff_omega (o₁ + o₂) e = CNF_coeff_omega o₂ e := by
  rw [CNF_coeff_omega_eq_iff, CNF_coeff_add_of_lt principal_add_omega o₁ he,
    natCast_CNF_coeff_omega]

theorem CNF_coeff_omega_opow_mul_add'_apply {x o₂ : Ordinal} (o₁ : Ordinal)
    (ho₂ : o₂ < ω ^ Order.succ x) (e) : CNF_coeff_omega (ω ^ x * o₁ + o₂) e =
      CNF_coeff_omega (ω ^ x * o₁) e + CNF_coeff_omega o₂ e := by
  rw [CNF_coeff_omega_eq_iff, CNF_coeff_opow_mul_add_of_principal_add_apply
    principal_add_omega o₁ ho₂ e, Nat.cast_add, natCast_CNF_coeff_omega, natCast_CNF_coeff_omega]

theorem CNF_coeff_omega_opow_mul_add' {x o₂ : Ordinal} (o₁ : Ordinal)
    (ho₂ : o₂ < ω ^ Order.succ x) : CNF_coeff_omega (ω ^ x * o₁ + o₂) =
      CNF_coeff_omega (ω ^ x * o₁) + CNF_coeff_omega o₂ := by
  ext e
  exact CNF_coeff_omega_opow_mul_add'_apply o₁ ho₂ e

theorem CNF_coeff_omega_opow_add'_apply {x o : Ordinal} (ho₂ : o < ω ^ Order.succ x) (e) :
    CNF_coeff_omega (ω ^ x + o) e = CNF_coeff_omega (ω ^ x) e + CNF_coeff_omega o e := by
  convert CNF_coeff_omega_opow_mul_add'_apply 1 ho₂ e using 1 <;>
  rw [mul_one]

theorem CNF_coeff_omega_opow_add' {x o : Ordinal} (ho₂ : o < ω ^ Order.succ x) :
    CNF_coeff_omega (ω ^ x + o) = CNF_coeff_omega (ω ^ x) + CNF_coeff_omega o := by
  ext e
  exact CNF_coeff_omega_opow_add'_apply ho₂ e

/-! ### Evaluating Cantor normal forms -/


/-- Evaluates a finitely supported function `Ordinal →₀ Ordinal` as a base `b` Cantor normal form.
This is the (left) inverse of `CNF_coeff`. -/
@[pp_nodot]
def CNF_eval (b : Ordinal) (f : Ordinal →₀ Ordinal) : Ordinal :=
  (f.support.sort (· ≥ ·)).foldr (fun e r ↦ b ^ e * f e + r) 0

@[simp]
theorem CNF_eval_zero (b : Ordinal) : CNF_eval b 0 = 0 := by
  rw [CNF_eval]
  simp

@[simp]
theorem CNF_eval_single (b e c : Ordinal) : CNF_eval b (single e c) = b ^ e * c := by
  obtain rfl | hc := eq_or_ne c 0
  · simp
  · rw [CNF_eval, support_single_ne_zero e hc]
    simp

theorem CNF_eval_cons (b : Ordinal) {f : Ordinal →₀ Ordinal} {e : Ordinal} (c : Ordinal)
    (h : ∀ a ∈ f.support, a < e) : CNF_eval b (single e c + f) = b ^ e * c + CNF_eval b f := by
  obtain rfl | hc := eq_or_ne c 0; simp
  have he := fun h' => (h e h').false
  rw [CNF_eval, support_single_add he hc, Finset.sort_insert _ (fun x hx => (h x hx).le) he,
    foldr_cons, coe_add, Pi.add_apply, single_eq_same, not_mem_support_iff.1 he, add_zero,
    add_left_cancel]
  apply foldr_ext
  intro x hx y
  rw [Pi.add_apply, single_eq_of_ne (h x <| (Finset.mem_sort _).1 hx).ne', zero_add]

theorem CNF_eval_list_foldr (b : Ordinal) (f : Ordinal →₀ Ordinal) (l : List Ordinal)
    (hl : l.Sorted (· > ·)) (hf : f.support = l.toFinset) :
    CNF_eval b f = l.foldr (fun e r ↦ b ^ e * f e + r) 0 := by
  rw [CNF_eval, hf, (toFinset_sort _ hl.nodup).2 hl.ge_of_gt]

@[simp]
theorem CNF_eval_CNF_coeff (b o : Ordinal) : CNF_eval b (CNF_coeff b o) = o := by
  rw [CNF_eval_list_foldr b _ _ (CNF_exponents_sorted b o) (support_CNF_coeff b o)]
  conv_rhs => rw [← CNF_foldr b o]
  rw [CNF.exponents, List.keys, foldr_map]
  apply foldr_ext
  intro x hx r
  rw [CNF_coeff_of_mem_CNF hx]

theorem CNF_coeff_injective (b : Ordinal) : Function.Injective (CNF_coeff b) :=
  Function.LeftInverse.injective (CNF_eval_CNF_coeff b)

@[simp]
theorem CNF_coeff_inj {b o₁ o₂ : Ordinal} : CNF_coeff b o₁ = CNF_coeff b o₂ ↔ o₁ = o₂ :=
  (CNF_coeff_injective b).eq_iff

/-- Evaluates a finitely supported function `Ordinal →₀ ℕ` as a base `ω` Cantor normal form.
This is the (two-sided) inverse of `CNF_coeff_omega`. -/
@[pp_nodot]
def CNF_omega_eval (f : Ordinal →₀ ℕ) : Ordinal :=
  CNF_eval ω <| f.mapRange _ Nat.cast_zero

@[simp]
theorem CNF_omega_eval_zero : CNF_omega_eval 0 = 0 := by
  rw [CNF_omega_eval]
  simp

@[simp]
theorem CNF_omega_eval_single (e : Ordinal) (c : ℕ) : CNF_omega_eval (single e c) = ω ^ e * c := by
  rw [CNF_omega_eval, mapRange_single, CNF_eval_single]

theorem CNF_omega_eval_list_foldr (f : Ordinal →₀ ℕ) (l : List Ordinal)
    (hl : l.Sorted (· > ·)) (hf : f.support = l.toFinset) :
    CNF_omega_eval f = l.foldr (fun e r ↦ ω ^ e * f e + r) 0 := by
  rw [CNF_omega_eval, CNF_eval_list_foldr ω _ l hl]
  · rfl
  · rwa [support_mapRange_of_injective _ _ Nat.cast_injective]

@[simp]
theorem CNF_omega_eval_CNF_coeff_omega (o : Ordinal) :
    CNF_omega_eval (CNF_coeff_omega o) = o := by
  rw [CNF_omega_eval, CNF_coeff_omega_mapRange, CNF_eval_CNF_coeff]

theorem CNF_omega_eval_cons {f : Ordinal →₀ ℕ} {e : Ordinal} (c : ℕ) (h : ∀ a ∈ f.support, a < e) :
    CNF_omega_eval (single e c + f) = ω ^ e * c + CNF_omega_eval f := by
  rw [CNF_omega_eval, mapRange_add Nat.cast_add, mapRange_single, CNF_eval_cons, CNF_omega_eval]
  rwa [support_mapRange_of_injective _ _ Nat.cast_injective]

theorem CNF_omega_eval_lt {f : Ordinal →₀ ℕ} {e : Ordinal} :
    (∀ a ∈ f.support, a < e) → CNF_omega_eval f < ω ^ e := by
  apply f.induction_on_max
  · intro
    rw [CNF_omega_eval_zero]
    exact opow_pos e omega_pos
  · intro x c f hf hc IH h
    rw [support_single_add (fun hx => (hf x hx).false) hc] at h
    rw [CNF_omega_eval_cons c hf]
    apply principal_add_omega_opow _ ((omega_opow_mul_nat_lt x c).trans_le _) (IH _)
    · rw [opow_le_opow_iff_right one_lt_omega, Order.succ_le_iff]
      exact h _ (Finset.mem_insert_self x _)
    · intro a ha
      apply h
      apply Finset.mem_insert_of_mem ha

@[simp]
theorem CNF_coeff_omega_CNF_omega_eval (f : Ordinal →₀ ℕ) :
    CNF_coeff_omega (CNF_omega_eval f) = f := by
  apply f.induction_on_max; simp
  intro e c f hf _ IH
  rw [CNF_omega_eval_cons c hf, CNF_coeff_omega_opow_mul_add c (CNF_omega_eval_lt hf),
    CNF_coeff_omega_opow_mul_nat, IH]

theorem CNF_coeff_omega_CNF_omega_eval_apply (f : Ordinal →₀ ℕ) (e : Ordinal) :
    CNF_coeff_omega (CNF_omega_eval f) e = f e := by
  rw [CNF_coeff_omega_CNF_omega_eval]

theorem CNF_coeff_omega_injective : Function.Injective CNF_coeff_omega :=
  Function.LeftInverse.injective CNF_omega_eval_CNF_coeff_omega

theorem CNF_coeff_omega_surjective : Function.Surjective CNF_coeff_omega :=
  Function.RightInverse.surjective CNF_coeff_omega_CNF_omega_eval

theorem CNF_coeff_omega_bijective : Function.Bijective CNF_coeff_omega :=
  ⟨CNF_coeff_omega_injective, CNF_coeff_omega_surjective⟩

@[simp]
theorem CNF_coeff_omega_inj {o₁ o₂ : Ordinal} : CNF_coeff_omega o₁ = CNF_coeff_omega o₂ ↔ o₁ = o₂ :=
  CNF_coeff_omega_injective.eq_iff

theorem CNF_omega_eval_injective : Function.Injective CNF_omega_eval :=
  Function.LeftInverse.injective CNF_coeff_omega_CNF_omega_eval

theorem CNF_omega_eval_surjective : Function.Surjective CNF_omega_eval :=
  Function.RightInverse.surjective CNF_omega_eval_CNF_coeff_omega

theorem CNF_omega_eval_bijective : Function.Bijective CNF_omega_eval :=
  ⟨CNF_omega_eval_injective, CNF_omega_eval_surjective⟩

@[simp]
theorem CNF_omega_eval_inj {f₁ f₂ : Ordinal →₀ ℕ} :
    CNF_omega_eval f₁ = CNF_omega_eval f₂ ↔ f₁ = f₂ :=
  CNF_omega_eval_injective.eq_iff

/-! ### Ordinal XOR -/

/-- The XOR of two ordinals is computed by XOR-ing each pair of corresponding natural coefficients
in the base `ω` Cantor normal form. -/
instance : Xor Ordinal :=
  ⟨fun a b => CNF_omega_eval <| (CNF_coeff_omega a).zipWith _ (Nat.zero_xor 0) (CNF_coeff_omega b)⟩

theorem CNF_coeff_omega_xor (a b e : Ordinal) :
    CNF_coeff_omega (a ^^^ b) e = CNF_coeff_omega a e ^^^ CNF_coeff_omega b e :=
  CNF_coeff_omega_CNF_omega_eval_apply _ e

/-! We port the results from Mathlib.Data.Nat.Bitwise in a mostly one to one manner. -/

@[simp]
protected theorem xor_self (a : Ordinal) : a ^^^ a = 0 := by
  rw [← CNF_coeff_omega_inj]
  ext e
  rw [CNF_coeff_omega_xor, Nat.xor_self, CNF_coeff_omega_zero_apply]

protected theorem xor_comm (a b : Ordinal) : a ^^^ b = b ^^^ a := by
  rw [← CNF_coeff_omega_inj]
  ext e
  rw [CNF_coeff_omega_xor, Nat.xor_comm, CNF_coeff_omega_xor]

protected theorem xor_assoc (a b c : Ordinal) : a ^^^ b ^^^ c = a ^^^ (b ^^^ c) := by
  rw [← CNF_coeff_omega_inj]
  ext e
  rw [CNF_coeff_omega_xor, CNF_coeff_omega_xor, Nat.xor_assoc,
    CNF_coeff_omega_xor, CNF_coeff_omega_xor]

@[simp]
protected theorem zero_xor (a : Ordinal) : 0 ^^^ a = a := by
  rw [← CNF_coeff_omega_inj]
  ext e
  rw [CNF_coeff_omega_xor, CNF_coeff_omega_zero_apply, Nat.zero_xor]

@[simp]
protected theorem xor_zero (a : Ordinal) : a ^^^ 0 = a := by
  rw [Ordinal.xor_comm, Ordinal.zero_xor]

protected theorem xor_cancel_right (a b : Ordinal) : b ^^^ a ^^^ a = b := by
  rw [Ordinal.xor_assoc, Ordinal.xor_self, Ordinal.xor_zero]

protected theorem xor_cancel_left (a b : Ordinal) : a ^^^ (a ^^^ b) = b := by
  rw [← Ordinal.xor_assoc, Ordinal.xor_self, Ordinal.zero_xor]

protected theorem xor_right_injective (a : Ordinal) : Function.Injective (a ^^^ ·) := by
  intro b c h
  dsimp at h
  rw [← Ordinal.xor_cancel_left a b, h, Ordinal.xor_cancel_left]

protected theorem xor_left_injective (a : Ordinal) : Function.Injective (· ^^^ a) := by
  intro b c h
  dsimp at h
  rw [← Ordinal.xor_cancel_right a b, h, Ordinal.xor_cancel_right]

@[simp]
protected theorem xor_right_inj {a b c : Ordinal} : a ^^^ b = a ^^^ c ↔ b = c :=
  (Ordinal.xor_right_injective a).eq_iff

@[simp]
protected theorem xor_left_inj {a b c : Ordinal} : b ^^^ a = c ^^^ a ↔ b = c :=
  (Ordinal.xor_left_injective a).eq_iff

@[simp]
protected theorem xor_eq_zero {a b : Ordinal} : a ^^^ b = 0 ↔ a = b := by
  rw [← Ordinal.xor_self b, Ordinal.xor_left_inj]

protected theorem xor_ne_zero {a b : Ordinal} : a ^^^ b ≠ 0 ↔ a ≠ b := 
  Ordinal.xor_eq_zero.not

end Ordinal
