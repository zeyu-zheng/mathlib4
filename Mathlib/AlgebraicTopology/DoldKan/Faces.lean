import Mathlib.Tactic.Have
/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.AlgebraicTopology.DoldKan.Homotopies
import Mathlib.Tactic.Ring

/-!

# Study of face maps for the Dold-Kan correspondence

In this file, we obtain the technical lemmas that are used in the file
`Projections.lean` in order to get basic properties of the endomorphisms
`P q : K[X] ⟶ K[X]` with respect to face maps (see `Homotopies.lean` for the
role of these endomorphisms in the overall strategy of proof).

The main lemma in this file is `HigherFacesVanish.induction`. It is based
on two technical lemmas `HigherFacesVanish.comp_Hσ_eq` and
`HigherFacesVanish.comp_Hσ_eq_zero`.

(See `Equivalence.lean` for the general strategy of proof of the Dold-Kan equivalence.)

-/


open CategoryTheory CategoryTheory.Limits CategoryTheory.Category
  CategoryTheory.Preadditive CategoryTheory.SimplicialObject Simplicial

namespace AlgebraicTopology

namespace DoldKan

variable {C : Type*} [Category C] [Preadditive C]
variable {X : SimplicialObject C}

/-- A morphism `φ : Y ⟶ X _[n+1]` satisfies `HigherFacesVanish q φ`
when the compositions `φ ≫ X.δ j` are `0` for `j ≥ max 1 (n+2-q)`. When `q ≤ n+1`,
it basically means that the composition `φ ≫ X.δ j` are `0` for the `q` highest
possible values of a nonzero `j`. Otherwise, when `q ≥ n+2`, all the compositions
`φ ≫ X.δ j` for nonzero `j` vanish. See also the lemma `comp_P_eq_self_iff` in
`Projections.lean` which states that `HigherFacesVanish q φ` is equivalent to
the identity `φ ≫ (P q).f (n+1) = φ`. -/
def HigherFacesVanish {Y : C} {n : ℕ} (q : ℕ) (φ : Y ⟶ X _[n + 1]) : Prop :=
  ∀ j : Fin (n + 1), n + 1 ≤ (j : ℕ) + q → φ ≫ X.δ j.succ = 0

namespace HigherFacesVanish

@[reassoc]
theorem comp_δ_eq_zero {Y : C} {n : ℕ} {q : ℕ} {φ : Y ⟶ X _[n + 1]} (v : HigherFacesVanish q φ)
    (j : Fin (n + 2)) (hj₁ : j ≠ 0) (hj₂ : n + 2 ≤ (j : ℕ) + q) : φ ≫ X.δ j = 0 := by
  obtain ⟨i, rfl⟩ := Fin.eq_succ_of_ne_zero hj₁
  apply v i
  simp only [Fin.val_succ] at hj₂
  omega

theorem of_succ {Y : C} {n q : ℕ} {φ : Y ⟶ X _[n + 1]} (v : HigherFacesVanish (q + 1) φ) :
    HigherFacesVanish q φ := fun j hj => v j (by simpa only [← add_assoc] using le_add_right hj)

theorem of_comp {Y Z : C} {q n : ℕ} {φ : Y ⟶ X _[n + 1]} (v : HigherFacesVanish q φ) (f : Z ⟶ Y) :
    HigherFacesVanish q (f ≫ φ) := fun j hj => by rw [assoc, v j hj, comp_zero]

theorem comp_Hσ_eq {Y : C} {n a q : ℕ} {φ : Y ⟶ X _[n + 1]} (v : HigherFacesVanish q φ)
    (hnaq : n = a + q) :
    φ ≫ (Hσ q).f (n + 1) =
      -φ ≫ X.δ ⟨a + 1, Nat.succ_lt_succ (Nat.lt_succ_iff.mpr (Nat.le.intro hnaq.symm))⟩ ≫
        X.σ ⟨a, Nat.lt_succ_iff.mpr (Nat.le.intro hnaq.symm)⟩ := by
  have hnaq_shift : ∀ d : ℕ, n + d = a + d + q
  intro d
  rw [add_assoc, add_comm d, ← add_assoc, hnaq]
  rw [Hσ, Homotopy.nullHomotopicMap'_f (c_mk (n + 2) (n + 1) rfl) (c_mk (n + 1) n rfl),
    hσ'_eq hnaq (c_mk (n + 1) n rfl), hσ'_eq (hnaq_shift 1) (c_mk (n + 2) (n + 1) rfl)]
  simp only [AlternatingFaceMapComplex.obj_d_eq, eqToHom_refl, comp_id, comp_sum, sum_comp,
    comp_add]
  simp only [comp_zsmul, zsmul_comp, ← assoc, ← mul_zsmul]
  -- cleaning up the first sum
  rw [← Fin.sum_congr' _ (hnaq_shift 2).symm, Fin.sum_trunc]
  swap
  rintro ⟨k, hk⟩
  suffices φ ≫ X.δ (⟨a + 2 + k, by omega⟩ : Fin (n + 2)) = 0 by
    simp only [this, Fin.natAdd_mk, Fin.cast_mk, zero_comp, smul_zero]
  convert v ⟨a + k + 1, by omega⟩ (by rw [Fin.val_mk]; omega)
  dsimp
  omega
  -- cleaning up the second sum
  rw [← Fin.sum_congr' _ (hnaq_shift 3).symm, @Fin.sum_trunc _ _ (a + 3)]
  swap
  rintro ⟨k, hk⟩
  rw [assoc, X.δ_comp_σ_of_gt', v.comp_δ_eq_zero_assoc, zero_comp, zsmul_zero]
  simp only [Fin.lt_iff_val_lt_val]
  dsimp [Fin.natAdd, Fin.cast]
  omega
  intro h
  rw [Fin.pred_eq_iff_eq_succ, Fin.ext_iff] at h
  dsimp [Fin.cast] at h
  omega
  dsimp [Fin.cast, Fin.pred]
  rw [Nat.add_right_comm, Nat.add_sub_assoc (by norm_num : 1 ≤ 3)]
  omega
  simp only [assoc]
  conv_lhs =>
    congr
    · rw [Fin.sum_univ_castSucc]
    rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
  dsimp [Fin.cast, Fin.castLE, Fin.castLT]
  /- the purpose of the following `simplif` is to create three subgoals in order
      to finish the proof -/
  have simplif :
    ∀ a b c d e f : Y ⟶ X _[n + 1], b = f → d + e = 0 → c + a = 0 → a + b + (c + d + e) = f := by
    intro a b c d e f h1 h2 h3
    rw [add_assoc c d e, h2, add_zero, add_comm a, add_assoc, add_comm a, h3, add_zero, h1]
  apply simplif
  -- b = f
  rw [← pow_add, Odd.neg_one_pow, neg_smul, one_zsmul]
  exact ⟨a, by omega⟩
  -- d + e = 0
  rw [X.δ_comp_σ_self' (Fin.castSucc_mk _ _ _).symm,
    X.δ_comp_σ_succ' (Fin.succ_mk _ _ _).symm]
  simp only [comp_id, pow_add _ (a + 1) 1, pow_one, mul_neg, mul_one, neg_mul, neg_smul,
    add_right_neg]
  -- c + a = 0
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  rintro ⟨i, hi⟩ _
  simp only
  have hia : (⟨i, by omega⟩ : Fin (n + 2)) ≤
      Fin.castSucc (⟨a, by omega⟩ : Fin (n + 1)) := by
    rw [Fin.le_iff_val_le_val]
    dsimp
    omega
  erw [δ_comp_σ_of_le X hia, add_eq_zero_iff_eq_neg, ← neg_zsmul]
  congr 2
  ring

theorem comp_Hσ_eq_zero {Y : C} {n q : ℕ} {φ : Y ⟶ X _[n + 1]} (v : HigherFacesVanish q φ)
    (hqn : n < q) : φ ≫ (Hσ q).f (n + 1) = 0 := by
  simp only [Hσ, Homotopy.nullHomotopicMap'_f (c_mk (n + 2) (n + 1) rfl) (c_mk (n + 1) n rfl)]
  rw [hσ'_eq_zero hqn (c_mk (n + 1) n rfl), comp_zero, zero_add]
  by_cases hqn' : n + 1 < q
  rw [hσ'_eq_zero hqn' (c_mk (n + 2) (n + 1) rfl), zero_comp, comp_zero]
  simp only [hσ'_eq (show n + 1 = 0 + q by omega) (c_mk (n + 2) (n + 1) rfl), pow_zero,
    Fin.mk_zero, one_zsmul, eqToHom_refl, comp_id, comp_sum,
    AlternatingFaceMapComplex.obj_d_eq]
  rw [← Fin.sum_congr' _ (show 2 + (n + 1) = n + 1 + 2 by omega), Fin.sum_trunc]
  simp only [Fin.sum_univ_castSucc, Fin.sum_univ_zero, zero_add, Fin.last, Fin.castLE_mk,
    Fin.cast_mk, Fin.castSucc_mk]
  simp only [Fin.mk_zero, Fin.val_zero, pow_zero, one_zsmul, Fin.mk_one, Fin.val_one, pow_one,
    neg_smul, comp_neg]
  erw [δ_comp_σ_self, δ_comp_σ_succ, add_right_neg]
  intro j
  dsimp [Fin.cast, Fin.castLE, Fin.castLT]
  rw [comp_zsmul, comp_zsmul, δ_comp_σ_of_gt', v.comp_δ_eq_zero_assoc, zero_comp, zsmul_zero]
  simp only [Fin.lt_iff_val_lt_val]
  dsimp [Fin.succ]
  omega
  intro h
  simp only [Fin.pred, Fin.subNat, Fin.ext_iff, Nat.succ_add_sub_one,
    Fin.val_zero, add_eq_zero, false_and] at h
  simp only [Fin.pred, Fin.subNat, Nat.pred_eq_sub_one, Nat.succ_add_sub_one]
  omega

theorem induction {Y : C} {n q : ℕ} {φ : Y ⟶ X _[n + 1]} (v : HigherFacesVanish q φ) :
    HigherFacesVanish (q + 1) (φ ≫ (𝟙 _ + Hσ q).f (n + 1)) := by
  intro j hj₁
  dsimp
  simp only [comp_add, add_comp, comp_id]
  -- when n < q, the result follows immediately from the assumption
  by_cases hqn : n < q
  rw [v.comp_Hσ_eq_zero hqn, zero_comp, add_zero, v j (by omega)]
  -- we now assume that n≥q, and write n=a+q
  cases' Nat.le.dest (not_lt.mp hqn) with a ha
  rw [v.comp_Hσ_eq (show n = a + q by omega), neg_comp, add_neg_eq_zero, assoc, assoc]
  cases' n with m hm
  -- the boundary case n=0
  simp only [Nat.eq_zero_of_add_eq_zero_left ha, Fin.eq_zero j, Fin.mk_zero, Fin.mk_one,
    δ_comp_σ_succ, comp_id]
  rfl
  -- in the other case, we need to write n as m+1
  -- then, we first consider the particular case j = a
  by_cases hj₂ : a = (j : ℕ)
  simp only [hj₂, Fin.eta, δ_comp_σ_succ, comp_id]
  rfl
  -- now, we assume j ≠ a (i.e. a < j)
  have haj : a < j := (Ne.le_iff_lt hj₂).mp (by omega)
  have ham : a ≤ m
  by_contra h
  rw [not_le, ← Nat.succ_le_iff] at h
  omega
  rw [X.δ_comp_σ_of_gt', j.pred_succ]
  swap
  rw [Fin.lt_iff_val_lt_val]
  simpa only [Fin.val_mk, Fin.val_succ, add_lt_add_iff_right] using haj
  obtain _ | ham'' := ham.lt_or_eq
  -- case where `a<m`
  rw [← X.δ_comp_δ''_assoc]
  swap
  rw [Fin.le_iff_val_le_val]
  dsimp
  linarith
  simp only [← assoc, v j (by omega), zero_comp]
  -- in the last case, a=m, q=1 and j=a+1
  rw [X.δ_comp_δ_self'_assoc]
  swap
  ext
  cases j
  dsimp
  dsimp only [Nat.succ_eq_add_one] at *
  omega
  simp only [← assoc, v j (by omega), zero_comp]

end HigherFacesVanish

end DoldKan

end AlgebraicTopology
