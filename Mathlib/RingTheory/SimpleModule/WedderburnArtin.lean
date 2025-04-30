/-
Copyright (c) 2025 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.RingTheory.FiniteLength
import Mathlib.RingTheory.SimpleModule.Isotypic
import Mathlib.RingTheory.SimpleRing.Congr
import Mathlib.RingTheory.SimpleRing.Matrix

/-!
# Wedderburn-Artin Theorem
-/

universe u
variable (R₀ : Type*) {R : Type u} [CommSemiring R₀] [Ring R] [Algebra R₀ R]

/-- A simple ring is semisimple iff it is artinian, iff it has a minimal left ideal. -/
theorem IsSimpleRing.tfae [IsSimpleRing R] : List.TFAE
    [IsSemisimpleRing R, IsArtinianRing R, ∃ I : Ideal R, IsAtom I] := by
  tfae_have 1 → 2 := fun _ ↦ inferInstance
  tfae_have 2 → 3 := fun _ ↦ IsAtomic.exists_atom _
  tfae_have 3 → 1 := fun ⟨I, hI⟩ ↦ by
    have ⟨_, h⟩ := isSimpleRing_iff_isTwoSided_imp.mp ‹IsSimpleRing R›
    simp_rw [← isFullyInvariant_iff_isTwoSided] at h
    have := isSimpleModule_iff_isAtom.mpr hI
    obtain eq | eq := h _ (.isotypicComponent R R I)
    · exact (hI.bot_lt.not_le <| (le_sSup <| by exact ⟨.refl ..⟩).trans_eq eq).elim
    exact .congr (.symm <| .trans (.ofEq _ _ eq) Submodule.topEquiv)
  tfae_finish

theorem IsSimpleRing.isSemisimpleRing_iff_isArtinianRing [IsSimpleRing R] :
    IsSemisimpleRing R ↔ IsArtinianRing R := tfae.out 0 1

theorem isSimpleRing_isArtinianRing_iff :
    IsSimpleRing R ∧ IsArtinianRing R ↔ IsSemisimpleRing R ∧ IsIsotypic R R ∧ Nontrivial R := by
  refine ⟨fun ⟨_, _⟩ ↦ ?_, fun ⟨_, _, _⟩ ↦ ?_⟩
  on_goal 1 => have := IsSimpleRing.isSemisimpleRing_iff_isArtinianRing.mpr ‹_›
  all_goals simp_rw [isIsotypic_iff_isFullyInvariant_imp_bot_or_top,
      isFullyInvariant_iff_isTwoSided, isSimpleRing_iff_isTwoSided_imp] at *
  · exact ⟨this, by rwa [and_comm]⟩
  · exact ⟨⟨‹_›, ‹_›⟩, inferInstance⟩

namespace IsSimpleRing

variable (R) [IsSimpleRing R] [IsArtinianRing R]

instance (priority := low) : IsSemisimpleRing R :=
  (isSimpleRing_isArtinianRing_iff.mp ⟨‹_›, ‹_›⟩).1

theorem isIsotypic (M) [AddCommGroup M] [Module R M] : IsIsotypic R M :=
  (isSimpleRing_isArtinianRing_iff.mp ⟨‹_›, ‹_›⟩).2.1.of_self M

theorem exists_ringEquiv_matrix_end_mulOpposite :
    ∃ (n : ℕ) (_ : NeZero n) (I : Ideal R) (_ : IsSimpleModule R I),
      Nonempty (R ≃+* Matrix (Fin n) (Fin n) (Module.End R I)ᵐᵒᵖ) := by
  have ⟨n, hn, S, hS, ⟨e⟩⟩ := (isIsotypic R R).linearEquiv_fun
  refine ⟨n, hn, S, hS, ⟨.trans (.opOp R) <| .trans (.op ?_) (.symm .mopMatrix)⟩⟩
  exact .trans (.moduleEndSelf R) <| .trans e.conjRingEquiv (endVecRingEquivMatrixEnd ..)

theorem exists_ringEquiv_matrix_divisionRing :
    ∃ (n : ℕ) (_ : NeZero n) (D : Type u) (_ : DivisionRing D),
      Nonempty (R ≃+* Matrix (Fin n) (Fin n) D) := by
  have ⟨n, hn, I, _, ⟨e⟩⟩ := exists_ringEquiv_matrix_end_mulOpposite R
  classical exact ⟨n, hn, _, _, ⟨e⟩⟩

theorem exists_algEquiv_matrix_end_mulOpposite :
    ∃ (n : ℕ) (_ : NeZero n) (I : Ideal R) (_ : IsSimpleModule R I),
      Nonempty (R ≃ₐ[R₀] Matrix (Fin n) (Fin n) (Module.End R I)ᵐᵒᵖ) := by
  have ⟨n, hn, S, hS, ⟨e⟩⟩ := (isIsotypic R R).linearEquiv_fun
  refine ⟨n, hn, S, hS, ⟨.trans (.opOp R₀ R) <| .trans (.op ?_) (.symm .mopMatrix)⟩⟩
  exact .trans (.moduleEndSelf R₀) <| .trans (e.algConj R₀) (endVecAlgEquivMatrixEnd ..)

theorem exists_algEquiv_matrix_divisionRing :
    ∃ (n : ℕ) (_ : NeZero n) (D : Type u) (_ : DivisionRing D) (_ : Algebra R₀ D),
      Nonempty (R ≃ₐ[R₀] Matrix (Fin n) (Fin n) D) := by
  have ⟨n, hn, I, _, ⟨e⟩⟩ := exists_algEquiv_matrix_end_mulOpposite R₀ R
  classical exact ⟨n, hn, _, _, _, ⟨e⟩⟩

theorem exists_algEquiv_matrix_divisionRing_finite [Module.Finite R₀ R] :
    ∃ (n : ℕ) (_ : NeZero n) (D : Type u) (_ : DivisionRing D) (_ : Algebra R₀ D)
      (_ : Module.Finite R₀ D), Nonempty (R ≃ₐ[R₀] Matrix (Fin n) (Fin n) D) := by
  have ⟨n, hn, I, _, ⟨e⟩⟩ := exists_algEquiv_matrix_end_mulOpposite R₀ R
  have := Module.Finite.equiv e.toLinearEquiv
  classical exact ⟨n, hn, _, _, _, .of_surjective
    (Matrix.entryLinearMap R₀ _ (0 : Fin n) (0 : Fin n)) fun f ↦ ⟨fun _ _ ↦ f, rfl⟩, ⟨e⟩⟩

end IsSimpleRing

namespace IsSemisimpleModule

open Module (End)

universe v
variable (R) (M : Type v) [AddCommGroup M] [Module R₀ M] [Module R M] [IsScalarTower R₀ R M]
  [IsSemisimpleModule R M] [Module.Finite R M]

theorem exists_end_algEquiv_pi_matrix_end :
    ∃ (n : ℕ) (S : Fin n → Submodule R M) (d : Fin n → ℕ),
      (∀ i, IsSimpleModule R (S i)) ∧ (∀ i, NeZero (d i)) ∧
      Nonempty (End R M ≃ₐ[R₀] Π i, Matrix (Fin (d i)) (Fin (d i)) (End R (S i))) := by
  choose d pos S _ simple e using fun c : isotypicComponents R M ↦
    (IsIsotypic.isotypicComponents c.2).submodule_linearEquiv_fun
  classical exact ⟨_, _, _, fun _ ↦ simple _, fun _ ↦ pos _, ⟨.trans (endAlgEquiv R₀ R M) <| .trans
    (.piCongrRight fun c ↦ ((e c).some.algConj R₀).trans (endVecAlgEquivMatrixEnd ..)) <|
    (.piCongrLeft' R₀ _ (Finite.equivFin _))⟩⟩

theorem exists_end_ringEquiv_pi_matrix_end :
    ∃ (n : ℕ) (S : Fin n → Submodule R M) (d : Fin n → ℕ),
      (∀ i, IsSimpleModule R (S i)) ∧ (∀ i, NeZero (d i)) ∧
      Nonempty (End R M ≃+* Π i, Matrix (Fin (d i)) (Fin (d i)) (End R (S i))) :=
  have ⟨n, S, d, hS, hd, ⟨e⟩⟩ := exists_end_algEquiv_pi_matrix_end ℕ R M; ⟨n, S, d, hS, hd, ⟨e⟩⟩

-- TODO: can also require D be in `Type u`, since every simple module is the quotient by an ideal.
theorem exists_end_algEquiv_pi_matrix_divisionRing :
    ∃ (n : ℕ) (D : Fin n → Type v) (d : Fin n → ℕ) (_ : ∀ i, DivisionRing (D i))
      (_ : ∀ i, Algebra R₀ (D i)), (∀ i, NeZero (d i)) ∧
      Nonempty (End R M ≃ₐ[R₀] Π i, Matrix (Fin (d i)) (Fin (d i)) (D i)) := by
  have ⟨n, S, d, _, hd, ⟨e⟩⟩ := exists_end_algEquiv_pi_matrix_end R₀ R M
  classical exact ⟨n, _, d, inferInstance, inferInstance, hd, ⟨e⟩⟩

theorem exists_end_ringEquiv_pi_matrix_divisionRing :
    ∃ (n : ℕ) (D : Fin n → Type v) (d : Fin n → ℕ) (_ : ∀ i, DivisionRing (D i)),
      (∀ i, NeZero (d i)) ∧ Nonempty (End R M ≃+* Π i, Matrix (Fin (d i)) (Fin (d i)) (D i)) :=
  have ⟨n, D, d, _, _, hd, ⟨e⟩⟩ := exists_end_algEquiv_pi_matrix_divisionRing ℕ R M
  ⟨n, D, d, _, hd, ⟨e⟩⟩

theorem _root_.IsSemisimpleRing.moduleEnd : IsSemisimpleRing (Module.End R M) :=
  have ⟨_, _, _, _, _, ⟨e⟩⟩ := exists_end_ringEquiv_pi_matrix_divisionRing R M
  e.symm.isSemisimpleRing

end IsSemisimpleModule

namespace IsSemisimpleRing

variable (R) [IsSemisimpleRing R]

theorem exists_algEquiv_pi_matrix_end_mulOpposite :
    ∃ (n : ℕ) (S : Fin n → Ideal R) (d : Fin n → ℕ),
      (∀ i, IsSimpleModule R (S i)) ∧ (∀ i, NeZero (d i)) ∧
      Nonempty (R ≃ₐ[R₀] Π i, Matrix (Fin (d i)) (Fin (d i)) (Module.End R (S i))ᵐᵒᵖ) :=
  have ⟨n, S, d, hS, hd, ⟨e⟩⟩ := IsSemisimpleModule.exists_end_algEquiv_pi_matrix_end R₀ R R
  ⟨n, S, d, hS, hd, ⟨.trans (.opOp R₀ R) <| .trans (.op <| .trans (.moduleEndSelf R₀) e) <|
    .trans (.piMulOpposite _ _) (.piCongrRight fun _ ↦ .symm .mopMatrix)⟩⟩

theorem exists_algEquiv_pi_matrix_divisionRing :
    ∃ (n : ℕ) (D : Fin n → Type u) (d : Fin n → ℕ) (_ : ∀ i, DivisionRing (D i))
      (_ : ∀ i, Algebra R₀ (D i)), (∀ i, NeZero (d i)) ∧
      Nonempty (R ≃ₐ[R₀] Π i, Matrix (Fin (d i)) (Fin (d i)) (D i)) := by
  have ⟨n, S, d, _, hd, ⟨e⟩⟩ := exists_algEquiv_pi_matrix_end_mulOpposite R₀ R
  classical exact ⟨n, _, d, inferInstance, inferInstance, hd, ⟨e⟩⟩

theorem exists_algEquiv_pi_matrix_divisionRing_finite [Module.Finite R₀ R] :
    ∃ (n : ℕ) (D : Fin n → Type u) (d : Fin n → ℕ) (_ : ∀ i, DivisionRing (D i))
      (_ : ∀ i, Algebra R₀ (D i)) (_ : ∀ i, Module.Finite R₀ (D i)), (∀ i, NeZero (d i)) ∧
      Nonempty (R ≃ₐ[R₀] Π i, Matrix (Fin (d i)) (Fin (d i)) (D i)) := by
  have ⟨n, D, d, _, _, hd, ⟨e⟩⟩ := exists_algEquiv_pi_matrix_divisionRing R₀ R
  have := Module.Finite.equiv e.toLinearEquiv
  refine ⟨n, D, d, _, _, fun i ↦ ?_, hd, ⟨e⟩⟩
  let l := Matrix.entryLinearMap R₀ (D i) 0 0 ∘ₗ
    .proj (φ := fun i ↦ Matrix (Fin (d i)) (Fin (d i)) _) i
  exact .of_surjective l fun x ↦ ⟨fun j _ _ ↦ Function.update (fun _ ↦ 0) i x j, by simp [l]⟩

theorem exists_ringEquiv_pi_matrix_end_mulOpposite :
    ∃ (n : ℕ) (D : Fin n → Ideal R) (d : Fin n → ℕ),
      (∀ i, IsSimpleModule R (D i)) ∧ (∀ i, NeZero (d i)) ∧
      Nonempty (R ≃+* Π i, Matrix (Fin (d i)) (Fin (d i)) (Module.End R (D i))ᵐᵒᵖ) :=
  have ⟨n, S, d, hS, hd, ⟨e⟩⟩ := exists_algEquiv_pi_matrix_end_mulOpposite ℕ R
  ⟨n, S, d, hS, hd, ⟨e⟩⟩

theorem exists_ringEquiv_pi_matrix_divisionRing :
    ∃ (n : ℕ) (D : Fin n → Type u) (d : Fin n → ℕ) (_ : ∀ i, DivisionRing (D i)),
      (∀ i, NeZero (d i)) ∧ Nonempty (R ≃+* Π i, Matrix (Fin (d i)) (Fin (d i)) (D i)) :=
  have ⟨n, D, d, _, _, hd, ⟨e⟩⟩ := exists_algEquiv_pi_matrix_divisionRing ℕ R
  ⟨n, D, d, _, hd, ⟨e⟩⟩

instance (n) [Fintype n] [DecidableEq n] : IsSemisimpleRing (Matrix n n R) :=
  (isEmpty_or_nonempty n).elim (fun _ ↦ inferInstance) fun _ ↦
    have ⟨_, _, _, _, _, ⟨e⟩⟩ := exists_ringEquiv_pi_matrix_divisionRing R
    (e.mapMatrix (m := n).trans Matrix.piRingEquiv).symm.isSemisimpleRing

instance [IsSemisimpleRing R] : IsSemisimpleRing Rᵐᵒᵖ :=
  have ⟨_, _, _, _, _, ⟨e⟩⟩ := exists_ringEquiv_pi_matrix_divisionRing R
  ((e.op.trans (.piMulOpposite _)).trans (.piCongrRight fun _ ↦ .symm .mopMatrix)).symm
    |>.isSemisimpleRing

end IsSemisimpleRing

theorem isSemisimpleRing_mulOpposite_iff : IsSemisimpleRing Rᵐᵒᵖ ↔ IsSemisimpleRing R :=
  ⟨fun _ ↦ (RingEquiv.opOp R).symm.isSemisimpleRing, fun _ ↦ inferInstance⟩

/-- The existence part of the Artin–Wedderburn theorem. -/
theorem isSemisimpleRing_iff_pi_matrix_divisionRing : IsSemisimpleRing R ↔
    ∃ (n : ℕ) (D : Fin n → Type u) (d : Fin n → ℕ) (_ : Π i, DivisionRing (D i)),
      Nonempty (R ≃+* Π i, Matrix (Fin (d i)) (Fin (d i)) (D i)) where
  mp _ := have ⟨n, D, d, _, _, e⟩ := IsSemisimpleRing.exists_ringEquiv_pi_matrix_divisionRing R
    ⟨n, D, d, _, e⟩
  mpr := fun ⟨_, _, _, _, ⟨e⟩⟩ ↦ e.symm.isSemisimpleRing

-- Need left-right symmetry of Jacobson radical
proof_wanted IsSemiprimaryRing.mulOpposite [IsSemiprimaryRing R] : IsSemiprimaryRing Rᵐᵒᵖ

proof_wanted isSemiprimaryRing_mulOpposite_iff : IsSemiprimaryRing Rᵐᵒᵖ ↔ IsSemiprimaryRing R

-- A left Artinian ring is right Noetherian iff it is right Artinian. To be left as an `example`.
proof_wanted IsArtinianRing.isNoetherianRing_iff_isArtinianRing_mulOpposite
    [IsArtinianRing R] : IsNoetherianRing Rᵐᵒᵖ ↔ IsArtinianRing Rᵐᵒᵖ
