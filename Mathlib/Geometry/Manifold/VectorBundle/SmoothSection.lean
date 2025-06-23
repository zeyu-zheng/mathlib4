import Mathlib.Tactic.Have
/-
Copyright (c) 2023 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth, Floris van Doorn
-/
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Topology.ContinuousFunction.Basic
import Mathlib.Geometry.Manifold.Algebra.LieGroup

/-!
# Smooth sections

In this file we define the type `ContMDiffSection` of `n` times continuously differentiable
sections of a smooth vector bundle over a manifold `M` and prove that it's a module.
-/


open Bundle Filter Function

open scoped Bundle Manifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H : Type*}
  [TopologicalSpace H] {H' : Type*} [TopologicalSpace H'] (I : ModelWithCorners 𝕜 E H)
  (I' : ModelWithCorners 𝕜 E' H') {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {M' : Type*}
  [TopologicalSpace M'] [ChartedSpace H' M'] {E'' : Type*} [NormedAddCommGroup E'']
  [NormedSpace 𝕜 E''] {H'' : Type*} [TopologicalSpace H''] {I'' : ModelWithCorners 𝕜 E'' H''}
  {M'' : Type*} [TopologicalSpace M''] [ChartedSpace H'' M''] [SmoothManifoldWithCorners I M]

variable (F : Type*) [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  -- `F` model fiber
  (n : ℕ∞)
  (V : M → Type*) [TopologicalSpace (TotalSpace F V)]
  -- `V` vector bundle
  [∀ x, AddCommGroup (V x)]
  [∀ x, Module 𝕜 (V x)]

variable [∀ x : M, TopologicalSpace (V x)] [FiberBundle F V] [VectorBundle 𝕜 F V]
  [SmoothVectorBundle F V I]

/-- Bundled `n` times continuously differentiable sections of a vector bundle. -/
structure ContMDiffSection where
  /-- the underlying function of this section -/
  protected toFun : ∀ x, V x
  /-- proof that this section is `C^n` -/
  protected contMDiff_toFun : ContMDiff I (I.prod 𝓘(𝕜, F)) n fun x ↦
    TotalSpace.mk' F x (toFun x)

/-- Bundled smooth sections of a vector bundle. -/
abbrev SmoothSection :=
  ContMDiffSection I F ⊤ V

@[inherit_doc] scoped[Manifold] notation "Cₛ^" n "⟮" I "; " F ", " V "⟯" => ContMDiffSection I F n V

namespace ContMDiffSection

variable {I} {I'} {n} {F} {V}

instance : DFunLike Cₛ^n⟮I; F, V⟯ M V where
  coe := ContMDiffSection.toFun
  coe_injective' := by rintro ⟨⟩ ⟨⟩ h; congr

variable {s t : Cₛ^n⟮I; F, V⟯}

@[simp]
theorem coeFn_mk (s : ∀ x, V x)
    (hs : ContMDiff I (I.prod 𝓘(𝕜, F)) n fun x => TotalSpace.mk x (s x)) :
    (mk s hs : ∀ x, V x) = s :=
  rfl

protected theorem contMDiff (s : Cₛ^n⟮I; F, V⟯) :
    ContMDiff I (I.prod 𝓘(𝕜, F)) n fun x => TotalSpace.mk' F x (s x : V x) :=
  s.contMDiff_toFun

protected theorem smooth (s : Cₛ^∞⟮I; F, V⟯) :
    Smooth I (I.prod 𝓘(𝕜, F)) fun x => TotalSpace.mk' F x (s x : V x) :=
  s.contMDiff_toFun

protected theorem mdifferentiable' (s : Cₛ^n⟮I; F, V⟯) (hn : 1 ≤ n) :
    MDifferentiable I (I.prod 𝓘(𝕜, F)) fun x => TotalSpace.mk' F x (s x : V x) :=
  s.contMDiff.mdifferentiable hn

protected theorem mdifferentiable (s : Cₛ^∞⟮I; F, V⟯) :
    MDifferentiable I (I.prod 𝓘(𝕜, F)) fun x => TotalSpace.mk' F x (s x : V x) :=
  s.contMDiff.mdifferentiable le_top

protected theorem mdifferentiableAt (s : Cₛ^∞⟮I; F, V⟯) {x} :
    MDifferentiableAt I (I.prod 𝓘(𝕜, F)) (fun x => TotalSpace.mk' F x (s x : V x)) x :=
  s.mdifferentiable x

theorem coe_inj ⦃s t : Cₛ^n⟮I; F, V⟯⦄ (h : (s : ∀ x, V x) = t) : s = t :=
  DFunLike.ext' h

theorem coe_injective : Injective ((↑) : Cₛ^n⟮I; F, V⟯ → ∀ x, V x) :=
  coe_inj

@[ext]
theorem ext (h : ∀ x, s x = t x) : s = t := DFunLike.ext _ _ h

instance instAdd : Add Cₛ^n⟮I; F, V⟯ := by
  refine ⟨fun s t => ⟨s + t, ?_⟩⟩
  intro x₀
  have hs := s.contMDiff x₀
  have ht := t.contMDiff x₀
  rw [contMDiffAt_section] at hs ht ⊢
  set e := trivializationAt F V x₀
  refine (hs.add ht).congr_of_eventuallyEq ?_
  refine eventually_of_mem (e.open_baseSet.mem_nhds <| mem_baseSet_trivializationAt F V x₀) ?_
  intro x hx
  apply (e.linear 𝕜 hx).1

@[simp]
theorem coe_add (s t : Cₛ^n⟮I; F, V⟯) : ⇑(s + t) = ⇑s + t :=
  rfl

instance instSub : Sub Cₛ^n⟮I; F, V⟯ := by
  refine ⟨fun s t => ⟨s - t, ?_⟩⟩
  intro x₀
  have hs := s.contMDiff x₀
  have ht := t.contMDiff x₀
  rw [contMDiffAt_section] at hs ht ⊢
  set e := trivializationAt F V x₀
  refine (hs.sub ht).congr_of_eventuallyEq ?_
  refine eventually_of_mem (e.open_baseSet.mem_nhds <| mem_baseSet_trivializationAt F V x₀) ?_
  intro x hx
  apply (e.linear 𝕜 hx).map_sub

@[simp]
theorem coe_sub (s t : Cₛ^n⟮I; F, V⟯) : ⇑(s - t) = s - t :=
  rfl

instance instZero : Zero Cₛ^n⟮I; F, V⟯ :=
  ⟨⟨fun _ => 0, (smooth_zeroSection 𝕜 V).of_le le_top⟩⟩

instance inhabited : Inhabited Cₛ^n⟮I; F, V⟯ :=
  ⟨0⟩

@[simp]
theorem coe_zero : ⇑(0 : Cₛ^n⟮I; F, V⟯) = 0 :=
  rfl

instance instSMul : SMul 𝕜 Cₛ^n⟮I; F, V⟯ := by
  refine ⟨fun c s => ⟨c • ⇑s, ?_⟩⟩
  intro x₀
  have hs := s.contMDiff x₀
  rw [contMDiffAt_section] at hs ⊢
  set e := trivializationAt F V x₀
  refine ((contMDiffAt_const (c := c)).smul hs).congr_of_eventuallyEq ?_
  refine eventually_of_mem (e.open_baseSet.mem_nhds <| mem_baseSet_trivializationAt F V x₀) ?_
  intro x hx
  apply (e.linear 𝕜 hx).2

@[simp]
theorem coe_smul (r : 𝕜) (s : Cₛ^n⟮I; F, V⟯) : ⇑(r • s : Cₛ^n⟮I; F, V⟯) = r • ⇑s :=
  rfl

instance instNeg : Neg Cₛ^n⟮I; F, V⟯ := by
  refine ⟨fun s => ⟨-s, ?_⟩⟩
  intro x₀
  have hs := s.contMDiff x₀
  rw [contMDiffAt_section] at hs ⊢
  set e := trivializationAt F V x₀
  refine hs.neg.congr_of_eventuallyEq ?_
  refine eventually_of_mem (e.open_baseSet.mem_nhds <| mem_baseSet_trivializationAt F V x₀) ?_
  intro x hx
  apply (e.linear 𝕜 hx).map_neg

@[simp]
theorem coe_neg (s : Cₛ^n⟮I; F, V⟯) : ⇑(-s : Cₛ^n⟮I; F, V⟯) = -s :=
  rfl

instance instNSMul : SMul ℕ Cₛ^n⟮I; F, V⟯ :=
  ⟨nsmulRec⟩

@[simp]
theorem coe_nsmul (s : Cₛ^n⟮I; F, V⟯) (k : ℕ) : ⇑(k • s : Cₛ^n⟮I; F, V⟯) = k • ⇑s := by
  induction' k with k ih
  simp_rw [zero_smul]; rfl
  simp_rw [succ_nsmul, ← ih]; rfl

instance instZSMul : SMul ℤ Cₛ^n⟮I; F, V⟯ :=
  ⟨zsmulRec⟩

@[simp]
theorem coe_zsmul (s : Cₛ^n⟮I; F, V⟯) (z : ℤ) : ⇑(z • s : Cₛ^n⟮I; F, V⟯) = z • ⇑s := by
  cases' z with n n
  refine (coe_nsmul s n).trans ?_
  simp only [Int.ofNat_eq_coe, natCast_zsmul]
  refine (congr_arg Neg.neg (coe_nsmul s (n + 1))).trans ?_
  simp only [negSucc_zsmul, neg_inj]

instance instAddCommGroup : AddCommGroup Cₛ^n⟮I; F, V⟯ :=
  coe_injective.addCommGroup _ coe_zero coe_add coe_neg coe_sub coe_nsmul coe_zsmul

variable (I F V n)

/-- The additive morphism from smooth sections to dependent maps. -/
def coeAddHom : Cₛ^n⟮I; F, V⟯ →+ ∀ x, V x where
  toFun := (↑)
  map_zero' := coe_zero
  map_add' := coe_add

variable {I F V n}

instance instModule : Module 𝕜 Cₛ^n⟮I; F, V⟯ :=
  coe_injective.module 𝕜 (coeAddHom I F n V) coe_smul

end ContMDiffSection
