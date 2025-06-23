import Mathlib.Tactic.Have
/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lp
import Mathlib.MeasureTheory.Integral.SetIntegral
import Mathlib.Order.Filter.Ring

/-! # From equality of integrals to equality of functions

This file provides various statements of the general form "if two functions have the same integral
on all sets, then they are equal almost everywhere".
The different lemmas use various hypotheses on the class of functions, on the target space or on the
possible finiteness of the measure.

## Main statements

All results listed below apply to two functions `f, g`, together with two main hypotheses,
* `f` and `g` are integrable on all measurable sets with finite measure,
* for all measurable sets `s` with finite measure, `∫ x in s, f x ∂μ = ∫ x in s, g x ∂μ`.
The conclusion is then `f =ᵐ[μ] g`. The main lemmas are:
* `ae_eq_of_forall_setIntegral_eq_of_sigmaFinite`: case of a sigma-finite measure.
* `AEFinStronglyMeasurable.ae_eq_of_forall_setIntegral_eq`: for functions which are
  `AEFinStronglyMeasurable`.
* `Lp.ae_eq_of_forall_setIntegral_eq`: for elements of `Lp`, for `0 < p < ∞`.
* `Integrable.ae_eq_of_forall_setIntegral_eq`: for integrable functions.

For each of these results, we also provide a lemma about the equality of one function and 0. For
example, `Lp.ae_eq_zero_of_forall_setIntegral_eq_zero`.

We also register the corresponding lemma for integrals of `ℝ≥0∞`-valued functions, in
`ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite`.

Generally useful lemmas which are not related to integrals:
* `ae_eq_zero_of_forall_inner`: if for all constants `c`, `fun x => inner c (f x) =ᵐ[μ] 0` then
  `f =ᵐ[μ] 0`.
* `ae_eq_zero_of_forall_dual`: if for all constants `c` in the dual space,
  `fun x => c (f x) =ᵐ[μ] 0` then `f =ᵐ[μ] 0`.

-/


open MeasureTheory TopologicalSpace NormedSpace Filter

open scoped ENNReal NNReal MeasureTheory Topology

namespace MeasureTheory

section AeEqOfForall

variable {α E 𝕜 : Type*} {m : MeasurableSpace α} {μ : Measure α} [RCLike 𝕜]

theorem ae_eq_zero_of_forall_inner [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [SecondCountableTopology E] {f : α → E} (hf : ∀ c : E, (fun x => (inner c (f x) : 𝕜)) =ᵐ[μ] 0) :
    f =ᵐ[μ] 0 := by
  let s := denseSeq E
  have hs : DenseRange s := denseRange_denseSeq E
  have hf' : ∀ᵐ x ∂μ, ∀ n : ℕ, inner (s n) (f x) = (0 : 𝕜)
  apply ae_all_iff.mpr fun n => hf (s n)
  refine hf'.mono fun x hx => ?_
  rw [Pi.zero_apply, ← @inner_self_eq_zero 𝕜]
  have h_closed : IsClosed {c : E | inner c (f x) = (0 : 𝕜)} :=
    isClosed_eq (continuous_id.inner continuous_const) continuous_const
  exact @isClosed_property ℕ E _ s (fun c => inner c (f x) = (0 : 𝕜)) hs h_closed (fun n => hx n) _

local notation "⟪" x ", " y "⟫" => y x

variable (𝕜)

theorem ae_eq_zero_of_forall_dual_of_isSeparable [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {t : Set E} (ht : TopologicalSpace.IsSeparable t) {f : α → E}
    (hf : ∀ c : Dual 𝕜 E, (fun x => ⟪f x, c⟫) =ᵐ[μ] 0) (h't : ∀ᵐ x ∂μ, f x ∈ t) : f =ᵐ[μ] 0 := by
  rcases ht with ⟨d, d_count, hd⟩
  haveI : Encodable d := d_count.toEncodable
  have : ∀ x : d, ∃ g : E →L[𝕜] 𝕜, ‖g‖ ≤ 1 ∧ g x = ‖(x : E)‖
  exact fun x => exists_dual_vector'' 𝕜 (x : E)
  choose s hs using this
  have A : ∀ a : E, a ∈ t → (∀ x, ⟪a, s x⟫ = (0 : 𝕜)) → a = 0
  intro a hat ha
  contrapose! ha
  have a_pos : 0 < ‖a‖
  simp only [ha, norm_pos_iff, Ne, not_false_iff]
  have a_mem : a ∈ closure d
  exact hd hat
  obtain ⟨x, hx⟩ : ∃ x : d, dist a x < ‖a‖ / 2
  rcases Metric.mem_closure_iff.1 a_mem (‖a‖ / 2) (half_pos a_pos) with ⟨x, h'x, hx⟩
  exact ⟨⟨x, h'x⟩, hx⟩
  use x
  have I : ‖a‖ / 2 < ‖(x : E)‖
  have : ‖a‖ ≤ ‖(x : E)‖ + ‖a - x‖ := norm_le_insert' _ _
  have : ‖a - x‖ < ‖a‖ / 2
  rwa [dist_eq_norm] at hx
  linarith
  intro h
  apply lt_irrefl ‖s x x‖
  calc
    ‖s x x‖ = ‖s x (x - a)‖ := by simp only [h, sub_zero, ContinuousLinearMap.map_sub]
    _ ≤ 1 * ‖(x : E) - a‖ := ContinuousLinearMap.le_of_opNorm_le _ (hs x).1 _
    _ < ‖a‖ / 2 := by rw [one_mul]; rwa [dist_eq_norm'] at hx
    _ < ‖(x : E)‖ := I
    _ = ‖s x x‖ := by rw [(hs x).2, RCLike.norm_coe_norm]
  have hfs : ∀ y : d, ∀ᵐ x ∂μ, ⟪f x, s y⟫ = (0 : 𝕜) := fun y => hf (s y)
  have hf' : ∀ᵐ x ∂μ, ∀ y : d, ⟪f x, s y⟫ = (0 : 𝕜)
  rwa [ae_all_iff]
  filter_upwards [hf', h't] with x hx h'x
  exact A (f x) h'x hx

theorem ae_eq_zero_of_forall_dual [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [SecondCountableTopology E] {f : α → E} (hf : ∀ c : Dual 𝕜 E, (fun x => ⟪f x, c⟫) =ᵐ[μ] 0) :
    f =ᵐ[μ] 0 :=
  ae_eq_zero_of_forall_dual_of_isSeparable 𝕜 (.of_separableSpace Set.univ) hf
    (eventually_of_forall fun _ => Set.mem_univ _)

variable {𝕜}

end AeEqOfForall

variable {α E : Type*} {m m0 : MeasurableSpace α} {μ : Measure α} {s t : Set α}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {p : ℝ≥0∞}

section AeEqOfForallSetIntegralEq

theorem ae_const_le_iff_forall_lt_measure_zero {β} [LinearOrder β] [TopologicalSpace β]
    [OrderTopology β] [FirstCountableTopology β] (f : α → β) (c : β) :
    (∀ᵐ x ∂μ, c ≤ f x) ↔ ∀ b < c, μ {x | f x ≤ b} = 0 := by
  rw [ae_iff]
  push_neg
  constructor
  intro h b hb
  exact measure_mono_null (fun y hy => (lt_of_le_of_lt hy hb : _)) h
  intro hc
  by_cases h : ∀ b, c ≤ b
  have : {a : α | f a < c} = ∅
  apply Set.eq_empty_iff_forall_not_mem.2 fun x hx => ?_
  exact (lt_irrefl _ (lt_of_lt_of_le hx (h (f x)))).elim
  simp [this]
  by_cases H : ¬IsLUB (Set.Iio c) c
  have : c ∈ upperBounds (Set.Iio c)
  apply fun y hy => le_of_lt hy
  obtain ⟨b, b_up, bc⟩ : ∃ b : β, b ∈ upperBounds (Set.Iio c) ∧ b < c
  simpa [IsLUB, IsLeast, this, lowerBounds] using H
  exact measure_mono_null (fun x hx => b_up hx) (hc b bc)
  push_neg at H h
  obtain ⟨u, _, u_lt, u_lim, -⟩ :
    ∃ u : ℕ → β,
      StrictMono u ∧ (∀ n : ℕ, u n < c) ∧ Tendsto u atTop (𝓝 c) ∧ ∀ n : ℕ, u n ∈ Set.Iio c :=
    H.exists_seq_strictMono_tendsto_of_not_mem (lt_irrefl c) h
  have h_Union : {x | f x < c} = ⋃ n : ℕ, {x | f x ≤ u n}
  ext1 x
  simp_rw [Set.mem_iUnion, Set.mem_setOf_eq]
  constructor <;> intro h
  obtain ⟨n, hn⟩ := ((tendsto_order.1 u_lim).1 _ h).exists; exact ⟨n, hn.le⟩
  obtain ⟨n, hn⟩ := h; exact hn.trans_lt (u_lt _)
  rw [h_Union, measure_iUnion_null_iff]
  intro n
  exact hc _ (u_lt n)

section ENNReal

open scoped Topology

theorem ae_le_of_forall_setLIntegral_le_of_sigmaFinite₀ [SigmaFinite μ]
    {f g : α → ℝ≥0∞} (hf : AEMeasurable f μ)
    (h : ∀ s, MeasurableSet s → μ s < ∞ → ∫⁻ x in s, f x ∂μ ≤ ∫⁻ x in s, g x ∂μ) :
    f ≤ᵐ[μ] g := by
  have A : ∀ (ε N : ℝ≥0) (p : ℕ), 0 < ε →
      μ ({x | g x + ε ≤ f x ∧ g x ≤ N} ∩ spanningSets μ p) = 0
  intro ε N p εpos
  let s := {x | g x + ε ≤ f x ∧ g x ≤ N} ∩ spanningSets μ p
  have s_lt_top : μ s < ∞
  apply (measure_mono (Set.inter_subset_right)).trans_lt (measure_spanningSets_lt_top μ p)
  have A : (∫⁻ x in s, g x ∂μ) + ε * μ s ≤ (∫⁻ x in s, g x ∂μ) + 0
  apply calc
      (∫⁻ x in s, g x ∂μ) + ε * μ s = (∫⁻ x in s, g x ∂μ) + ∫⁻ _ in s, ε ∂μ := by
        simp only [lintegral_const, Set.univ_inter, MeasurableSet.univ, Measure.restrict_apply]
      _ = ∫⁻ x in s, g x + ε ∂μ := (lintegral_add_right _ measurable_const).symm
      _ ≤ ∫⁻ x in s, f x ∂μ :=
        setLIntegral_mono_ae hf.restrict <| ae_of_all _ fun x hx => hx.1.1
      _ ≤ (∫⁻ x in s, g x ∂μ) + 0 := by
        rw [add_zero, ← Measure.restrict_toMeasurable s_lt_top.ne]
        refine h _ (measurableSet_toMeasurable ..) ?_
        rwa [measure_toMeasurable]
  have B : (∫⁻ x in s, g x ∂μ) ≠ ∞
  apply (setLIntegral_lt_top_of_le_nnreal s_lt_top.ne ⟨N, fun _ h ↦ h.1.2⟩).ne
  have : (ε : ℝ≥0∞) * μ s ≤ 0 := ENNReal.le_of_add_le_add_left B A
  simpa only [ENNReal.coe_eq_zero, nonpos_iff_eq_zero, mul_eq_zero, εpos.ne', false_or_iff]
  obtain ⟨u, _, u_pos, u_lim⟩ :
    ∃ u : ℕ → ℝ≥0, StrictAnti u ∧ (∀ n, 0 < u n) ∧ Tendsto u atTop (𝓝 0) :=
    exists_seq_strictAnti_tendsto (0 : ℝ≥0)
  let s := fun n : ℕ => {x | g x + u n ≤ f x ∧ g x ≤ (n : ℝ≥0)} ∩ spanningSets μ n
  have μs : ∀ n, μ (s n) = 0
  apply fun n => A _ _ _ (u_pos n)
  have B : {x | f x ≤ g x}ᶜ ⊆ ⋃ n, s n
  intro x hx
  simp only [Set.mem_compl_iff, Set.mem_setOf, not_le] at hx
  have L1 : ∀ᶠ n in atTop, g x + u n ≤ f x
  have : Tendsto (fun n => g x + u n) atTop (𝓝 (g x + (0 : ℝ≥0))) :=
    tendsto_const_nhds.add (ENNReal.tendsto_coe.2 u_lim)
  simp only [ENNReal.coe_zero, add_zero] at this
  exact eventually_le_of_tendsto_lt hx this
  have L2 : ∀ᶠ n : ℕ in (atTop : Filter ℕ), g x ≤ (n : ℝ≥0) :=
    haveI : Tendsto (fun n : ℕ => ((n : ℝ≥0) : ℝ≥0∞)) atTop (𝓝 ∞) := by
      simp only [ENNReal.coe_natCast]
      exact ENNReal.tendsto_nat_nhds_top
    eventually_ge_of_tendsto_gt (hx.trans_le le_top) this
  apply Set.mem_iUnion.2
  exact ((L1.and L2).and (eventually_mem_spanningSets μ x)).exists
  refine le_antisymm ?_ bot_le
  calc
    μ {x : α | (fun x : α => f x ≤ g x) x}ᶜ ≤ μ (⋃ n, s n) := measure_mono B
    _ ≤ ∑' n, μ (s n) := measure_iUnion_le _
    _ = 0 := by simp only [μs, tsum_zero]

@[deprecated (since := "2024-06-29")]
alias ae_le_of_forall_set_lintegral_le_of_sigmaFinite₀ :=
  ae_le_of_forall_setLIntegral_le_of_sigmaFinite₀

theorem ae_le_of_forall_setLIntegral_le_of_sigmaFinite [SigmaFinite μ] {f g : α → ℝ≥0∞}
    (hf : Measurable f)
    (h : ∀ s, MeasurableSet s → μ s < ∞ → (∫⁻ x in s, f x ∂μ) ≤ ∫⁻ x in s, g x ∂μ) : f ≤ᵐ[μ] g :=
  ae_le_of_forall_setLIntegral_le_of_sigmaFinite₀ hf.aemeasurable h

@[deprecated (since := "2024-06-29")]
alias ae_le_of_forall_set_lintegral_le_of_sigmaFinite :=
  ae_le_of_forall_setLIntegral_le_of_sigmaFinite

theorem ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite₀ [SigmaFinite μ]
    {f g : α → ℝ≥0∞} (hf : AEMeasurable f μ) (hg : AEMeasurable g μ)
    (h : ∀ s, MeasurableSet s → μ s < ∞ → ∫⁻ x in s, f x ∂μ = ∫⁻ x in s, g x ∂μ) : f =ᵐ[μ] g := by
  have A : f ≤ᵐ[μ] g :=
    ae_le_of_forall_setLIntegral_le_of_sigmaFinite₀ hf fun s hs h's => le_of_eq (h s hs h's)
  have B : g ≤ᵐ[μ] f :=
    ae_le_of_forall_setLIntegral_le_of_sigmaFinite₀ hg fun s hs h's => ge_of_eq (h s hs h's)
  filter_upwards [A, B] with x using le_antisymm

@[deprecated (since := "2024-06-29")]
alias ae_eq_of_forall_set_lintegral_eq_of_sigmaFinite₀ :=
  ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite₀

theorem ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite [SigmaFinite μ] {f g : α → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g)
    (h : ∀ s, MeasurableSet s → μ s < ∞ → ∫⁻ x in s, f x ∂μ = ∫⁻ x in s, g x ∂μ) : f =ᵐ[μ] g :=
  ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite₀ hf.aemeasurable hg.aemeasurable h

@[deprecated (since := "2024-06-29")]
alias ae_eq_of_forall_set_lintegral_eq_of_sigmaFinite :=
  ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite

end ENNReal

section Real

variable {f : α → ℝ}

theorem ae_nonneg_of_forall_setIntegral_nonneg (hf : Integrable f μ)
    (hf_zero : ∀ s, MeasurableSet s → μ s < ∞ → 0 ≤ ∫ x in s, f x ∂μ) : 0 ≤ᵐ[μ] f := by
  simp_rw [EventuallyLE, Pi.zero_apply]
  rw [ae_const_le_iff_forall_lt_measure_zero]
  intro b hb_neg
  let s := {x | f x ≤ b}
  have hs : NullMeasurableSet s μ
  exact nullMeasurableSet_le hf.1.aemeasurable aemeasurable_const
  have mus : μ s < ∞
  exact Integrable.measure_le_lt_top hf hb_neg
  have h_int_gt : (∫ x in s, f x ∂μ) ≤ b * (μ s).toReal
  have h_const_le : (∫ x in s, f x ∂μ) ≤ ∫ _ in s, b ∂μ
  refine setIntegral_mono_ae_restrict hf.integrableOn (integrableOn_const.mpr (Or.inr mus)) ?_
  rw [EventuallyLE, ae_restrict_iff₀ (hs.mono μ.restrict_le_self)]
  exact eventually_of_forall fun x hxs => hxs
  rwa [setIntegral_const, smul_eq_mul, mul_comm] at h_const_le
  contrapose! h_int_gt with H
  calc
    b * (μ s).toReal < 0 := mul_neg_of_neg_of_pos hb_neg <| ENNReal.toReal_pos H mus.ne
    _ ≤ ∫ x in s, f x ∂μ := by
      rw [← μ.restrict_toMeasurable mus.ne]
      exact hf_zero _ (measurableSet_toMeasurable ..) (by rwa [measure_toMeasurable])

@[deprecated (since := "2024-04-17")]
alias ae_nonneg_of_forall_set_integral_nonneg_of_stronglyMeasurable :=
  ae_nonneg_of_forall_setIntegral_nonneg

@[deprecated (since := "2024-07-12")]
alias ae_nonneg_of_forall_setIntegral_nonneg_of_stronglyMeasurable :=
  ae_nonneg_of_forall_setIntegral_nonneg

@[deprecated (since := "2024-04-17")]
alias ae_nonneg_of_forall_set_integral_nonneg :=
  ae_nonneg_of_forall_setIntegral_nonneg

theorem ae_le_of_forall_setIntegral_le {f g : α → ℝ} (hf : Integrable f μ) (hg : Integrable g μ)
    (hf_le : ∀ s, MeasurableSet s → μ s < ∞ → (∫ x in s, f x ∂μ) ≤ ∫ x in s, g x ∂μ) :
    f ≤ᵐ[μ] g := by
  rw [← eventually_sub_nonneg]
  refine ae_nonneg_of_forall_setIntegral_nonneg (hg.sub hf) fun s hs => ?_
  rw [integral_sub' hg.integrableOn hf.integrableOn, sub_nonneg]
  exact hf_le s hs

@[deprecated (since := "2024-04-17")]
alias ae_le_of_forall_set_integral_le := ae_le_of_forall_setIntegral_le

theorem ae_nonneg_restrict_of_forall_setIntegral_nonneg_inter {f : α → ℝ} {t : Set α}
    (hf : IntegrableOn f t μ)
    (hf_zero : ∀ s, MeasurableSet s → μ (s ∩ t) < ∞ → 0 ≤ ∫ x in s ∩ t, f x ∂μ) :
    0 ≤ᵐ[μ.restrict t] f := by
  refine ae_nonneg_of_forall_setIntegral_nonneg hf fun s hs h's => ?_
  simp_rw [Measure.restrict_restrict hs]
  apply hf_zero s hs
  rwa [Measure.restrict_apply hs] at h's

@[deprecated (since := "2024-04-17")]
alias ae_nonneg_restrict_of_forall_set_integral_nonneg_inter :=
  ae_nonneg_restrict_of_forall_setIntegral_nonneg_inter

theorem ae_nonneg_of_forall_setIntegral_nonneg_of_sigmaFinite [SigmaFinite μ] {f : α → ℝ}
    (hf_int_finite : ∀ s, MeasurableSet s → μ s < ∞ → IntegrableOn f s μ)
    (hf_zero : ∀ s, MeasurableSet s → μ s < ∞ → 0 ≤ ∫ x in s, f x ∂μ) : 0 ≤ᵐ[μ] f := by
  apply ae_of_forall_measure_lt_top_ae_restrict
  intro t t_meas t_lt_top
  apply ae_nonneg_restrict_of_forall_setIntegral_nonneg_inter (hf_int_finite t t_meas t_lt_top)
  intro s s_meas _
  exact
    hf_zero _ (s_meas.inter t_meas)
      (lt_of_le_of_lt (measure_mono (Set.inter_subset_right)) t_lt_top)

@[deprecated (since := "2024-04-17")]
alias ae_nonneg_of_forall_set_integral_nonneg_of_sigmaFinite :=
  ae_nonneg_of_forall_setIntegral_nonneg_of_sigmaFinite

theorem AEFinStronglyMeasurable.ae_nonneg_of_forall_setIntegral_nonneg {f : α → ℝ}
    (hf : AEFinStronglyMeasurable f μ)
    (hf_int_finite : ∀ s, MeasurableSet s → μ s < ∞ → IntegrableOn f s μ)
    (hf_zero : ∀ s, MeasurableSet s → μ s < ∞ → 0 ≤ ∫ x in s, f x ∂μ) : 0 ≤ᵐ[μ] f := by
  let t := hf.sigmaFiniteSet
  suffices 0 ≤ᵐ[μ.restrict t] f from
    ae_of_ae_restrict_of_ae_restrict_compl _ this hf.ae_eq_zero_compl.symm.le
  haveI : SigmaFinite (μ.restrict t) := hf.sigmaFinite_restrict
  refine
    ae_nonneg_of_forall_setIntegral_nonneg_of_sigmaFinite (fun s hs hμts => ?_) fun s hs hμts => ?_
  rw [IntegrableOn, Measure.restrict_restrict hs]
  rw [Measure.restrict_apply hs] at hμts
  exact hf_int_finite (s ∩ t) (hs.inter hf.measurableSet) hμts
  rw [Measure.restrict_restrict hs]
  rw [Measure.restrict_apply hs] at hμts
  exact hf_zero (s ∩ t) (hs.inter hf.measurableSet) hμts

@[deprecated (since := "2024-04-17")]
alias AEFinStronglyMeasurable.ae_nonneg_of_forall_set_integral_nonneg :=
  AEFinStronglyMeasurable.ae_nonneg_of_forall_setIntegral_nonneg

theorem ae_nonneg_restrict_of_forall_setIntegral_nonneg {f : α → ℝ}
    (hf_int_finite : ∀ s, MeasurableSet s → μ s < ∞ → IntegrableOn f s μ)
    (hf_zero : ∀ s, MeasurableSet s → μ s < ∞ → 0 ≤ ∫ x in s, f x ∂μ) {t : Set α}
    (ht : MeasurableSet t) (hμt : μ t ≠ ∞) : 0 ≤ᵐ[μ.restrict t] f := by
  refine
    ae_nonneg_restrict_of_forall_setIntegral_nonneg_inter
      (hf_int_finite t ht (lt_top_iff_ne_top.mpr hμt)) fun s hs _ => ?_
  refine hf_zero (s ∩ t) (hs.inter ht) ?_
  exact (measure_mono Set.inter_subset_right).trans_lt (lt_top_iff_ne_top.mpr hμt)

@[deprecated (since := "2024-04-17")]
alias ae_nonneg_restrict_of_forall_set_integral_nonneg :=
  ae_nonneg_restrict_of_forall_setIntegral_nonneg

theorem ae_eq_zero_restrict_of_forall_setIntegral_eq_zero_real {f : α → ℝ}
    (hf_int_finite : ∀ s, MeasurableSet s → μ s < ∞ → IntegrableOn f s μ)
    (hf_zero : ∀ s, MeasurableSet s → μ s < ∞ → ∫ x in s, f x ∂μ = 0) {t : Set α}
    (ht : MeasurableSet t) (hμt : μ t ≠ ∞) : f =ᵐ[μ.restrict t] 0 := by
  suffices h_and : f ≤ᵐ[μ.restrict t] 0 ∧ 0 ≤ᵐ[μ.restrict t] f from
    h_and.1.mp (h_and.2.mono fun x hx1 hx2 => le_antisymm hx2 hx1)
  refine
    ⟨?_,
      ae_nonneg_restrict_of_forall_setIntegral_nonneg hf_int_finite
        (fun s hs hμs => (hf_zero s hs hμs).symm.le) ht hμt⟩
  suffices h_neg : 0 ≤ᵐ[μ.restrict t] -f by
    refine h_neg.mono fun x hx => ?_
    rw [Pi.neg_apply] at hx
    simpa using hx
  refine
    ae_nonneg_restrict_of_forall_setIntegral_nonneg (fun s hs hμs => (hf_int_finite s hs hμs).neg)
      (fun s hs hμs => ?_) ht hμt
  simp_rw [Pi.neg_apply]
  rw [integral_neg, neg_nonneg]
  exact (hf_zero s hs hμs).le

@[deprecated (since := "2024-04-17")]
alias ae_eq_zero_restrict_of_forall_set_integral_eq_zero_real :=
  ae_eq_zero_restrict_of_forall_setIntegral_eq_zero_real

end Real

theorem ae_eq_zero_restrict_of_forall_setIntegral_eq_zero {f : α → E}
    (hf_int_finite : ∀ s, MeasurableSet s → μ s < ∞ → IntegrableOn f s μ)
    (hf_zero : ∀ s : Set α, MeasurableSet s → μ s < ∞ → ∫ x in s, f x ∂μ = 0) {t : Set α}
    (ht : MeasurableSet t) (hμt : μ t ≠ ∞) : f =ᵐ[μ.restrict t] 0 := by
  rcases (hf_int_finite t ht hμt.lt_top).aestronglyMeasurable.isSeparable_ae_range with
    ⟨u, u_sep, hu⟩
  refine ae_eq_zero_of_forall_dual_of_isSeparable ℝ u_sep (fun c => ?_) hu
  refine ae_eq_zero_restrict_of_forall_setIntegral_eq_zero_real ?_ ?_ ht hμt
  intro s hs hμs
  exact ContinuousLinearMap.integrable_comp c (hf_int_finite s hs hμs)
  intro s hs hμs
  rw [ContinuousLinearMap.integral_comp_comm c (hf_int_finite s hs hμs), hf_zero s hs hμs]
  exact ContinuousLinearMap.map_zero _

@[deprecated (since := "2024-04-17")]
alias ae_eq_zero_restrict_of_forall_set_integral_eq_zero :=
  ae_eq_zero_restrict_of_forall_setIntegral_eq_zero

theorem ae_eq_restrict_of_forall_setIntegral_eq {f g : α → E}
    (hf_int_finite : ∀ s, MeasurableSet s → μ s < ∞ → IntegrableOn f s μ)
    (hg_int_finite : ∀ s, MeasurableSet s → μ s < ∞ → IntegrableOn g s μ)
    (hfg_zero : ∀ s : Set α, MeasurableSet s → μ s < ∞ → ∫ x in s, f x ∂μ = ∫ x in s, g x ∂μ)
    {t : Set α} (ht : MeasurableSet t) (hμt : μ t ≠ ∞) : f =ᵐ[μ.restrict t] g := by
  rw [← sub_ae_eq_zero]
  have hfg' : ∀ s : Set α, MeasurableSet s → μ s < ∞ → (∫ x in s, (f - g) x ∂μ) = 0
  intro s hs hμs
  rw [integral_sub' (hf_int_finite s hs hμs) (hg_int_finite s hs hμs)]
  exact sub_eq_zero.mpr (hfg_zero s hs hμs)
  have hfg_int : ∀ s, MeasurableSet s → μ s < ∞ → IntegrableOn (f - g) s μ := fun s hs hμs =>
    (hf_int_finite s hs hμs).sub (hg_int_finite s hs hμs)
  exact ae_eq_zero_restrict_of_forall_setIntegral_eq_zero hfg_int hfg' ht hμt

@[deprecated (since := "2024-04-17")]
alias ae_eq_restrict_of_forall_set_integral_eq :=
  ae_eq_restrict_of_forall_setIntegral_eq

theorem ae_eq_zero_of_forall_setIntegral_eq_of_sigmaFinite [SigmaFinite μ] {f : α → E}
    (hf_int_finite : ∀ s, MeasurableSet s → μ s < ∞ → IntegrableOn f s μ)
    (hf_zero : ∀ s : Set α, MeasurableSet s → μ s < ∞ → ∫ x in s, f x ∂μ = 0) : f =ᵐ[μ] 0 := by
  let S := spanningSets μ
  rw [← @Measure.restrict_univ _ _ μ, ← iUnion_spanningSets μ, EventuallyEq, ae_iff,
    Measure.restrict_apply' (MeasurableSet.iUnion (measurable_spanningSets μ))]
  rw [Set.inter_iUnion, measure_iUnion_null_iff]
  intro n
  have h_meas_n : MeasurableSet (S n) := measurable_spanningSets μ n
  have hμn : μ (S n) < ∞ := measure_spanningSets_lt_top μ n
  rw [← Measure.restrict_apply' h_meas_n]
  exact ae_eq_zero_restrict_of_forall_setIntegral_eq_zero hf_int_finite hf_zero h_meas_n hμn.ne

@[deprecated (since := "2024-04-17")]
alias ae_eq_zero_of_forall_set_integral_eq_of_sigmaFinite :=
  ae_eq_zero_of_forall_setIntegral_eq_of_sigmaFinite

theorem ae_eq_of_forall_setIntegral_eq_of_sigmaFinite [SigmaFinite μ] {f g : α → E}
    (hf_int_finite : ∀ s, MeasurableSet s → μ s < ∞ → IntegrableOn f s μ)
    (hg_int_finite : ∀ s, MeasurableSet s → μ s < ∞ → IntegrableOn g s μ)
    (hfg_eq : ∀ s : Set α, MeasurableSet s → μ s < ∞ → ∫ x in s, f x ∂μ = ∫ x in s, g x ∂μ) :
    f =ᵐ[μ] g := by
  rw [← sub_ae_eq_zero]
  have hfg : ∀ s : Set α, MeasurableSet s → μ s < ∞ → (∫ x in s, (f - g) x ∂μ) = 0
  intro s hs hμs
  rw [integral_sub' (hf_int_finite s hs hμs) (hg_int_finite s hs hμs),
    sub_eq_zero.mpr (hfg_eq s hs hμs)]
  have hfg_int : ∀ s, MeasurableSet s → μ s < ∞ → IntegrableOn (f - g) s μ := fun s hs hμs =>
    (hf_int_finite s hs hμs).sub (hg_int_finite s hs hμs)
  exact ae_eq_zero_of_forall_setIntegral_eq_of_sigmaFinite hfg_int hfg

@[deprecated (since := "2024-04-17")]
alias ae_eq_of_forall_set_integral_eq_of_sigmaFinite :=
  ae_eq_of_forall_setIntegral_eq_of_sigmaFinite

theorem AEFinStronglyMeasurable.ae_eq_zero_of_forall_setIntegral_eq_zero {f : α → E}
    (hf_int_finite : ∀ s, MeasurableSet s → μ s < ∞ → IntegrableOn f s μ)
    (hf_zero : ∀ s : Set α, MeasurableSet s → μ s < ∞ → ∫ x in s, f x ∂μ = 0)
    (hf : AEFinStronglyMeasurable f μ) : f =ᵐ[μ] 0 := by
  let t := hf.sigmaFiniteSet
  suffices f =ᵐ[μ.restrict t] 0 from
    ae_of_ae_restrict_of_ae_restrict_compl _ this hf.ae_eq_zero_compl
  haveI : SigmaFinite (μ.restrict t) := hf.sigmaFinite_restrict
  refine ae_eq_zero_of_forall_setIntegral_eq_of_sigmaFinite ?_ ?_
  intro s hs hμs
  rw [IntegrableOn, Measure.restrict_restrict hs]
  rw [Measure.restrict_apply hs] at hμs
  exact hf_int_finite _ (hs.inter hf.measurableSet) hμs
  intro s hs hμs
  rw [Measure.restrict_restrict hs]
  rw [Measure.restrict_apply hs] at hμs
  exact hf_zero _ (hs.inter hf.measurableSet) hμs

@[deprecated (since := "2024-04-17")]
alias AEFinStronglyMeasurable.ae_eq_zero_of_forall_set_integral_eq_zero :=
  AEFinStronglyMeasurable.ae_eq_zero_of_forall_setIntegral_eq_zero

theorem AEFinStronglyMeasurable.ae_eq_of_forall_setIntegral_eq {f g : α → E}
    (hf_int_finite : ∀ s, MeasurableSet s → μ s < ∞ → IntegrableOn f s μ)
    (hg_int_finite : ∀ s, MeasurableSet s → μ s < ∞ → IntegrableOn g s μ)
    (hfg_eq : ∀ s : Set α, MeasurableSet s → μ s < ∞ → ∫ x in s, f x ∂μ = ∫ x in s, g x ∂μ)
    (hf : AEFinStronglyMeasurable f μ) (hg : AEFinStronglyMeasurable g μ) : f =ᵐ[μ] g := by
  rw [← sub_ae_eq_zero]
  have hfg : ∀ s : Set α, MeasurableSet s → μ s < ∞ → (∫ x in s, (f - g) x ∂μ) = 0
  intro s hs hμs
  rw [integral_sub' (hf_int_finite s hs hμs) (hg_int_finite s hs hμs),
    sub_eq_zero.mpr (hfg_eq s hs hμs)]
  have hfg_int : ∀ s, MeasurableSet s → μ s < ∞ → IntegrableOn (f - g) s μ := fun s hs hμs =>
    (hf_int_finite s hs hμs).sub (hg_int_finite s hs hμs)
  exact (hf.sub hg).ae_eq_zero_of_forall_setIntegral_eq_zero hfg_int hfg

@[deprecated (since := "2024-04-17")]
alias AEFinStronglyMeasurable.ae_eq_of_forall_set_integral_eq :=
  AEFinStronglyMeasurable.ae_eq_of_forall_setIntegral_eq

theorem Lp.ae_eq_zero_of_forall_setIntegral_eq_zero (f : Lp E p μ) (hp_ne_zero : p ≠ 0)
    (hp_ne_top : p ≠ ∞) (hf_int_finite : ∀ s, MeasurableSet s → μ s < ∞ → IntegrableOn f s μ)
    (hf_zero : ∀ s : Set α, MeasurableSet s → μ s < ∞ → ∫ x in s, f x ∂μ = 0) : f =ᵐ[μ] 0 :=
  AEFinStronglyMeasurable.ae_eq_zero_of_forall_setIntegral_eq_zero hf_int_finite hf_zero
    (Lp.finStronglyMeasurable _ hp_ne_zero hp_ne_top).aefinStronglyMeasurable

@[deprecated (since := "2024-04-17")]
alias Lp.ae_eq_zero_of_forall_set_integral_eq_zero :=
  Lp.ae_eq_zero_of_forall_setIntegral_eq_zero

theorem Lp.ae_eq_of_forall_setIntegral_eq (f g : Lp E p μ) (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞)
    (hf_int_finite : ∀ s, MeasurableSet s → μ s < ∞ → IntegrableOn f s μ)
    (hg_int_finite : ∀ s, MeasurableSet s → μ s < ∞ → IntegrableOn g s μ)
    (hfg : ∀ s : Set α, MeasurableSet s → μ s < ∞ → ∫ x in s, f x ∂μ = ∫ x in s, g x ∂μ) :
    f =ᵐ[μ] g :=
  AEFinStronglyMeasurable.ae_eq_of_forall_setIntegral_eq hf_int_finite hg_int_finite hfg
    (Lp.finStronglyMeasurable _ hp_ne_zero hp_ne_top).aefinStronglyMeasurable
    (Lp.finStronglyMeasurable _ hp_ne_zero hp_ne_top).aefinStronglyMeasurable

@[deprecated (since := "2024-04-17")]
alias Lp.ae_eq_of_forall_set_integral_eq := Lp.ae_eq_of_forall_setIntegral_eq

theorem ae_eq_zero_of_forall_setIntegral_eq_of_finStronglyMeasurable_trim (hm : m ≤ m0) {f : α → E}
    (hf_int_finite : ∀ s, MeasurableSet[m] s → μ s < ∞ → IntegrableOn f s μ)
    (hf_zero : ∀ s : Set α, MeasurableSet[m] s → μ s < ∞ → ∫ x in s, f x ∂μ = 0)
    (hf : FinStronglyMeasurable f (μ.trim hm)) : f =ᵐ[μ] 0 := by
  obtain ⟨t, ht_meas, htf_zero, htμ⟩ := hf.exists_set_sigmaFinite
  haveI : SigmaFinite ((μ.restrict t).trim hm) := by rwa [restrict_trim hm μ ht_meas] at htμ
  have htf_zero : f =ᵐ[μ.restrict tᶜ] 0
  rw [EventuallyEq, ae_restrict_iff' (MeasurableSet.compl (hm _ ht_meas))]
  exact eventually_of_forall htf_zero
  have hf_meas_m : StronglyMeasurable[m] f := hf.stronglyMeasurable
  suffices f =ᵐ[μ.restrict t] 0 from
    ae_of_ae_restrict_of_ae_restrict_compl _ this htf_zero
  refine measure_eq_zero_of_trim_eq_zero hm ?_
  refine ae_eq_zero_of_forall_setIntegral_eq_of_sigmaFinite ?_ ?_
  intro s hs hμs
  unfold IntegrableOn
  rw [restrict_trim hm (μ.restrict t) hs, Measure.restrict_restrict (hm s hs)]
  rw [← restrict_trim hm μ ht_meas, Measure.restrict_apply hs,
    trim_measurableSet_eq hm (hs.inter ht_meas)] at hμs
  refine Integrable.trim hm ?_ hf_meas_m
  exact hf_int_finite _ (hs.inter ht_meas) hμs
  intro s hs hμs
  rw [restrict_trim hm (μ.restrict t) hs, Measure.restrict_restrict (hm s hs)]
  rw [← restrict_trim hm μ ht_meas, Measure.restrict_apply hs,
    trim_measurableSet_eq hm (hs.inter ht_meas)] at hμs
  rw [← integral_trim hm hf_meas_m]
  exact hf_zero _ (hs.inter ht_meas) hμs

@[deprecated (since := "2024-04-17")]
alias ae_eq_zero_of_forall_set_integral_eq_of_finStronglyMeasurable_trim :=
  ae_eq_zero_of_forall_setIntegral_eq_of_finStronglyMeasurable_trim

theorem Integrable.ae_eq_zero_of_forall_setIntegral_eq_zero {f : α → E} (hf : Integrable f μ)
    (hf_zero : ∀ s, MeasurableSet s → μ s < ∞ → ∫ x in s, f x ∂μ = 0) : f =ᵐ[μ] 0 := by
  have hf_Lp : Memℒp f 1 μ := memℒp_one_iff_integrable.mpr hf
  let f_Lp := hf_Lp.toLp f
  have hf_f_Lp : f =ᵐ[μ] f_Lp := (Memℒp.coeFn_toLp hf_Lp).symm
  refine hf_f_Lp.trans ?_
  refine Lp.ae_eq_zero_of_forall_setIntegral_eq_zero f_Lp one_ne_zero ENNReal.coe_ne_top ?_ ?_
  exact fun s _ _ => Integrable.integrableOn (L1.integrable_coeFn _)
  intro s hs hμs
  rw [integral_congr_ae (ae_restrict_of_ae hf_f_Lp.symm)]
  exact hf_zero s hs hμs

@[deprecated (since := "2024-04-17")]
alias Integrable.ae_eq_zero_of_forall_set_integral_eq_zero :=
  Integrable.ae_eq_zero_of_forall_setIntegral_eq_zero

theorem Integrable.ae_eq_of_forall_setIntegral_eq (f g : α → E) (hf : Integrable f μ)
    (hg : Integrable g μ)
    (hfg : ∀ s : Set α, MeasurableSet s → μ s < ∞ → ∫ x in s, f x ∂μ = ∫ x in s, g x ∂μ) :
    f =ᵐ[μ] g := by
  rw [← sub_ae_eq_zero]
  have hfg' : ∀ s : Set α, MeasurableSet s → μ s < ∞ → (∫ x in s, (f - g) x ∂μ) = 0
  intro s hs hμs
  rw [integral_sub' hf.integrableOn hg.integrableOn]
  exact sub_eq_zero.mpr (hfg s hs hμs)
  exact Integrable.ae_eq_zero_of_forall_setIntegral_eq_zero (hf.sub hg) hfg'

@[deprecated (since := "2024-04-17")]
alias Integrable.ae_eq_of_forall_set_integral_eq :=
  Integrable.ae_eq_of_forall_setIntegral_eq

variable {β : Type*} [TopologicalSpace β] [MeasurableSpace β] [BorelSpace β]

/-- If an integrable function has zero integral on all closed sets, then it is zero
almost everwhere. -/
lemma ae_eq_zero_of_forall_setIntegral_isClosed_eq_zero {μ : Measure β} {f : β → E}
    (hf : Integrable f μ) (h'f : ∀ (s : Set β), IsClosed s → ∫ x in s, f x ∂μ = 0) :
    f =ᵐ[μ] 0 := by
  suffices ∀ s, MeasurableSet s → ∫ x in s, f x ∂μ = 0 from
    hf.ae_eq_zero_of_forall_setIntegral_eq_zero (fun s hs _ ↦ this s hs)
  have A : ∀ (t : Set β), MeasurableSet t → ∫ (x : β) in t, f x ∂μ = 0
      → ∫ (x : β) in tᶜ, f x ∂μ = 0 := by
    intro t t_meas ht
    have I : ∫ x, f x ∂μ = 0
    rw [← integral_univ]; exact h'f _ isClosed_univ
    simpa [ht, I] using integral_add_compl t_meas hf
  intro s hs
  refine MeasurableSet.induction_on_open (fun U hU ↦ ?_) A (fun g g_disj g_meas hg ↦ ?_) hs
  rw [← compl_compl U]
  exact A _ hU.measurableSet.compl (h'f _ hU.isClosed_compl)
  rw [integral_iUnion g_meas g_disj hf.integrableOn]
  simp [hg]

@[deprecated (since := "2024-04-17")]
alias ae_eq_zero_of_forall_set_integral_isClosed_eq_zero :=
  ae_eq_zero_of_forall_setIntegral_isClosed_eq_zero

/-- If an integrable function has zero integral on all compact sets in a sigma-compact space, then
it is zero almost everwhere. -/
lemma ae_eq_zero_of_forall_setIntegral_isCompact_eq_zero
    [SigmaCompactSpace β] [R1Space β] {μ : Measure β} {f : β → E} (hf : Integrable f μ)
    (h'f : ∀ (s : Set β), IsCompact s → ∫ x in s, f x ∂μ = 0) :
    f =ᵐ[μ] 0 := by
  apply ae_eq_zero_of_forall_setIntegral_isClosed_eq_zero hf (fun s hs ↦ ?_)
  let t : ℕ → Set β := fun n ↦ closure (compactCovering β n) ∩ s
  suffices H : Tendsto (fun n ↦ ∫ x in t n, f x ∂μ) atTop (𝓝 (∫ x in s, f x ∂μ)) by
    have A : ∀ n, ∫ x in t n, f x ∂μ = 0
    apply fun n ↦ h'f _ ((isCompact_compactCovering β n).closure.inter_right hs)
    simp_rw [A, tendsto_const_nhds_iff] at H
    exact H.symm
  have B : s = ⋃ n, t n
  rw [← Set.iUnion_inter, iUnion_closure_compactCovering, Set.univ_inter]
  rw [B]
  apply tendsto_setIntegral_of_monotone
  intros n
  exact (isClosed_closure.inter hs).measurableSet
  intros m n hmn
  simp only [t, Set.le_iff_subset]
  gcongr
  exact hf.integrableOn

/-- If a locally integrable function has zero integral on all compact sets in a sigma-compact space,
then it is zero almost everwhere. -/
lemma ae_eq_zero_of_forall_setIntegral_isCompact_eq_zero'
    [SigmaCompactSpace β] [R1Space β] {μ : Measure β} {f : β → E} (hf : LocallyIntegrable f μ)
    (h'f : ∀ (s : Set β), IsCompact s → ∫ x in s, f x ∂μ = 0) :
    f =ᵐ[μ] 0 := by
  rw [← μ.restrict_univ, ← iUnion_closure_compactCovering]
  apply (ae_restrict_iUnion_iff _ _).2 (fun n ↦ ?_)
  apply ae_eq_zero_of_forall_setIntegral_isCompact_eq_zero
  exact hf.integrableOn_isCompact (isCompact_compactCovering β n).closure
  intro s hs
  rw [Measure.restrict_restrict' measurableSet_closure]
  exact h'f _ (hs.inter_right isClosed_closure)

end AeEqOfForallSetIntegralEq

section Lintegral

theorem AEMeasurable.ae_eq_of_forall_setLIntegral_eq {f g : α → ℝ≥0∞} (hf : AEMeasurable f μ)
    (hg : AEMeasurable g μ) (hfi : ∫⁻ x, f x ∂μ ≠ ∞) (hgi : ∫⁻ x, g x ∂μ ≠ ∞)
    (hfg : ∀ ⦃s⦄, MeasurableSet s → μ s < ∞ → ∫⁻ x in s, f x ∂μ = ∫⁻ x in s, g x ∂μ) :
    f =ᵐ[μ] g := by
  refine
    ENNReal.eventuallyEq_of_toReal_eventuallyEq (ae_lt_top' hf hfi).ne_of_lt
      (ae_lt_top' hg hgi).ne_of_lt
      (Integrable.ae_eq_of_forall_setIntegral_eq _ _
        (integrable_toReal_of_lintegral_ne_top hf hfi)
        (integrable_toReal_of_lintegral_ne_top hg hgi) fun s hs hs' => ?_)
  rw [integral_eq_lintegral_of_nonneg_ae, integral_eq_lintegral_of_nonneg_ae]
  congr 1
  rw [lintegral_congr_ae (ofReal_toReal_ae_eq _), lintegral_congr_ae (ofReal_toReal_ae_eq _)]
  exact hfg hs hs'
  refine ae_lt_top' hg.restrict (ne_of_lt (lt_of_le_of_lt ?_ hgi.lt_top))
  exact @setLIntegral_univ α _ μ g ▸ lintegral_mono_set (Set.subset_univ _)
  refine ae_lt_top' hf.restrict (ne_of_lt (lt_of_le_of_lt ?_ hfi.lt_top))
  exact @setLIntegral_univ α _ μ f ▸ lintegral_mono_set (Set.subset_univ _)
  -- putting the proofs where they are used is extremely slow
  exacts [ae_of_all _ fun x => ENNReal.toReal_nonneg,
    hg.ennreal_toReal.restrict.aestronglyMeasurable, ae_of_all _ fun x => ENNReal.toReal_nonneg,
    hf.ennreal_toReal.restrict.aestronglyMeasurable]

@[deprecated (since := "2024-06-29")]
alias AEMeasurable.ae_eq_of_forall_set_lintegral_eq := AEMeasurable.ae_eq_of_forall_setLIntegral_eq

end Lintegral

section WithDensity

variable {m : MeasurableSpace α} {μ : Measure α}

theorem withDensity_eq_iff_of_sigmaFinite [SigmaFinite μ] {f g : α → ℝ≥0∞} (hf : AEMeasurable f μ)
    (hg : AEMeasurable g μ) : μ.withDensity f = μ.withDensity g ↔ f =ᵐ[μ] g :=
  ⟨fun hfg ↦ by
    refine ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite₀ hf hg fun s hs _ ↦ ?_
    rw [← withDensity_apply f hs, ← withDensity_apply g hs, ← hfg], withDensity_congr_ae⟩

theorem withDensity_eq_iff {f g : α → ℝ≥0∞} (hf : AEMeasurable f μ)
    (hg : AEMeasurable g μ) (hfi : ∫⁻ x, f x ∂μ ≠ ∞) :
    μ.withDensity f = μ.withDensity g ↔ f =ᵐ[μ] g :=
  ⟨fun hfg ↦ by
    refine AEMeasurable.ae_eq_of_forall_setLIntegral_eq hf hg hfi ?_ fun s hs _ ↦ ?_
    rwa [← setLIntegral_univ, ← withDensity_apply g MeasurableSet.univ, ← hfg,
      withDensity_apply f MeasurableSet.univ, setLIntegral_univ]
    rw [← withDensity_apply f hs, ← withDensity_apply g hs, ← hfg], withDensity_congr_ae⟩

end WithDensity

end MeasureTheory
