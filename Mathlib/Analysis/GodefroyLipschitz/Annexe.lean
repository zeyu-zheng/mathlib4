import Mathlib.Analysis.Calculus.FDeriv.Norm
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Asymptotics.TVS
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Data.Real.Sign
import Mathlib.LinearAlgebra.Dimension.Finrank

open Real NNReal Set Filter Topology FiniteDimensional MeasureTheory Module Submodule LinearMap

variable {E : Type*}
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

section OfTopLeSpan

variable {K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]
variable {s t : Set V}

namespace Basis

noncomputable instance [Module.Finite K V] (hs : LinearIndependent K ((↑) : s → V)) (hst : s ⊆ t) :
    Fintype (hs.extend hst) := by
  refine Classical.choice (Cardinal.lt_aleph0_iff_fintype.1 ?_)
  refine lt_of_le_of_lt (LinearIndependent.cardinal_le_rank' (hs.linearIndependent_extend hst)) ?_
  exact rank_lt_aleph0 K V

end Basis

end OfTopLeSpan

section spancoe

variable {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]

theorem span_coe {s : Set M} {t : Set (span R s)} (hst : ((↑) : _ → M) ⁻¹' s ⊆ t) :
    span R t = ⊤ := by
  refine eq_top_iff'.2 fun ⟨x, hx⟩ ↦ ?_
  obtain ⟨n, f, g, hx⟩ := mem_span_set'.1 hx
  rw [mem_span_set']
  let h i : t := ⟨⟨g i, subset_span (g i).2⟩, hst (g i).2⟩
  refine ⟨n, f, h, ?_⟩
  rw [← Subtype.val_inj, AddSubmonoid.coe_finset_sum]
  simp [hx, h]

end spancoe

variable [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem le_opNorm_of {f : E →L[ℝ] F} {x : E} {C : ℝ} (hx : x ≠ 0) (h : C * ‖x‖ ≤ ‖f x‖) :
    C ≤ ‖f‖ := by
  rw [← _root_.mul_le_mul_right (norm_pos_iff.2 hx)]
  exact h.trans (ContinuousLinearMap.le_opNorm _ _)

theorem le_opNorm_of' {f : E →L[ℝ] F} {x : E} {C : ℝ} (hx : ‖x‖ = 1) (h : C ≤ ‖f x‖) :
    C ≤ ‖f‖ := by
  apply le_opNorm_of (norm_ne_zero_iff.1 (hx ▸ (by norm_num : (1 : ℝ) ≠ 0)))
  rwa [hx, mul_one]

theorem le_opNorm_of'' {f : E →L[ℝ] F} {x : E} {C : ℝ} (hx : x ≠ 0) (nx : ‖x‖ ≤ 1) (h : C ≤ ‖f x‖) :
    C ≤ ‖f‖ := by
  obtain hC | hC := le_total C 0
  · exact hC.trans (norm_nonneg _)
  · exact le_opNorm_of hx (le_trans (mul_le_of_le_one_right hC nx) h)

section LowerSemicontinuous

open WeakDual ContinuousLinearMap in
theorem lowerSemicontinuous_norm :
    LowerSemicontinuous (fun f : WeakDual ℝ E ↦ ‖toNormedDual f‖) := by
  intro f r hrf
  obtain hr | hr := lt_or_le r 0
  · exact Eventually.of_forall fun _ ↦ lt_of_lt_of_le hr (norm_nonneg _)
  · obtain ⟨x, nx, hx⟩ := exists_lt_apply_of_lt_opNorm f hrf
    wlog hfx : 0 ≤ f x
    · apply this f r hrf hr (-x)
      · rwa [norm_neg]
      · rwa [map_neg, norm_neg]
      · rw [map_neg]
        linarith
    · let U : Set (WeakDual ℝ E) := (fun (f : WeakDual ℝ E) ↦ f x) ⁻¹' Ioi r
      have : U ∈ 𝓝 f := by
        apply (isOpen_Ioi.preimage (eval_continuous x)).mem_nhds
        rw [norm_of_nonneg hfx] at hx
        simpa
      apply eventually_of_mem this
      intro g hg
      rw [← not_le, (opNorm_le_iff hr).not]
      push_neg
      use x
      apply lt_of_le_of_lt (b := r)
      · nth_rw 2 [← mul_one r]
        exact mul_le_mul_of_nonneg_left nx.le hr
      · exact lt_of_lt_of_le hg (le_abs_self _)

end LowerSemicontinuous
