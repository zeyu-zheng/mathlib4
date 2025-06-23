import Mathlib.Tactic.Have
/-
Copyright (c) 2024 Geoffrey Irving. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Irving
-/
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-!
# Properties of analyticity restricted to a set

From `Mathlib.Analysis.Analytic.Basic`, we have the definitons

1. `AnalyticWithinAt 𝕜 f s x` means a power series at `x` converges to `f` on `𝓝[s] x`, and
    `f` is continuous within `s` at `x`.
2. `AnalyticWithinOn 𝕜 f s t` means `∀ x ∈ t, AnalyticWithinAt 𝕜 f s x`.

This means there exists an extension of `f` which is analytic and agrees with `f` on `s ∪ {x}`, but
`f` is allowed to be arbitrary elsewhere.  Requiring `ContinuousWithinAt` is essential if `x ∉ s`:
it is required for composition and smoothness to follow without extra hypotheses (we could
alternately require convergence at `x` even if `x ∉ s`).

Here we prove basic properties of these definitions. Where convenient we assume completeness of the
ambient space, which allows us to related `AnalyticWithinAt` to analyticity of a local extension.
-/

noncomputable section

open Topology Filter ENNReal

open Set Filter

variable {α : Type*}

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

variable {E F G H : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F]
  [NormedSpace 𝕜 F] [NormedAddCommGroup G] [NormedSpace 𝕜 G] [NormedAddCommGroup H]
  [NormedSpace 𝕜 H]

/-!
### Basic properties
-/

@[simp] lemma hasFPowerSeriesWithinOnBall_univ {f : E → F} {p : FormalMultilinearSeries 𝕜 E F}
    {x : E} {r : ℝ≥0∞} :
    HasFPowerSeriesWithinOnBall f p univ x r ↔ HasFPowerSeriesOnBall f p x r := by
  constructor
  intro h
  exact ⟨h.r_le, h.r_pos, fun {y} m ↦ h.hasSum (mem_univ _) m⟩
  intro h
  refine ⟨h.r_le, h.r_pos, fun {y} _ m => h.hasSum m, ?_⟩
  exact (h.continuousOn.continuousAt (EMetric.ball_mem_nhds x h.r_pos)).continuousWithinAt

@[simp] lemma hasFPowerSeriesWithinAt_univ {f : E → F} {p : FormalMultilinearSeries 𝕜 E F} {x : E} :
    HasFPowerSeriesWithinAt f p univ x ↔ HasFPowerSeriesAt f p x := by
  simp only [HasFPowerSeriesWithinAt, hasFPowerSeriesWithinOnBall_univ, HasFPowerSeriesAt]

@[simp] lemma analyticWithinAt_univ {f : E → F} {x : E} :
    AnalyticWithinAt 𝕜 f univ x ↔ AnalyticAt 𝕜 f x := by
  simp only [AnalyticWithinAt, hasFPowerSeriesWithinAt_univ, AnalyticAt]

lemma analyticWithinOn_univ {f : E → F} :
    AnalyticWithinOn 𝕜 f univ ↔ AnalyticOn 𝕜 f univ := by
  simp only [AnalyticWithinOn, analyticWithinAt_univ, AnalyticOn]

lemma HasFPowerSeriesWithinAt.continuousWithinAt {f : E → F} {p : FormalMultilinearSeries 𝕜 E F}
    {s : Set E} {x : E} (h : HasFPowerSeriesWithinAt f p s x) : ContinuousWithinAt f s x := by
  rcases h with ⟨r, h⟩
  exact h.continuousWithinAt

lemma AnalyticWithinAt.continuousWithinAt {f : E → F} {s : Set E} {x : E}
    (h : AnalyticWithinAt 𝕜 f s x) : ContinuousWithinAt f s x := by
  rcases h with ⟨p, h⟩
  exact h.continuousWithinAt

/-- `AnalyticWithinAt` is trivial if `{x} ∈ 𝓝[s] x` -/
lemma analyticWithinAt_of_singleton_mem {f : E → F} {s : Set E} {x : E} (h : {x} ∈ 𝓝[s] x) :
    AnalyticWithinAt 𝕜 f s x := by
  have fc : ContinuousWithinAt f s x :=
    Filter.Tendsto.mono_left (tendsto_pure_nhds _ _) (Filter.le_pure_iff.mpr h)
  rcases mem_nhdsWithin.mp h with ⟨t, ot, xt, st⟩
  rcases Metric.mem_nhds_iff.mp (ot.mem_nhds xt) with ⟨r, r0, rt⟩
  exact ⟨constFormalMultilinearSeries 𝕜 E (f x), .ofReal r, {
    r_le := by simp only [FormalMultilinearSeries.constFormalMultilinearSeries_radius, le_top]
    r_pos := by positivity
    hasSum := by
      intro y ys yr
      simp only [subset_singleton_iff, mem_inter_iff, and_imp] at st
      specialize st (x + y) (rt (by simpa using yr)) ys
      simp only [st]
      apply (hasFPowerSeriesOnBall_const (e := 0)).hasSum
      simp only [Metric.emetric_ball_top, mem_univ]
    continuousWithinAt := fc
  }⟩

/-- Analyticity implies analyticity within any `s` -/
lemma AnalyticAt.analyticWithinAt {f : E → F} {s : Set E} {x : E} (h : AnalyticAt 𝕜 f x) :
    AnalyticWithinAt 𝕜 f s x := by
  rcases h with ⟨p, r, hp⟩
  exact ⟨p, r, {
    r_le := hp.r_le
    r_pos := hp.r_pos
    hasSum := fun {y} _ yr ↦ hp.hasSum yr
    continuousWithinAt :=
      (hp.continuousOn.continuousAt (EMetric.ball_mem_nhds x hp.r_pos)).continuousWithinAt
  }⟩

/-- Analyticity on `s` implies analyticity within `s` -/
lemma AnalyticOn.analyticWithinOn {f : E → F} {s : Set E} (h : AnalyticOn 𝕜 f s) :
    AnalyticWithinOn 𝕜 f s :=
  fun x m ↦ (h x m).analyticWithinAt

lemma AnalyticWithinOn.continuousOn {f : E → F} {s : Set E} (h : AnalyticWithinOn 𝕜 f s) :
    ContinuousOn f s :=
  fun x m ↦ (h x m).continuousWithinAt

/-- If `f` is `AnalyticWithinOn` near each point in a set, it is `AnalyticWithinOn` the set -/
lemma analyticWithinOn_of_locally_analyticWithinOn {f : E → F} {s : Set E}
    (h : ∀ x ∈ s, ∃ u, IsOpen u ∧ x ∈ u ∧ AnalyticWithinOn 𝕜 f (s ∩ u)) :
    AnalyticWithinOn 𝕜 f s := by
  intro x m
  rcases h x m with ⟨u, ou, xu, fu⟩
  rcases Metric.mem_nhds_iff.mp (ou.mem_nhds xu) with ⟨r, r0, ru⟩
  rcases fu x ⟨m, xu⟩ with ⟨p, t, fp⟩
  exact ⟨p, min (.ofReal r) t, {
    r_pos := lt_min (by positivity) fp.r_pos
    r_le := min_le_of_right_le fp.r_le
    hasSum := by
      intro y ys yr
      simp only [EMetric.mem_ball, lt_min_iff, edist_lt_ofReal, dist_zero_right] at yr
      apply fp.hasSum ⟨ys, ru ?_⟩
      simp only [EMetric.mem_ball, yr]
      simp only [Metric.mem_ball, dist_self_add_left, yr]
    continuousWithinAt := by
      refine (fu.continuousOn x ⟨m, xu⟩).mono_left (le_of_eq ?_)
      exact nhdsWithin_eq_nhdsWithin xu ou (by simp only [inter_assoc, inter_self])
  }⟩

/-- On open sets, `AnalyticOn` and `AnalyticWithinOn` coincide -/
@[simp] lemma IsOpen.analyticWithinOn_iff_analyticOn {f : E → F} {s : Set E} (hs : IsOpen s) :
    AnalyticWithinOn 𝕜 f s ↔ AnalyticOn 𝕜 f s := by
  refine ⟨?_, AnalyticOn.analyticWithinOn⟩
  intro hf x m
  rcases Metric.mem_nhds_iff.mp (hs.mem_nhds m) with ⟨r, r0, rs⟩
  rcases hf x m with ⟨p, t, fp⟩
  exact ⟨p, min (.ofReal r) t, {
    r_pos := lt_min (by positivity) fp.r_pos
    r_le := min_le_of_right_le fp.r_le
    hasSum := by
      intro y ym
      simp only [EMetric.mem_ball, lt_min_iff, edist_lt_ofReal, dist_zero_right] at ym
      refine fp.hasSum (rs ?_) ym.2
      simp only [Metric.mem_ball, dist_self_add_left, ym.1]
  }⟩

/-!
### Equivalence to analyticity of a local extension

We show that `HasFPowerSeriesWithinOnBall`, `HasFPowerSeriesWithinAt`, and `AnalyticWithinAt` are
equivalent to the existence of a local extension with full analyticity.  We do not yet show a
result for `AnalyticWithinOn`, as this requires a bit more work to show that local extensions can
be stitched together.
-/

/-- `f` has power series `p` at `x` iff some local extension of `f` has that series -/
lemma hasFPowerSeriesWithinOnBall_iff_exists_hasFPowerSeriesOnBall [CompleteSpace F] {f : E → F}
    {p : FormalMultilinearSeries 𝕜 E F} {s : Set E} {x : E} {r : ℝ≥0∞} :
    HasFPowerSeriesWithinOnBall f p s x r ↔
      ContinuousWithinAt f s x ∧ ∃ g, EqOn f g (s ∩ EMetric.ball x r) ∧
        HasFPowerSeriesOnBall g p x r := by
  constructor
  intro h
  refine ⟨h.continuousWithinAt, fun y ↦ p.sum (y - x), ?_, ?_⟩
  intro y ⟨ys,yb⟩
  simp only [EMetric.mem_ball, edist_eq_coe_nnnorm_sub] at yb
  have e0 := p.hasSum (x := y - x) ?_
  have e1 := (h.hasSum (y := y - x) ?_ ?_)
  simp only [add_sub_cancel] at e1
  exact e1.unique e0
  simpa only [add_sub_cancel]
  simpa only [EMetric.mem_ball, edist_eq_coe_nnnorm]
  simp only [EMetric.mem_ball, edist_eq_coe_nnnorm]
  exact lt_of_lt_of_le yb h.r_le
  refine ⟨h.r_le, h.r_pos, ?_⟩
  intro y lt
  simp only [add_sub_cancel_left]
  apply p.hasSum
  simp only [EMetric.mem_ball] at lt ⊢
  exact lt_of_lt_of_le lt h.r_le
  intro ⟨mem, g, hfg, hg⟩
  refine ⟨hg.r_le, hg.r_pos, ?_, mem⟩
  intro y ys lt
  rw [hfg]
  exact hg.hasSum lt
  refine ⟨ys, ?_⟩
  simpa only [EMetric.mem_ball, edist_eq_coe_nnnorm_sub, add_sub_cancel_left, sub_zero] using lt

/-- `f` has power series `p` at `x` iff some local extension of `f` has that series -/
lemma hasFPowerSeriesWithinAt_iff_exists_hasFPowerSeriesAt [CompleteSpace F] {f : E → F}
    {p : FormalMultilinearSeries 𝕜 E F} {s : Set E} {x : E} :
    HasFPowerSeriesWithinAt f p s x ↔
      ContinuousWithinAt f s x ∧ ∃ g, f =ᶠ[𝓝[s] x] g ∧ HasFPowerSeriesAt g p x := by
  constructor
  intro ⟨r, h⟩
  rcases hasFPowerSeriesWithinOnBall_iff_exists_hasFPowerSeriesOnBall.mp h with ⟨fc, g, e, h⟩
  refine ⟨fc, g, ?_, ⟨r, h⟩⟩
  refine Filter.eventuallyEq_iff_exists_mem.mpr ⟨_, ?_, e⟩
  exact inter_mem_nhdsWithin _ (EMetric.ball_mem_nhds _ h.r_pos)
  intro ⟨mem, g, hfg, ⟨r, hg⟩⟩
  simp only [eventuallyEq_nhdsWithin_iff, Metric.eventually_nhds_iff] at hfg
  rcases hfg with ⟨e, e0, hfg⟩
  refine ⟨min r (.ofReal e), ?_⟩
  refine hasFPowerSeriesWithinOnBall_iff_exists_hasFPowerSeriesOnBall.mpr ⟨mem, g, ?_, ?_⟩
  intro y ⟨ys, xy⟩
  refine hfg ?_ ys
  simp only [EMetric.mem_ball, lt_min_iff, edist_lt_ofReal] at xy
  exact xy.2
  exact hg.mono (lt_min hg.r_pos (by positivity)) (min_le_left _ _)

/-- `f` is analytic within `s` at `x` iff some local extension of `f` is analytic at `x` -/
lemma analyticWithinAt_iff_exists_analyticAt [CompleteSpace F] {f : E → F} {s : Set E} {x : E} :
    AnalyticWithinAt 𝕜 f s x ↔
      ContinuousWithinAt f s x ∧ ∃ g, f =ᶠ[𝓝[s] x] g ∧ AnalyticAt 𝕜 g x := by
  simp only [AnalyticWithinAt, AnalyticAt, hasFPowerSeriesWithinAt_iff_exists_hasFPowerSeriesAt]
  tauto

/-- If `f` is analytic within `s` at `x`, some local extension of `f` is analytic at `x` -/
lemma AnalyticWithinAt.exists_analyticAt [CompleteSpace F] {f : E → F} {s : Set E} {x : E}
    (h : AnalyticWithinAt 𝕜 f s x) : ∃ g, f x = g x ∧ f =ᶠ[𝓝[s] x] g ∧ AnalyticAt 𝕜 g x := by
  by_cases s0 : 𝓝[s] x = ⊥
  refine ⟨fun _ ↦ f x, rfl, ?_, analyticAt_const⟩
  simp only [EventuallyEq, s0, eventually_bot]
  rcases analyticWithinAt_iff_exists_analyticAt.mp h with ⟨_, g, fg, hg⟩
  refine ⟨g, ?_, fg, hg⟩
  exact tendsto_nhds_unique' ⟨s0⟩ h.continuousWithinAt
    (hg.continuousAt.continuousWithinAt.congr' fg.symm)

/-!
### Congruence

We require completeness to use equivalence to locally extensions, but this is nonessential.
-/

lemma AnalyticWithinAt.congr_of_eventuallyEq [CompleteSpace F] {f g : E → F} {s : Set E} {x : E}
    (hf : AnalyticWithinAt 𝕜 f s x) (hs : f =ᶠ[𝓝[s] x] g) (hx : f x = g x) :
    AnalyticWithinAt 𝕜 g s x := by
  rcases hf.exists_analyticAt with ⟨f', fx, ef, hf'⟩
  rw [analyticWithinAt_iff_exists_analyticAt]
  have eg := hs.symm.trans ef
  refine ⟨?_, f', eg, hf'⟩
  exact hf'.continuousAt.continuousWithinAt.congr_of_eventuallyEq eg (hx.symm.trans fx)

lemma AnalyticWithinAt.congr [CompleteSpace F] {f g : E → F} {s : Set E} {x : E}
    (hf : AnalyticWithinAt 𝕜 f s x) (hs : EqOn f g s) (hx : f x = g x) :
    AnalyticWithinAt 𝕜 g s x :=
  hf.congr_of_eventuallyEq hs.eventuallyEq_nhdsWithin hx

lemma AnalyticWithinOn.congr [CompleteSpace F] {f g : E → F} {s : Set E}
    (hf : AnalyticWithinOn 𝕜 f s) (hs : EqOn f g s) :
    AnalyticWithinOn 𝕜 g s :=
  fun x m ↦ (hf x m).congr hs (hs m)

/-!
### Monotonicity w.r.t. the set we're analytic within
-/

lemma HasFPowerSeriesWithinOnBall.mono {f : E → F} {p : FormalMultilinearSeries 𝕜 E F}
    {s t : Set E} {x : E} {r : ℝ≥0∞} (h : HasFPowerSeriesWithinOnBall f p t x r)
    (hs : s ⊆ t) : HasFPowerSeriesWithinOnBall f p s x r where
  r_le := h.r_le
  r_pos := h.r_pos
  hasSum {_} ys yb := h.hasSum (hs ys) yb
  continuousWithinAt := h.continuousWithinAt.mono hs

lemma HasFPowerSeriesWithinAt.mono {f : E → F} {p : FormalMultilinearSeries 𝕜 E F}
    {s t : Set E} {x : E} (h : HasFPowerSeriesWithinAt f p t x)
    (hs : s ⊆ t) : HasFPowerSeriesWithinAt f p s x := by
  rcases h with ⟨r, hr⟩
  exact ⟨r, hr.mono hs⟩

lemma AnalyticWithinAt.mono {f : E → F} {s t : Set E} {x : E} (h : AnalyticWithinAt 𝕜 f t x)
    (hs : s ⊆ t) : AnalyticWithinAt 𝕜 f s x := by
  rcases h with ⟨p, hp⟩
  exact ⟨p, hp.mono hs⟩

lemma AnalyticWithinOn.mono {f : E → F} {s t : Set E} (h : AnalyticWithinOn 𝕜 f t)
    (hs : s ⊆ t) : AnalyticWithinOn 𝕜 f s :=
  fun _ m ↦ (h _ (hs m)).mono hs

/-!
### Analyticity within respects composition

Currently we require `CompleteSpace`s to use equivalence to local extensions, but this is not
essential.
-/

lemma AnalyticWithinAt.comp [CompleteSpace F] [CompleteSpace G] {f : F → G} {g : E → F} {s : Set F}
    {t : Set E} {x : E} (hf : AnalyticWithinAt 𝕜 f s (g x)) (hg : AnalyticWithinAt 𝕜 g t x)
    (h : MapsTo g t s) : AnalyticWithinAt 𝕜 (f ∘ g) t x := by
  rcases hf.exists_analyticAt with ⟨f', _, ef, hf'⟩
  rcases hg.exists_analyticAt with ⟨g', gx, eg, hg'⟩
  refine analyticWithinAt_iff_exists_analyticAt.mpr ⟨?_, f' ∘ g', ?_, ?_⟩
  exact hf.continuousWithinAt.comp hg.continuousWithinAt h
  have gt := hg.continuousWithinAt.tendsto_nhdsWithin h
  filter_upwards [eg, gt.eventually ef]
  intro y gy fgy
  simp only [Function.comp_apply, fgy, ← gy]
  exact hf'.comp_of_eq hg' gx.symm

lemma AnalyticWithinOn.comp [CompleteSpace F] [CompleteSpace G] {f : F → G} {g : E → F} {s : Set F}
    {t : Set E} (hf : AnalyticWithinOn 𝕜 f s) (hg : AnalyticWithinOn 𝕜 g t) (h : MapsTo g t s) :
    AnalyticWithinOn 𝕜 (f ∘ g) t :=
  fun x m ↦ (hf _ (h m)).comp (hg x m) h

/-!
### Analyticity within implies smoothness
-/

lemma AnalyticWithinAt.contDiffWithinAt [CompleteSpace F] {f : E → F} {s : Set E} {x : E}
    (h : AnalyticWithinAt 𝕜 f s x) {n : ℕ∞} : ContDiffWithinAt 𝕜 n f s x := by
  rcases h.exists_analyticAt with ⟨g, fx, fg, hg⟩
  exact hg.contDiffAt.contDiffWithinAt.congr_of_eventuallyEq fg fx

lemma AnalyticWithinOn.contDiffOn [CompleteSpace F] {f : E → F} {s : Set E}
    (h : AnalyticWithinOn 𝕜 f s) {n : ℕ∞} : ContDiffOn 𝕜 n f s :=
  fun x m ↦ (h x m).contDiffWithinAt

/-!
### Analyticity within respects products
-/

lemma HasFPowerSeriesWithinOnBall.prod {e : E} {f : E → F} {g : E → G} {s : Set E} {r t : ℝ≥0∞}
    {p : FormalMultilinearSeries 𝕜 E F} {q : FormalMultilinearSeries 𝕜 E G}
    (hf : HasFPowerSeriesWithinOnBall f p s e r) (hg : HasFPowerSeriesWithinOnBall g q s e t) :
    HasFPowerSeriesWithinOnBall (fun x ↦ (f x, g x)) (p.prod q) s e (min r t) where
  r_le := by
    rw [p.radius_prod_eq_min]
    exact min_le_min hf.r_le hg.r_le
  r_pos := lt_min hf.r_pos hg.r_pos
  hasSum := by
    intro y m hy
    simp_rw [FormalMultilinearSeries.prod, ContinuousMultilinearMap.prod_apply]
    refine (hf.hasSum m ?_).prod_mk (hg.hasSum m ?_)
    exact EMetric.mem_ball.mpr (lt_of_lt_of_le hy (min_le_left _ _))
    exact EMetric.mem_ball.mpr (lt_of_lt_of_le hy (min_le_right _ _))
  continuousWithinAt := hf.continuousWithinAt.prod hg.continuousWithinAt

lemma HasFPowerSeriesWithinAt.prod {e : E} {f : E → F} {g : E → G} {s : Set E}
    {p : FormalMultilinearSeries 𝕜 E F} {q : FormalMultilinearSeries 𝕜 E G}
    (hf : HasFPowerSeriesWithinAt f p s e) (hg : HasFPowerSeriesWithinAt g q s e) :
    HasFPowerSeriesWithinAt (fun x ↦ (f x, g x)) (p.prod q) s e := by
  rcases hf with ⟨_, hf⟩
  rcases hg with ⟨_, hg⟩
  exact ⟨_, hf.prod hg⟩

lemma AnalyticWithinAt.prod {e : E} {f : E → F} {g : E → G} {s : Set E}
    (hf : AnalyticWithinAt 𝕜 f s e) (hg : AnalyticWithinAt 𝕜 g s e) :
    AnalyticWithinAt 𝕜 (fun x ↦ (f x, g x)) s e := by
  rcases hf with ⟨_, hf⟩
  rcases hg with ⟨_, hg⟩
  exact ⟨_, hf.prod hg⟩

lemma AnalyticWithinOn.prod {f : E → F} {g : E → G} {s : Set E}
    (hf : AnalyticWithinOn 𝕜 f s) (hg : AnalyticWithinOn 𝕜 g s) :
    AnalyticWithinOn 𝕜 (fun x ↦ (f x, g x)) s :=
  fun x hx ↦ (hf x hx).prod (hg x hx)
