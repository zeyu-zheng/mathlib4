import Mathlib.Tactic.Have
/-
Copyright (c) 2021 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying, Rémy Degenne
-/
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real

/-!
# Filtrations

This file defines filtrations of a measurable space and σ-finite filtrations.

## Main definitions

* `MeasureTheory.Filtration`: a filtration on a measurable space. That is, a monotone sequence of
  sub-σ-algebras.
* `MeasureTheory.SigmaFiniteFiltration`: a filtration `f` is σ-finite with respect to a measure
  `μ` if for all `i`, `μ.trim (f.le i)` is σ-finite.
* `MeasureTheory.Filtration.natural`: the smallest filtration that makes a process adapted. That
  notion `adapted` is not defined yet in this file. See `MeasureTheory.adapted`.

## Main results

* `MeasureTheory.Filtration.instCompleteLattice`: filtrations are a complete lattice.

## Tags

filtration, stochastic process

-/


open Filter Order TopologicalSpace

open scoped Classical MeasureTheory NNReal ENNReal Topology

namespace MeasureTheory

/-- A `Filtration` on a measurable space `Ω` with σ-algebra `m` is a monotone
sequence of sub-σ-algebras of `m`. -/
structure Filtration {Ω : Type*} (ι : Type*) [Preorder ι] (m : MeasurableSpace Ω) where
  seq : ι → MeasurableSpace Ω
  mono' : Monotone seq
  le' : ∀ i : ι, seq i ≤ m

attribute [coe] Filtration.seq

variable {Ω β ι : Type*} {m : MeasurableSpace Ω}

instance [Preorder ι] : CoeFun (Filtration ι m) fun _ => ι → MeasurableSpace Ω :=
  ⟨fun f => f.seq⟩

namespace Filtration

variable [Preorder ι]

protected theorem mono {i j : ι} (f : Filtration ι m) (hij : i ≤ j) : f i ≤ f j :=
  f.mono' hij

protected theorem le (f : Filtration ι m) (i : ι) : f i ≤ m :=
  f.le' i

@[ext]
protected theorem ext {f g : Filtration ι m} (h : (f : ι → MeasurableSpace Ω) = g) : f = g := by
  cases f; cases g; congr

variable (ι)

/-- The constant filtration which is equal to `m` for all `i : ι`. -/
def const (m' : MeasurableSpace Ω) (hm' : m' ≤ m) : Filtration ι m :=
  ⟨fun _ => m', monotone_const, fun _ => hm'⟩

variable {ι}

@[simp]
theorem const_apply {m' : MeasurableSpace Ω} {hm' : m' ≤ m} (i : ι) : const ι m' hm' i = m' :=
  rfl

instance : Inhabited (Filtration ι m) :=
  ⟨const ι m le_rfl⟩

instance : LE (Filtration ι m) :=
  ⟨fun f g => ∀ i, f i ≤ g i⟩

instance : Bot (Filtration ι m) :=
  ⟨const ι ⊥ bot_le⟩

instance : Top (Filtration ι m) :=
  ⟨const ι m le_rfl⟩

instance : Sup (Filtration ι m) :=
  ⟨fun f g =>
    { seq := fun i => f i ⊔ g i
      mono' := fun _ _ hij =>
        sup_le ((f.mono hij).trans le_sup_left) ((g.mono hij).trans le_sup_right)
      le' := fun i => sup_le (f.le i) (g.le i) }⟩

@[norm_cast]
theorem coeFn_sup {f g : Filtration ι m} : ⇑(f ⊔ g) = ⇑f ⊔ ⇑g :=
  rfl

instance : Inf (Filtration ι m) :=
  ⟨fun f g =>
    { seq := fun i => f i ⊓ g i
      mono' := fun _ _ hij =>
        le_inf (inf_le_left.trans (f.mono hij)) (inf_le_right.trans (g.mono hij))
      le' := fun i => inf_le_left.trans (f.le i) }⟩

@[norm_cast]
theorem coeFn_inf {f g : Filtration ι m} : ⇑(f ⊓ g) = ⇑f ⊓ ⇑g :=
  rfl

instance : SupSet (Filtration ι m) :=
  ⟨fun s =>
    { seq := fun i => sSup ((fun f : Filtration ι m => f i) '' s)
      mono' := fun i j hij => by
        refine sSup_le fun m' hm' => ?_
        rw [Set.mem_image] at hm'
        obtain ⟨f, hf_mem, hfm'⟩ := hm'
        rw [← hfm']
        refine (f.mono hij).trans ?_
        have hfj_mem : f j ∈ (fun g : Filtration ι m => g j) '' s := ⟨f, hf_mem, rfl⟩
        exact le_sSup hfj_mem
      le' := fun i => by
        refine sSup_le fun m' hm' => ?_
        rw [Set.mem_image] at hm'
        obtain ⟨f, _, hfm'⟩ := hm'
        rw [← hfm']
        exact f.le i }⟩

theorem sSup_def (s : Set (Filtration ι m)) (i : ι) :
    sSup s i = sSup ((fun f : Filtration ι m => f i) '' s) :=
  rfl

noncomputable instance : InfSet (Filtration ι m) :=
  ⟨fun s =>
    { seq := fun i => if Set.Nonempty s then sInf ((fun f : Filtration ι m => f i) '' s) else m
      mono' := fun i j hij => by
        by_cases h_nonempty : Set.Nonempty s
        swap; · simp only [h_nonempty, Set.image_nonempty, if_false, le_refl]
        simp only [h_nonempty, if_true, le_sInf_iff, Set.mem_image, forall_exists_index, and_imp,
          forall_apply_eq_imp_iff₂]
        refine fun f hf_mem => le_trans ?_ (f.mono hij)
        have hfi_mem : f i ∈ (fun g : Filtration ι m => g i) '' s := ⟨f, hf_mem, rfl⟩
        exact sInf_le hfi_mem
      le' := fun i => by
        by_cases h_nonempty : Set.Nonempty s
        swap; · simp only [h_nonempty, if_false, le_refl]
        simp only [h_nonempty, if_true]
        obtain ⟨f, hf_mem⟩ := h_nonempty
        exact le_trans (sInf_le ⟨f, hf_mem, rfl⟩) (f.le i) }⟩

theorem sInf_def (s : Set (Filtration ι m)) (i : ι) :
    sInf s i = if Set.Nonempty s then sInf ((fun f : Filtration ι m => f i) '' s) else m :=
  rfl

noncomputable instance instCompleteLattice : CompleteLattice (Filtration ι m) where
  le := (· ≤ ·)
  le_refl f i := le_rfl
  le_trans f g h h_fg h_gh i := (h_fg i).trans (h_gh i)
  le_antisymm f g h_fg h_gf := Filtration.ext <| funext fun i => (h_fg i).antisymm (h_gf i)
  sup := (· ⊔ ·)
  le_sup_left f g i := le_sup_left
  le_sup_right f g i := le_sup_right
  sup_le f g h h_fh h_gh i := sup_le (h_fh i) (h_gh _)
  inf := (· ⊓ ·)
  inf_le_left f g i := inf_le_left
  inf_le_right f g i := inf_le_right
  le_inf f g h h_fg h_fh i := le_inf (h_fg i) (h_fh i)
  sSup := sSup
  le_sSup s f hf_mem i := le_sSup ⟨f, hf_mem, rfl⟩
  sSup_le s f h_forall i :=
    sSup_le fun m' hm' => by
      obtain ⟨g, hg_mem, hfm'⟩ := hm'
      rw [← hfm']
      exact h_forall g hg_mem i
  sInf := sInf
  sInf_le s f hf_mem i := by
    have hs : s.Nonempty := ⟨f, hf_mem⟩
    simp only [sInf_def, hs, if_true]
    exact sInf_le ⟨f, hf_mem, rfl⟩
  le_sInf s f h_forall i := by
    by_cases hs : s.Nonempty
    swap; · simp only [sInf_def, hs, if_false]; exact f.le i
    simp only [sInf_def, hs, if_true, le_sInf_iff, Set.mem_image, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂]
    exact fun g hg_mem => h_forall g hg_mem i
  top := ⊤
  bot := ⊥
  le_top f i := f.le' i
  bot_le f i := bot_le

end Filtration

theorem measurableSet_of_filtration [Preorder ι] {f : Filtration ι m} {s : Set Ω} {i : ι}
    (hs : MeasurableSet[f i] s) : MeasurableSet[m] s :=
  f.le i s hs

/-- A measure is σ-finite with respect to filtration if it is σ-finite with respect
to all the sub-σ-algebra of the filtration. -/
class SigmaFiniteFiltration [Preorder ι] (μ : Measure Ω) (f : Filtration ι m) : Prop where
  SigmaFinite : ∀ i : ι, SigmaFinite (μ.trim (f.le i))

instance sigmaFinite_of_sigmaFiniteFiltration [Preorder ι] (μ : Measure Ω) (f : Filtration ι m)
    [hf : SigmaFiniteFiltration μ f] (i : ι) : SigmaFinite (μ.trim (f.le i)) :=
  hf.SigmaFinite _

instance (priority := 100) IsFiniteMeasure.sigmaFiniteFiltration [Preorder ι] (μ : Measure Ω)
    (f : Filtration ι m) [IsFiniteMeasure μ] : SigmaFiniteFiltration μ f :=
  ⟨fun n => by infer_instance⟩

/-- Given an integrable function `g`, the conditional expectations of `g` with respect to a
filtration is uniformly integrable. -/
theorem Integrable.uniformIntegrable_condexp_filtration [Preorder ι] {μ : Measure Ω}
    [IsFiniteMeasure μ] {f : Filtration ι m} {g : Ω → ℝ} (hg : Integrable g μ) :
    UniformIntegrable (fun i => μ[g|f i]) 1 μ :=
  hg.uniformIntegrable_condexp f.le

section OfSet

variable [Preorder ι]

/-- Given a sequence of measurable sets `(sₙ)`, `filtrationOfSet` is the smallest filtration
such that `sₙ` is measurable with respect to the `n`-th sub-σ-algebra in `filtrationOfSet`. -/
def filtrationOfSet {s : ι → Set Ω} (hsm : ∀ i, MeasurableSet (s i)) : Filtration ι m where
  seq i := MeasurableSpace.generateFrom {t | ∃ j ≤ i, s j = t}
  mono' _ _ hnm := MeasurableSpace.generateFrom_mono fun _ ⟨k, hk₁, hk₂⟩ => ⟨k, hk₁.trans hnm, hk₂⟩
  le' _ := MeasurableSpace.generateFrom_le fun _ ⟨k, _, hk₂⟩ => hk₂ ▸ hsm k

theorem measurableSet_filtrationOfSet {s : ι → Set Ω} (hsm : ∀ i, MeasurableSet[m] (s i)) (i : ι)
    {j : ι} (hj : j ≤ i) : MeasurableSet[filtrationOfSet hsm i] (s j) :=
  MeasurableSpace.measurableSet_generateFrom ⟨j, hj, rfl⟩

theorem measurableSet_filtrationOfSet' {s : ι → Set Ω} (hsm : ∀ n, MeasurableSet[m] (s n))
    (i : ι) : MeasurableSet[filtrationOfSet hsm i] (s i) :=
  measurableSet_filtrationOfSet hsm i le_rfl

end OfSet

namespace Filtration

variable [TopologicalSpace β] [MetrizableSpace β] [mβ : MeasurableSpace β] [BorelSpace β]
  [Preorder ι]

/-- Given a sequence of functions, the natural filtration is the smallest sequence
of σ-algebras such that that sequence of functions is measurable with respect to
the filtration. -/
def natural (u : ι → Ω → β) (hum : ∀ i, StronglyMeasurable (u i)) : Filtration ι m where
  seq i := ⨆ j ≤ i, MeasurableSpace.comap (u j) mβ
  mono' i j hij := biSup_mono fun k => ge_trans hij
  le' i := by
    refine iSup₂_le ?_
    rintro j _ s ⟨t, ht, rfl⟩
    exact (hum j).measurable ht

section

open MeasurableSpace

theorem filtrationOfSet_eq_natural [MulZeroOneClass β] [Nontrivial β] {s : ι → Set Ω}
    (hsm : ∀ i, MeasurableSet[m] (s i)) :
    filtrationOfSet hsm = natural (fun i => (s i).indicator (fun _ => 1 : Ω → β)) fun i =>
      stronglyMeasurable_one.indicator (hsm i) := by
  simp only [filtrationOfSet, natural, measurableSpace_iSup_eq, exists_prop, mk.injEq]
  ext1 i
  refine le_antisymm (generateFrom_le ?_) (generateFrom_le ?_)
  rintro _ ⟨j, hij, rfl⟩
  refine measurableSet_generateFrom ⟨j, measurableSet_generateFrom ⟨hij, ?_⟩⟩
  rw [comap_eq_generateFrom]
  refine measurableSet_generateFrom ⟨{1}, measurableSet_singleton 1, ?_⟩
  ext x
  simp [Set.indicator_const_preimage_eq_union]
  rintro t ⟨n, ht⟩
  suffices MeasurableSpace.generateFrom {t | n ≤ i ∧
    MeasurableSet[MeasurableSpace.comap ((s n).indicator (fun _ => 1 : Ω → β)) mβ] t} ≤
      MeasurableSpace.generateFrom {t | ∃ (j : ι), j ≤ i ∧ s j = t} by
    exact this _ ht
  refine generateFrom_le ?_
  rintro t ⟨hn, u, _, hu'⟩
  obtain heq | heq | heq | heq := Set.indicator_const_preimage (s n) u (1 : β)
  on_goal 4 => rw [Set.mem_singleton_iff] at heq
  all_goals rw [heq] at hu'; rw [← hu']
  exacts [MeasurableSet.univ, measurableSet_generateFrom ⟨n, hn, rfl⟩,
    MeasurableSet.compl (measurableSet_generateFrom ⟨n, hn, rfl⟩), measurableSet_empty _]

end

section Limit

variable {E : Type*} [Zero E] [TopologicalSpace E] {ℱ : Filtration ι m} {f : ι → Ω → E}
  {μ : Measure Ω}

/-- Given a process `f` and a filtration `ℱ`, if `f` converges to some `g` almost everywhere and
`g` is `⨆ n, ℱ n`-measurable, then `limitProcess f ℱ μ` chooses said `g`, else it returns 0.

This definition is used to phrase the a.e. martingale convergence theorem
`Submartingale.ae_tendsto_limitProcess` where an L¹-bounded submartingale `f` adapted to `ℱ`
converges to `limitProcess f ℱ μ` `μ`-almost everywhere. -/
noncomputable def limitProcess (f : ι → Ω → E) (ℱ : Filtration ι m)
    (μ : Measure Ω) :=
  if h : ∃ g : Ω → E,
    StronglyMeasurable[⨆ n, ℱ n] g ∧ ∀ᵐ ω ∂μ, Tendsto (fun n => f n ω) atTop (𝓝 (g ω)) then
  Classical.choose h else 0

theorem stronglyMeasurable_limitProcess : StronglyMeasurable[⨆ n, ℱ n] (limitProcess f ℱ μ) := by
  rw [limitProcess]
  split_ifs with h
  exacts [(Classical.choose_spec h).1, stronglyMeasurable_zero]

theorem stronglyMeasurable_limit_process' : StronglyMeasurable[m] (limitProcess f ℱ μ) :=
  stronglyMeasurable_limitProcess.mono (sSup_le fun _ ⟨_, hn⟩ => hn ▸ ℱ.le _)

theorem memℒp_limitProcess_of_eLpNorm_bdd {R : ℝ≥0} {p : ℝ≥0∞} {F : Type*} [NormedAddCommGroup F]
    {ℱ : Filtration ℕ m} {f : ℕ → Ω → F} (hfm : ∀ n, AEStronglyMeasurable (f n) μ)
    (hbdd : ∀ n, eLpNorm (f n) p μ ≤ R) : Memℒp (limitProcess f ℱ μ) p μ := by
  rw [limitProcess]
  split_ifs with h
  refine ⟨StronglyMeasurable.aestronglyMeasurable
    ((Classical.choose_spec h).1.mono (sSup_le fun m ⟨n, hn⟩ => hn ▸ ℱ.le _)),
    lt_of_le_of_lt (Lp.eLpNorm_lim_le_liminf_eLpNorm hfm _ (Classical.choose_spec h).2)
      (lt_of_le_of_lt ?_ (ENNReal.coe_lt_top : ↑R < ∞))⟩
  simp_rw [liminf_eq, eventually_atTop]
  exact sSup_le fun b ⟨a, ha⟩ => (ha a le_rfl).trans (hbdd _)
  exact zero_memℒp

@[deprecated (since := "2024-07-27")]
alias memℒp_limitProcess_of_snorm_bdd := memℒp_limitProcess_of_eLpNorm_bdd

end Limit

end Filtration

end MeasureTheory
