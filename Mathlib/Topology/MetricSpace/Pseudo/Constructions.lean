import Mathlib.Tactic.Have
/-
Copyright (c) 2015, 2017 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Robert Y. Lewis, Johannes Hölzl, Mario Carneiro, Sébastien Gouëzel
-/
import Mathlib.Topology.Bornology.Constructions
import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-!
# Product of pseudo-metric spaces and other constructions

This file constructs the infinity distance on finite products of normed groups and provides
instances for type synonyms.
-/

open Bornology Filter Metric Set
open scoped NNReal Topology

variable {α β : Type*} [PseudoMetricSpace α]

/-- Pseudometric space structure pulled back by a function. -/
abbrev PseudoMetricSpace.induced {α β} (f : α → β) (m : PseudoMetricSpace β) :
    PseudoMetricSpace α where
  dist x y := dist (f x) (f y)
  dist_self x := dist_self _
  dist_comm x y := dist_comm _ _
  dist_triangle x y z := dist_triangle _ _ _
  edist x y := edist (f x) (f y)
  edist_dist x y := edist_dist _ _
  toUniformSpace := UniformSpace.comap f m.toUniformSpace
  uniformity_dist := (uniformity_basis_dist.comap _).eq_biInf
  toBornology := Bornology.induced f
  cobounded_sets := Set.ext fun s => mem_comap_iff_compl.trans <| by
    simp only [← isBounded_def, isBounded_iff, forall_mem_image, mem_setOf]

/-- Pull back a pseudometric space structure by an inducing map. This is a version of
`PseudoMetricSpace.induced` useful in case if the domain already has a `TopologicalSpace`
structure. -/
def Inducing.comapPseudoMetricSpace {α β} [TopologicalSpace α] [m : PseudoMetricSpace β] {f : α → β}
    (hf : Inducing f) : PseudoMetricSpace α :=
  .replaceTopology (.induced f m) hf.induced

/-- Pull back a pseudometric space structure by a uniform inducing map. This is a version of
`PseudoMetricSpace.induced` useful in case if the domain already has a `UniformSpace`
structure. -/
def UniformInducing.comapPseudoMetricSpace {α β} [UniformSpace α] [m : PseudoMetricSpace β]
    (f : α → β) (h : UniformInducing f) : PseudoMetricSpace α :=
  .replaceUniformity (.induced f m) h.comap_uniformity.symm

instance Subtype.pseudoMetricSpace {p : α → Prop} : PseudoMetricSpace (Subtype p) :=
  PseudoMetricSpace.induced Subtype.val ‹_›

lemma Subtype.dist_eq {p : α → Prop} (x y : Subtype p) : dist x y = dist (x : α) y := rfl

lemma Subtype.nndist_eq {p : α → Prop} (x y : Subtype p) : nndist x y = nndist (x : α) y := rfl

namespace MulOpposite

@[to_additive]
instance instPseudoMetricSpace : PseudoMetricSpace αᵐᵒᵖ :=
  PseudoMetricSpace.induced MulOpposite.unop ‹_›

@[to_additive (attr := simp)]
lemma dist_unop (x y : αᵐᵒᵖ) : dist (unop x) (unop y) = dist x y := rfl

@[to_additive (attr := simp)]
lemma dist_op (x y : α) : dist (op x) (op y) = dist x y := rfl

@[to_additive (attr := simp)]
lemma nndist_unop (x y : αᵐᵒᵖ) : nndist (unop x) (unop y) = nndist x y := rfl

@[to_additive (attr := simp)]
lemma nndist_op (x y : α) : nndist (op x) (op y) = nndist x y := rfl

end MulOpposite

section NNReal

instance : PseudoMetricSpace ℝ≥0 := Subtype.pseudoMetricSpace

lemma NNReal.dist_eq (a b : ℝ≥0) : dist a b = |(a : ℝ) - b| := rfl

lemma NNReal.nndist_eq (a b : ℝ≥0) : nndist a b = max (a - b) (b - a) :=
  eq_of_forall_ge_iff fun _ => by
    simp only [max_le_iff, tsub_le_iff_right (α := ℝ≥0)]
    simp only [← NNReal.coe_le_coe, coe_nndist, dist_eq, abs_sub_le_iff,
      tsub_le_iff_right, NNReal.coe_add]

@[simp]
lemma NNReal.nndist_zero_eq_val (z : ℝ≥0) : nndist 0 z = z := by
  simp only [NNReal.nndist_eq, max_eq_right, tsub_zero, zero_tsub, zero_le']

@[simp]
lemma NNReal.nndist_zero_eq_val' (z : ℝ≥0) : nndist z 0 = z := by
  rw [nndist_comm]
  exact NNReal.nndist_zero_eq_val z

lemma NNReal.le_add_nndist (a b : ℝ≥0) : a ≤ b + nndist a b := by
  suffices (a : ℝ) ≤ (b : ℝ) + dist a b by
    rwa [← NNReal.coe_le_coe, NNReal.coe_add, coe_nndist]
  rw [← sub_le_iff_le_add']
  exact le_of_abs_le (dist_eq a b).ge

lemma NNReal.ball_zero_eq_Ico' (c : ℝ≥0) :
    Metric.ball (0 : ℝ≥0) c.toReal = Set.Ico 0 c := by ext x; simp

lemma NNReal.ball_zero_eq_Ico (c : ℝ) :
    Metric.ball (0 : ℝ≥0) c = Set.Ico 0 c.toNNReal := by
  by_cases c_pos : 0 < c
  convert NNReal.ball_zero_eq_Ico' ⟨c, c_pos.le⟩
  simp [Real.toNNReal, c_pos.le]
  simp [not_lt.mp c_pos]

lemma NNReal.closedBall_zero_eq_Icc' (c : ℝ≥0) :
    Metric.closedBall (0 : ℝ≥0) c.toReal = Set.Icc 0 c := by ext x; simp

lemma NNReal.closedBall_zero_eq_Icc {c : ℝ} (c_nn : 0 ≤ c) :
    Metric.closedBall (0 : ℝ≥0) c = Set.Icc 0 c.toNNReal := by
  convert NNReal.closedBall_zero_eq_Icc' ⟨c, c_nn⟩
  simp [Real.toNNReal, c_nn]

end NNReal

namespace ULift
variable [PseudoMetricSpace β]

instance : PseudoMetricSpace (ULift β) := PseudoMetricSpace.induced ULift.down ‹_›

lemma dist_eq (x y : ULift β) : dist x y = dist x.down y.down := rfl

lemma nndist_eq (x y : ULift β) : nndist x y = nndist x.down y.down := rfl

@[simp] lemma dist_up_up (x y : β) : dist (ULift.up x) (ULift.up y) = dist x y := rfl

@[simp] lemma nndist_up_up (x y : β) : nndist (ULift.up x) (ULift.up y) = nndist x y := rfl

end ULift

section Prod
variable [PseudoMetricSpace β]

-- Porting note: added `let`, otherwise `simp` failed
instance Prod.pseudoMetricSpaceMax : PseudoMetricSpace (α × β) :=
  let i := PseudoEMetricSpace.toPseudoMetricSpaceOfDist
    (fun x y : α × β => dist x.1 y.1 ⊔ dist x.2 y.2)
    (fun x y => (max_lt (edist_lt_top _ _) (edist_lt_top _ _)).ne) fun x y => by
      simp only [sup_eq_max, dist_edist, ← ENNReal.toReal_max (edist_ne_top _ _) (edist_ne_top _ _),
        Prod.edist_eq]
  i.replaceBornology fun s => by
    simp only [← isBounded_image_fst_and_snd, isBounded_iff_eventually, forall_mem_image, ←
      eventually_and, ← forall_and, ← max_le_iff]
    rfl

lemma Prod.dist_eq {x y : α × β} : dist x y = max (dist x.1 y.1) (dist x.2 y.2) := rfl

@[simp]
lemma dist_prod_same_left {x : α} {y₁ y₂ : β} : dist (x, y₁) (x, y₂) = dist y₁ y₂ := by
  simp [Prod.dist_eq, dist_nonneg]

@[simp]
lemma dist_prod_same_right {x₁ x₂ : α} {y : β} : dist (x₁, y) (x₂, y) = dist x₁ x₂ := by
  simp [Prod.dist_eq, dist_nonneg]

lemma ball_prod_same (x : α) (y : β) (r : ℝ) : ball x r ×ˢ ball y r = ball (x, y) r :=
  ext fun z => by simp [Prod.dist_eq]

lemma closedBall_prod_same (x : α) (y : β) (r : ℝ) :
    closedBall x r ×ˢ closedBall y r = closedBall (x, y) r := ext fun z => by simp [Prod.dist_eq]

lemma sphere_prod (x : α × β) (r : ℝ) :
    sphere x r = sphere x.1 r ×ˢ closedBall x.2 r ∪ closedBall x.1 r ×ˢ sphere x.2 r := by
  obtain hr | rfl | hr := lt_trichotomy r 0
  simp [hr]
  cases x
  simp_rw [← closedBall_eq_sphere_of_nonpos le_rfl, union_self, closedBall_prod_same]
  ext ⟨x', y'⟩
  simp_rw [Set.mem_union, Set.mem_prod, Metric.mem_closedBall, Metric.mem_sphere, Prod.dist_eq,
    max_eq_iff]
  refine or_congr (and_congr_right ?_) (and_comm.trans (and_congr_left ?_))
  all_goals rintro rfl; rfl

end Prod

lemma uniformContinuous_dist : UniformContinuous fun p : α × α => dist p.1 p.2 :=
  Metric.uniformContinuous_iff.2 fun ε ε0 =>
    ⟨ε / 2, half_pos ε0, fun {a b} h =>
      calc dist (dist a.1 a.2) (dist b.1 b.2) ≤ dist a.1 b.1 + dist a.2 b.2 :=
        dist_dist_dist_le _ _ _ _
      _ ≤ dist a b + dist a b := add_le_add (le_max_left _ _) (le_max_right _ _)
      _ < ε / 2 + ε / 2 := add_lt_add h h
      _ = ε := add_halves ε⟩

protected lemma UniformContinuous.dist [UniformSpace β] {f g : β → α} (hf : UniformContinuous f)
    (hg : UniformContinuous g) : UniformContinuous fun b => dist (f b) (g b) :=
  uniformContinuous_dist.comp (hf.prod_mk hg)

@[continuity]
lemma continuous_dist : Continuous fun p : α × α ↦ dist p.1 p.2 := uniformContinuous_dist.continuous

@[continuity, fun_prop]
protected lemma Continuous.dist [TopologicalSpace β] {f g : β → α} (hf : Continuous f)
    (hg : Continuous g) : Continuous fun b => dist (f b) (g b) :=
  continuous_dist.comp (hf.prod_mk hg : _)

protected lemma Filter.Tendsto.dist {f g : β → α} {x : Filter β} {a b : α}
    (hf : Tendsto f x (𝓝 a)) (hg : Tendsto g x (𝓝 b)) :
    Tendsto (fun x => dist (f x) (g x)) x (𝓝 (dist a b)) :=
  (continuous_dist.tendsto (a, b)).comp (hf.prod_mk_nhds hg)

lemma continuous_iff_continuous_dist [TopologicalSpace β] {f : β → α} :
    Continuous f ↔ Continuous fun x : β × β => dist (f x.1) (f x.2) :=
  ⟨fun h => h.fst'.dist h.snd', fun h =>
    continuous_iff_continuousAt.2 fun _ => tendsto_iff_dist_tendsto_zero.2 <|
      (h.comp (continuous_id.prod_mk continuous_const)).tendsto' _ _ <| dist_self _⟩

lemma uniformContinuous_nndist : UniformContinuous fun p : α × α => nndist p.1 p.2 :=
  uniformContinuous_dist.subtype_mk _

protected lemma UniformContinuous.nndist [UniformSpace β] {f g : β → α} (hf : UniformContinuous f)
    (hg : UniformContinuous g) : UniformContinuous fun b => nndist (f b) (g b) :=
  uniformContinuous_nndist.comp (hf.prod_mk hg)

lemma continuous_nndist : Continuous fun p : α × α => nndist p.1 p.2 :=
  uniformContinuous_nndist.continuous

@[fun_prop]
protected lemma Continuous.nndist [TopologicalSpace β] {f g : β → α} (hf : Continuous f)
    (hg : Continuous g) : Continuous fun b => nndist (f b) (g b) :=
  continuous_nndist.comp (hf.prod_mk hg : _)

protected lemma Filter.Tendsto.nndist {f g : β → α} {x : Filter β} {a b : α}
    (hf : Tendsto f x (𝓝 a)) (hg : Tendsto g x (𝓝 b)) :
    Tendsto (fun x => nndist (f x) (g x)) x (𝓝 (nndist a b)) :=
  (continuous_nndist.tendsto (a, b)).comp (hf.prod_mk_nhds hg)

section Pi

open Finset

variable {π : β → Type*} [Fintype β] [∀ b, PseudoMetricSpace (π b)]

/-- A finite product of pseudometric spaces is a pseudometric space, with the sup distance. -/
instance pseudoMetricSpacePi : PseudoMetricSpace (∀ b, π b) := by
  /- we construct the instance from the pseudoemetric space instance to avoid checking again that
    the uniformity is the same as the product uniformity, but we register nevertheless a nice
    formula for the distance -/
  let i := PseudoEMetricSpace.toPseudoMetricSpaceOfDist
    (fun f g : ∀ b, π b => ((sup univ fun b => nndist (f b) (g b) : ℝ≥0) : ℝ))
    (fun f g => ((Finset.sup_lt_iff bot_lt_top).2 fun b _ => edist_lt_top _ _).ne)
    (fun f g => by
      simp only [edist_pi_def, edist_nndist, ← ENNReal.coe_finset_sup, ENNReal.coe_toReal])
  refine i.replaceBornology fun s => ?_
  simp only [← isBounded_def, isBounded_iff_eventually, ← forall_isBounded_image_eval_iff,
    forall_mem_image, ← Filter.eventually_all, Function.eval_apply, @dist_nndist (π _)]
  refine eventually_congr ((eventually_ge_atTop 0).mono fun C hC ↦ ?_)
  lift C to ℝ≥0 using hC
  refine ⟨fun H x hx y hy ↦ NNReal.coe_le_coe.2 <| Finset.sup_le fun b _ ↦ H b hx hy,
    fun H b x hx y hy ↦ NNReal.coe_le_coe.2 ?_⟩
  simpa only using Finset.sup_le_iff.1 (NNReal.coe_le_coe.1 <| H hx hy) b (Finset.mem_univ b)

lemma nndist_pi_def (f g : ∀ b, π b) : nndist f g = sup univ fun b => nndist (f b) (g b) := rfl

lemma dist_pi_def (f g : ∀ b, π b) : dist f g = (sup univ fun b => nndist (f b) (g b) : ℝ≥0) := rfl

lemma nndist_pi_le_iff {f g : ∀ b, π b} {r : ℝ≥0} :
    nndist f g ≤ r ↔ ∀ b, nndist (f b) (g b) ≤ r := by simp [nndist_pi_def]

lemma nndist_pi_lt_iff {f g : ∀ b, π b} {r : ℝ≥0} (hr : 0 < r) :
    nndist f g < r ↔ ∀ b, nndist (f b) (g b) < r := by
  rw [← bot_eq_zero'] at hr
  simp [nndist_pi_def, Finset.sup_lt_iff hr]

lemma nndist_pi_eq_iff {f g : ∀ b, π b} {r : ℝ≥0} (hr : 0 < r) :
    nndist f g = r ↔ (∃ i, nndist (f i) (g i) = r) ∧ ∀ b, nndist (f b) (g b) ≤ r := by
  rw [eq_iff_le_not_lt, nndist_pi_lt_iff hr, nndist_pi_le_iff, not_forall, and_comm]
  simp_rw [not_lt, and_congr_left_iff, le_antisymm_iff]
  intro h
  refine exists_congr fun b => ?_
  apply (and_iff_right <| h _).symm

lemma dist_pi_lt_iff {f g : ∀ b, π b} {r : ℝ} (hr : 0 < r) :
    dist f g < r ↔ ∀ b, dist (f b) (g b) < r := by
  lift r to ℝ≥0 using hr.le
  exact nndist_pi_lt_iff hr

lemma dist_pi_le_iff {f g : ∀ b, π b} {r : ℝ} (hr : 0 ≤ r) :
    dist f g ≤ r ↔ ∀ b, dist (f b) (g b) ≤ r := by
  lift r to ℝ≥0 using hr
  exact nndist_pi_le_iff

lemma dist_pi_eq_iff {f g : ∀ b, π b} {r : ℝ} (hr : 0 < r) :
    dist f g = r ↔ (∃ i, dist (f i) (g i) = r) ∧ ∀ b, dist (f b) (g b) ≤ r := by
  lift r to ℝ≥0 using hr.le
  simp_rw [← coe_nndist, NNReal.coe_inj, nndist_pi_eq_iff hr, NNReal.coe_le_coe]

lemma dist_pi_le_iff' [Nonempty β] {f g : ∀ b, π b} {r : ℝ} :
    dist f g ≤ r ↔ ∀ b, dist (f b) (g b) ≤ r := by
  by_cases hr : 0 ≤ r
  exact dist_pi_le_iff hr
  exact iff_of_false (fun h => hr <| dist_nonneg.trans h) fun h =>
    hr <| dist_nonneg.trans <| h <| Classical.arbitrary _

lemma dist_pi_const_le (a b : α) : (dist (fun _ : β => a) fun _ => b) ≤ dist a b :=
  (dist_pi_le_iff dist_nonneg).2 fun _ => le_rfl

lemma nndist_pi_const_le (a b : α) : (nndist (fun _ : β => a) fun _ => b) ≤ nndist a b :=
  nndist_pi_le_iff.2 fun _ => le_rfl

@[simp]
lemma dist_pi_const [Nonempty β] (a b : α) : (dist (fun _ : β => a) fun _ => b) = dist a b := by
  simpa only [dist_edist] using congr_arg ENNReal.toReal (edist_pi_const a b)

@[simp]
lemma nndist_pi_const [Nonempty β] (a b : α) : (nndist (fun _ : β => a) fun _ => b) = nndist a b :=
  NNReal.eq <| dist_pi_const a b

lemma nndist_le_pi_nndist (f g : ∀ b, π b) (b : β) : nndist (f b) (g b) ≤ nndist f g := by
  rw [← ENNReal.coe_le_coe, ← edist_nndist, ← edist_nndist]
  exact edist_le_pi_edist f g b

lemma dist_le_pi_dist (f g : ∀ b, π b) (b : β) : dist (f b) (g b) ≤ dist f g := by
  simp only [dist_nndist, NNReal.coe_le_coe, nndist_le_pi_nndist f g b]

/-- An open ball in a product space is a product of open balls. See also `ball_pi'`
for a version assuming `Nonempty β` instead of `0 < r`. -/
lemma ball_pi (x : ∀ b, π b) {r : ℝ} (hr : 0 < r) :
    ball x r = Set.pi univ fun b => ball (x b) r := by
  ext p
  simp [dist_pi_lt_iff hr]

/-- An open ball in a product space is a product of open balls. See also `ball_pi`
for a version assuming `0 < r` instead of `Nonempty β`. -/
lemma ball_pi' [Nonempty β] (x : ∀ b, π b) (r : ℝ) :
    ball x r = Set.pi univ fun b => ball (x b) r :=
  (lt_or_le 0 r).elim (ball_pi x) fun hr => by simp [ball_eq_empty.2 hr]

/-- A closed ball in a product space is a product of closed balls. See also `closedBall_pi'`
for a version assuming `Nonempty β` instead of `0 ≤ r`. -/
lemma closedBall_pi (x : ∀ b, π b) {r : ℝ} (hr : 0 ≤ r) :
    closedBall x r = Set.pi univ fun b => closedBall (x b) r := by
  ext p
  simp [dist_pi_le_iff hr]

/-- A closed ball in a product space is a product of closed balls. See also `closedBall_pi`
for a version assuming `0 ≤ r` instead of `Nonempty β`. -/
lemma closedBall_pi' [Nonempty β] (x : ∀ b, π b) (r : ℝ) :
    closedBall x r = Set.pi univ fun b => closedBall (x b) r :=
  (le_or_lt 0 r).elim (closedBall_pi x) fun hr => by simp [closedBall_eq_empty.2 hr]

/-- A sphere in a product space is a union of spheres on each component restricted to the closed
ball. -/
lemma sphere_pi (x : ∀ b, π b) {r : ℝ} (h : 0 < r ∨ Nonempty β) :
    sphere x r = (⋃ i : β, Function.eval i ⁻¹' sphere (x i) r) ∩ closedBall x r := by
  obtain hr | rfl | hr := lt_trichotomy r 0
  simp [hr]
  rw [closedBall_eq_sphere_of_nonpos le_rfl, eq_comm, Set.inter_eq_right]
  letI := h.resolve_left (lt_irrefl _)
  inhabit β
  refine subset_iUnion_of_subset default ?_
  intro x hx
  replace hx := hx.le
  rw [dist_pi_le_iff le_rfl] at hx
  exact le_antisymm (hx default) dist_nonneg
  ext
  simp [dist_pi_eq_iff hr, dist_pi_le_iff hr.le]

@[simp]
lemma Fin.nndist_insertNth_insertNth {n : ℕ} {α : Fin (n + 1) → Type*}
    [∀ i, PseudoMetricSpace (α i)] (i : Fin (n + 1)) (x y : α i) (f g : ∀ j, α (i.succAbove j)) :
    nndist (i.insertNth x f) (i.insertNth y g) = max (nndist x y) (nndist f g) :=
  eq_of_forall_ge_iff fun c => by simp [nndist_pi_le_iff, i.forall_iff_succAbove]

@[simp]
lemma Fin.dist_insertNth_insertNth {n : ℕ} {α : Fin (n + 1) → Type*}
    [∀ i, PseudoMetricSpace (α i)] (i : Fin (n + 1)) (x y : α i) (f g : ∀ j, α (i.succAbove j)) :
    dist (i.insertNth x f) (i.insertNth y g) = max (dist x y) (dist f g) := by
  simp only [dist_nndist, Fin.nndist_insertNth_insertNth, NNReal.coe_max]

end Pi

instance : PseudoMetricSpace (Additive α) := ‹_›
instance : PseudoMetricSpace (Multiplicative α) := ‹_›
instance : PseudoMetricSpace αᵒᵈ := ‹_›
