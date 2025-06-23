import Mathlib.Tactic.Have
/-
Copyright (c) 2021 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.Data.Rat.Encodable
import Mathlib.Data.Real.EReal
import Mathlib.Topology.Instances.ENNReal
import Mathlib.Topology.Order.MonotoneContinuity

/-!
# Topological structure on `EReal`

We endow `EReal` with the order topology, and prove basic properties of this topology.

## Main results

* `Real.toEReal : ℝ → EReal` is an open embedding
* `ENNReal.toEReal : ℝ≥0∞ → EReal` is a closed embedding
* The addition on `EReal` is continuous except at `(⊥, ⊤)` and at `(⊤, ⊥)`.
* Negation is a homeomorphism on `EReal`.

## Implementation

Most proofs are adapted from the corresponding proofs on `ℝ≥0∞`.
-/

noncomputable section

open scoped Classical
open Set Filter Metric TopologicalSpace Topology
open scoped ENNReal NNReal Filter

variable {α : Type*} [TopologicalSpace α]

namespace EReal

instance : TopologicalSpace EReal := Preorder.topology EReal
instance : OrderTopology EReal := ⟨rfl⟩
instance : T5Space EReal := inferInstance
instance : T2Space EReal := inferInstance

lemma denseRange_ratCast : DenseRange (fun r : ℚ ↦ ((r : ℝ) : EReal)) :=
  dense_of_exists_between fun _ _ h => exists_range_iff.2 <| exists_rat_btwn_of_lt h

instance : SecondCountableTopology EReal :=
  have : SeparableSpace EReal := ⟨⟨_, countable_range _, denseRange_ratCast⟩⟩
  .of_separableSpace_orderTopology _

/-! ### Real coercion -/

theorem embedding_coe : Embedding ((↑) : ℝ → EReal) :=
  coe_strictMono.embedding_of_ordConnected <| by rw [range_coe_eq_Ioo]; exact ordConnected_Ioo

theorem openEmbedding_coe : OpenEmbedding ((↑) : ℝ → EReal) :=
  ⟨embedding_coe, by simp only [range_coe_eq_Ioo, isOpen_Ioo]⟩

@[norm_cast]
theorem tendsto_coe {α : Type*} {f : Filter α} {m : α → ℝ} {a : ℝ} :
    Tendsto (fun a => (m a : EReal)) f (𝓝 ↑a) ↔ Tendsto m f (𝓝 a) :=
  embedding_coe.tendsto_nhds_iff.symm

theorem _root_.continuous_coe_real_ereal : Continuous ((↑) : ℝ → EReal) :=
  embedding_coe.continuous

theorem continuous_coe_iff {f : α → ℝ} : (Continuous fun a => (f a : EReal)) ↔ Continuous f :=
  embedding_coe.continuous_iff.symm

theorem nhds_coe {r : ℝ} : 𝓝 (r : EReal) = (𝓝 r).map (↑) :=
  (openEmbedding_coe.map_nhds_eq r).symm

theorem nhds_coe_coe {r p : ℝ} :
    𝓝 ((r : EReal), (p : EReal)) = (𝓝 (r, p)).map fun p : ℝ × ℝ => (↑p.1, ↑p.2) :=
  ((openEmbedding_coe.prod openEmbedding_coe).map_nhds_eq (r, p)).symm

theorem tendsto_toReal {a : EReal} (ha : a ≠ ⊤) (h'a : a ≠ ⊥) :
    Tendsto EReal.toReal (𝓝 a) (𝓝 a.toReal) := by
  lift a to ℝ using ⟨ha, h'a⟩
  rw [nhds_coe, tendsto_map'_iff]
  exact tendsto_id

theorem continuousOn_toReal : ContinuousOn EReal.toReal ({⊥, ⊤}ᶜ : Set EReal) := fun _a ha =>
  ContinuousAt.continuousWithinAt (tendsto_toReal (mt Or.inr ha) (mt Or.inl ha))

/-- The set of finite `EReal` numbers is homeomorphic to `ℝ`. -/
def neBotTopHomeomorphReal : ({⊥, ⊤}ᶜ : Set EReal) ≃ₜ ℝ where
  toEquiv := neTopBotEquivReal
  continuous_toFun := continuousOn_iff_continuous_restrict.1 continuousOn_toReal
  continuous_invFun := continuous_coe_real_ereal.subtype_mk _

/-! ### ENNReal coercion -/

theorem embedding_coe_ennreal : Embedding ((↑) : ℝ≥0∞ → EReal) :=
  coe_ennreal_strictMono.embedding_of_ordConnected <| by
    rw [range_coe_ennreal]; exact ordConnected_Ici

theorem closedEmbedding_coe_ennreal : ClosedEmbedding ((↑) : ℝ≥0∞ → EReal) :=
  ⟨embedding_coe_ennreal, by rw [range_coe_ennreal]; exact isClosed_Ici⟩

@[norm_cast]
theorem tendsto_coe_ennreal {α : Type*} {f : Filter α} {m : α → ℝ≥0∞} {a : ℝ≥0∞} :
    Tendsto (fun a => (m a : EReal)) f (𝓝 ↑a) ↔ Tendsto m f (𝓝 a) :=
  embedding_coe_ennreal.tendsto_nhds_iff.symm

theorem _root_.continuous_coe_ennreal_ereal : Continuous ((↑) : ℝ≥0∞ → EReal) :=
  embedding_coe_ennreal.continuous

theorem continuous_coe_ennreal_iff {f : α → ℝ≥0∞} :
    (Continuous fun a => (f a : EReal)) ↔ Continuous f :=
  embedding_coe_ennreal.continuous_iff.symm

/-! ### Neighborhoods of infinity -/

theorem nhds_top : 𝓝 (⊤ : EReal) = ⨅ (a) (_ : a ≠ ⊤), 𝓟 (Ioi a) :=
  nhds_top_order.trans <| by simp only [lt_top_iff_ne_top]

nonrec theorem nhds_top_basis : (𝓝 (⊤ : EReal)).HasBasis (fun _ : ℝ ↦ True) (Ioi ·) := by
  refine nhds_top_basis.to_hasBasis (fun x hx => ?_) fun _ _ ↦ ⟨_, coe_lt_top _, Subset.rfl⟩
  rcases exists_rat_btwn_of_lt hx with ⟨y, hxy, -⟩
  exact ⟨_, trivial, Ioi_subset_Ioi hxy.le⟩

theorem nhds_top' : 𝓝 (⊤ : EReal) = ⨅ a : ℝ, 𝓟 (Ioi ↑a) := nhds_top_basis.eq_iInf

theorem mem_nhds_top_iff {s : Set EReal} : s ∈ 𝓝 (⊤ : EReal) ↔ ∃ y : ℝ, Ioi (y : EReal) ⊆ s :=
  nhds_top_basis.mem_iff.trans <| by simp only [true_and]

theorem tendsto_nhds_top_iff_real {α : Type*} {m : α → EReal} {f : Filter α} :
    Tendsto m f (𝓝 ⊤) ↔ ∀ x : ℝ, ∀ᶠ a in f, ↑x < m a :=
  nhds_top_basis.tendsto_right_iff.trans <| by simp only [true_implies, mem_Ioi]

theorem nhds_bot : 𝓝 (⊥ : EReal) = ⨅ (a) (_ : a ≠ ⊥), 𝓟 (Iio a) :=
  nhds_bot_order.trans <| by simp only [bot_lt_iff_ne_bot]

theorem nhds_bot_basis : (𝓝 (⊥ : EReal)).HasBasis (fun _ : ℝ ↦ True) (Iio ·) := by
  refine _root_.nhds_bot_basis.to_hasBasis (fun x hx => ?_) fun _ _ ↦ ⟨_, bot_lt_coe _, Subset.rfl⟩
  rcases exists_rat_btwn_of_lt hx with ⟨y, -, hxy⟩
  exact ⟨_, trivial, Iio_subset_Iio hxy.le⟩

theorem nhds_bot' : 𝓝 (⊥ : EReal) = ⨅ a : ℝ, 𝓟 (Iio ↑a) :=
  nhds_bot_basis.eq_iInf

theorem mem_nhds_bot_iff {s : Set EReal} : s ∈ 𝓝 (⊥ : EReal) ↔ ∃ y : ℝ, Iio (y : EReal) ⊆ s :=
  nhds_bot_basis.mem_iff.trans <| by simp only [true_and]

theorem tendsto_nhds_bot_iff_real {α : Type*} {m : α → EReal} {f : Filter α} :
    Tendsto m f (𝓝 ⊥) ↔ ∀ x : ℝ, ∀ᶠ a in f, m a < x :=
  nhds_bot_basis.tendsto_right_iff.trans <| by simp only [true_implies, mem_Iio]

/-! ### Liminfs and Limsups -/

section LimInfSup

variable {α : Type*} {f : Filter α} {u v : α → EReal} {a b : EReal}

lemma liminf_le_liminf (h : u ≤ᶠ[f] v) :
    liminf u f ≤ liminf v f := Filter.liminf_le_liminf h

lemma limsup_le_limsup (h : u ≤ᶠ[f] v) :
    limsup u f ≤ limsup v f := Filter.limsup_le_limsup h

/-- This lemma is superseded by `limsup_add_le_of_le` (weaker hypothesis) and
`limsup_add_lt_of_lt` (stronger thesis). -/
private lemma limsup_add_le_of_lt (ha : limsup u f < a) (hb : limsup v f < b) :
    limsup (u + v) f ≤ a + b := by
  rcases eq_or_neBot f with (rfl | _)
  simp only [limsup_bot, bot_le]
  rw [← @limsup_const EReal α _ f _ (a + b)]
  apply limsup_le_limsup (Eventually.mp (Eventually.and (eventually_lt_of_limsup_lt ha)
    (eventually_lt_of_limsup_lt hb)) (eventually_of_forall _))
  simp only [Pi.add_apply, and_imp]
  intro x
  exact fun ux_lt_a vx_lt_b ↦ add_le_add (le_of_lt ux_lt_a) (le_of_lt vx_lt_b)

lemma limsup_add_lt_of_lt (ha : limsup u f < a) (hb : limsup v f < b) :
    limsup (u + v) f < a + b := by
  obtain ⟨c, hc, hca⟩ := DenselyOrdered.dense _ _ ha
  obtain ⟨d, hd, hdb⟩ := DenselyOrdered.dense _ _ hb
  exact (limsup_add_le_of_lt hc hd).trans_lt (add_lt_add hca hdb)

lemma limsup_add_bot_of_ne_top (h : limsup u f = ⊥) (h' : limsup v f ≠ ⊤) :
    limsup (u + v) f = ⊥ := by
  apply le_bot_iff.1
  apply (le_iff_le_forall_real_gt ⊥ (limsup (u + v) f)).1
  intro x
  rcases exists_between_coe_real (h'.lt_top) with ⟨y, ⟨hy, _⟩⟩
  rw [← sub_add_cancel x y, coe_add (x - y) y, coe_sub x y]
  intro _
  apply @limsup_add_le_of_lt α f u v (x - y) y _ hy
  rw [h, ← coe_sub x y]
  exact bot_lt_coe (x - y)

lemma limsup_add_le_add_limsup
    (h : limsup u f ≠ ⊥ ∨ limsup v f ≠ ⊤) (h' : limsup u f ≠ ⊤ ∨ limsup v f ≠ ⊥) :
    limsup (u + v) f ≤ (limsup u f) + (limsup v f) := by
  rcases eq_bot_or_bot_lt (limsup u f) with (u_bot | u_nbot)
  have v_ntop := h.neg_resolve_left u_bot
  rw [limsup_add_bot_of_ne_top u_bot v_ntop]; exact bot_le
  rcases eq_bot_or_bot_lt (limsup v f) with (v_bot | v_nbot)
  have u_ntop := h'.neg_resolve_right v_bot
  rw [add_comm, limsup_add_bot_of_ne_top v_bot u_ntop]; exact bot_le
  rcases eq_top_or_lt_top (limsup v f) with (v_top | v_ntop)
  rw [v_top, add_top_of_ne_bot (ne_of_gt u_nbot)]; exact le_top
  have limsup_v_real := coe_toReal (ne_of_lt v_ntop) (ne_of_gt v_nbot)
  apply (le_iff_le_forall_real_gt _ _).1
  intros x hx
  rcases lt_iff_exists_real_btwn.1 hx with ⟨y, ⟨sum_lt_y, y_lt_x⟩⟩
  have key₁ : limsup u f < (y - limsup v f)
  apply lt_of_eq_of_lt _ (sub_lt_sub_of_lt_of_le sum_lt_y (le_of_eq (Eq.refl (limsup v f)))
    (ne_of_gt v_nbot) (ne_of_lt v_ntop))
  rw [← limsup_v_real, add_sub_cancel_right]
  have key₂ : limsup v f < limsup v f + x - y
  rw [← limsup_v_real]; norm_cast; norm_cast at y_lt_x; linarith
  apply le_of_le_of_eq (limsup_add_le_of_lt key₁ key₂)
  rw [← limsup_v_real]; norm_cast; linarith

lemma limsup_add_le_of_le (ha : limsup u f < a) (hb : limsup v f ≤ b) :
    limsup (u + v) f ≤ a + b := by
  rcases lt_or_eq_of_le hb with (hb | hb)
  exact limsup_add_le_of_lt ha hb
  by_cases hb' : b = ⊤
  convert le_top
  on_goal 1 => rw [hb']
  -- This closes both remaining goals at once.
  exact add_top_of_ne_bot ha.ne_bot
  exact (limsup_add_le_add_limsup (hb ▸ Or.inr hb') (Or.inl ha.ne_top)).trans
    (add_le_add ha.le hb.le)

lemma liminf_neg : liminf (- v) f = - limsup v f :=
  EReal.negOrderIso.limsup_apply.symm

lemma limsup_neg : limsup (- v) f = - liminf v f :=
  EReal.negOrderIso.liminf_apply.symm

lemma liminf_add_gt_of_gt (ha : a < liminf u f) (hb : b < liminf v f) :
    a + b < liminf (u + v) f := by
  have ha' : a ≠ ⊤ := ha.ne_top
  have hb' : b ≠ ⊤ := hb.ne_top
  have h : limsup (-(u + v)) f = limsup (-u + -v) f
  apply limsup_congr
  filter_upwards [eventually_lt_of_lt_liminf ha, eventually_lt_of_lt_liminf hb] with x hax hbx
  dsimp
  rw [neg_add (Or.inl hax.ne_bot) (Or.inr hbx.ne_bot), sub_eq_add_neg]
  rw [← neg_lt_neg_iff, ← limsup_neg] at ha hb ⊢
  rw [neg_add (Or.inr hb') (Or.inl ha'), h]
  exact limsup_add_lt_of_lt ha hb

lemma liminf_add_top_of_ne_bot (h : liminf u f = ⊤) (h' : liminf v f ≠ ⊥) :
    liminf (u + v) f = ⊤ := by
  apply top_le_iff.1 ((ge_iff_le_forall_real_lt (liminf (u + v) f) ⊤).1 _)
  intro x
  rcases exists_between_coe_real (Ne.bot_lt h') with ⟨y, ⟨_, hy⟩⟩
  intro _
  rw [← sub_add_cancel x y, coe_add (x - y) y]
  exact coe_sub x y ▸ @liminf_add_gt_of_gt α f u v (x - y) y
    (h ▸ coe_sub x y ▸ coe_lt_top (x-y)) hy |>.le

lemma add_liminf_le_liminf_add : (liminf u f) + (liminf v f) ≤ liminf (u + v) f := by
  by_cases hu : liminf u f = ⊥
  simp_all
  by_cases hv : liminf v f = ⊥
  simp_all
  have h' : limsup (-(u + v)) f = limsup (-u + -v) f
  apply limsup_congr
  filter_upwards [eventually_lt_of_lt_liminf (bot_lt_iff_ne_bot.mpr hu),
    eventually_lt_of_lt_liminf (bot_lt_iff_ne_bot.mpr hv)] with x hux hvx
  dsimp
  rw [neg_add (Or.inl hux.ne_bot) (Or.inr hvx.ne_bot), sub_eq_add_neg]
  rw [← neg_le_neg_iff, neg_add (Or.inl hu) (Or.inr hv), sub_eq_add_neg]
  rw [← neg_inj, neg_bot] at hu hv
  simp_rw [← limsup_neg] at hu hv ⊢
  exact h' ▸ limsup_add_le_add_limsup (Or.inr hv) (Or.inl hu)

lemma limsup_le_iff {b : EReal} : limsup u f ≤ b ↔ ∀ c : ℝ, b < c → ∀ᶠ a : α in f, u a ≤ c := by
  rw [← le_iff_le_forall_real_gt]
  refine ⟨?_, ?_⟩ <;> intro h c b_lt_c
  rcases exists_between_coe_real b_lt_c with ⟨d, b_lt_d, d_lt_c⟩
  specialize h d b_lt_d
  have key := Filter.eventually_lt_of_limsup_lt (lt_of_le_of_lt h d_lt_c)
  apply Filter.mem_of_superset key
  rw [Set.setOf_subset_setOf]
  exact fun a h' ↦ le_of_lt h'
  rcases eq_or_neBot f with (rfl | _)
  simp only [limsup_bot, bot_le]
  specialize h c b_lt_c
  exact @Filter.limsup_const EReal α _ f _ (c : EReal) ▸ limsup_le_limsup h

end LimInfSup

/-! ### Continuity of addition -/

theorem continuousAt_add_coe_coe (a b : ℝ) :
    ContinuousAt (fun p : EReal × EReal => p.1 + p.2) (a, b) := by
  simp only [ContinuousAt, nhds_coe_coe, ← coe_add, tendsto_map'_iff, (· ∘ ·), tendsto_coe,
    tendsto_add]

theorem continuousAt_add_top_coe (a : ℝ) :
    ContinuousAt (fun p : EReal × EReal => p.1 + p.2) (⊤, a) := by
  simp only [ContinuousAt, tendsto_nhds_top_iff_real, top_add_coe]
  refine fun r ↦ ((lt_mem_nhds (coe_lt_top (r - (a - 1)))).prod_nhds
    (lt_mem_nhds <| EReal.coe_lt_coe_iff.2 <| sub_one_lt _)).mono fun _ h ↦ ?_
  simpa only [← coe_add, sub_add_cancel] using add_lt_add h.1 h.2

theorem continuousAt_add_coe_top (a : ℝ) :
    ContinuousAt (fun p : EReal × EReal => p.1 + p.2) (a, ⊤) := by
  simpa only [add_comm, (· ∘ ·), ContinuousAt, Prod.swap]
    using Tendsto.comp (continuousAt_add_top_coe a) (continuous_swap.tendsto ((a : EReal), ⊤))

theorem continuousAt_add_top_top : ContinuousAt (fun p : EReal × EReal => p.1 + p.2) (⊤, ⊤) := by
  simp only [ContinuousAt, tendsto_nhds_top_iff_real, top_add_top]
  refine fun r ↦ ((lt_mem_nhds (coe_lt_top 0)).prod_nhds
    (lt_mem_nhds <| coe_lt_top r)).mono fun _ h ↦ ?_
  simpa only [coe_zero, zero_add] using add_lt_add h.1 h.2

theorem continuousAt_add_bot_coe (a : ℝ) :
    ContinuousAt (fun p : EReal × EReal => p.1 + p.2) (⊥, a) := by
  simp only [ContinuousAt, tendsto_nhds_bot_iff_real, bot_add]
  refine fun r ↦ ((gt_mem_nhds (bot_lt_coe (r - (a + 1)))).prod_nhds
    (gt_mem_nhds <| EReal.coe_lt_coe_iff.2 <| lt_add_one _)).mono fun _ h ↦ ?_
  simpa only [← coe_add, sub_add_cancel] using add_lt_add h.1 h.2

theorem continuousAt_add_coe_bot (a : ℝ) :
    ContinuousAt (fun p : EReal × EReal => p.1 + p.2) (a, ⊥) := by
  simpa only [add_comm, (· ∘ ·), ContinuousAt, Prod.swap]
    using Tendsto.comp (continuousAt_add_bot_coe a) (continuous_swap.tendsto ((a : EReal), ⊥))

theorem continuousAt_add_bot_bot : ContinuousAt (fun p : EReal × EReal => p.1 + p.2) (⊥, ⊥) := by
  simp only [ContinuousAt, tendsto_nhds_bot_iff_real, bot_add]
  refine fun r ↦ ((gt_mem_nhds (bot_lt_coe 0)).prod_nhds
    (gt_mem_nhds <| bot_lt_coe r)).mono fun _ h ↦ ?_
  simpa only [coe_zero, zero_add] using add_lt_add h.1 h.2

/-- The addition on `EReal` is continuous except where it doesn't make sense (i.e., at `(⊥, ⊤)`
and at `(⊤, ⊥)`). -/
theorem continuousAt_add {p : EReal × EReal} (h : p.1 ≠ ⊤ ∨ p.2 ≠ ⊥) (h' : p.1 ≠ ⊥ ∨ p.2 ≠ ⊤) :
    ContinuousAt (fun p : EReal × EReal => p.1 + p.2) p := by
  rcases p with ⟨x, y⟩
  induction x <;> induction y
  exact continuousAt_add_bot_bot
  exact continuousAt_add_bot_coe _
  simp at h'
  exact continuousAt_add_coe_bot _
  exact continuousAt_add_coe_coe _ _
  exact continuousAt_add_coe_top _
  simp at h
  exact continuousAt_add_top_coe _
  exact continuousAt_add_top_top

/-! ### Negation -/

instance : ContinuousNeg EReal := ⟨negOrderIso.continuous⟩

/-! ### Continuity of multiplication -/

/- Outside of indeterminacies `(0, ±∞)` and `(±∞, 0)`, the multiplication on `EReal` is continuous.
There are many different cases to consider, so we first prove some special cases and leverage as
much as possible the symmetries of the multiplication. -/

private lemma continuousAt_mul_swap {a b : EReal}
    (h : ContinuousAt (fun p : EReal × EReal ↦ p.1 * p.2) (a, b)) :
    ContinuousAt (fun p : EReal × EReal ↦ p.1 * p.2) (b, a) := by
  convert h.comp continuous_swap.continuousAt (x := (b, a))
  simp [mul_comm]

private lemma continuousAt_mul_symm1 {a b : EReal}
    (h : ContinuousAt (fun p : EReal × EReal ↦ p.1 * p.2) (a, b)) :
    ContinuousAt (fun p : EReal × EReal ↦ p.1 * p.2) (-a, b) := by
  have : (fun p : EReal × EReal ↦ p.1 * p.2) = (fun x : EReal ↦ -x)
      ∘ (fun p : EReal × EReal ↦ p.1 * p.2) ∘ (fun p : EReal × EReal ↦ (-p.1, p.2)) := by
    ext p
    simp
  rw [this]
  apply ContinuousAt.comp (Continuous.continuousAt continuous_neg)
    <| ContinuousAt.comp _ (ContinuousAt.prod_map (Continuous.continuousAt continuous_neg)
      (Continuous.continuousAt continuous_id))
  simp [h]

private lemma continuousAt_mul_symm2 {a b : EReal}
    (h : ContinuousAt (fun p : EReal × EReal ↦ p.1 * p.2) (a, b)) :
    ContinuousAt (fun p : EReal × EReal ↦ p.1 * p.2) (a, -b) :=
  continuousAt_mul_swap (continuousAt_mul_symm1 (continuousAt_mul_swap h))

private lemma continuousAt_mul_symm3 {a b : EReal}
    (h : ContinuousAt (fun p : EReal × EReal ↦ p.1 * p.2) (a, b)) :
    ContinuousAt (fun p : EReal × EReal ↦ p.1 * p.2) (-a, -b) :=
  continuousAt_mul_symm1 (continuousAt_mul_symm2 h)

private lemma continuousAt_mul_coe_coe (a b : ℝ) :
    ContinuousAt (fun p : EReal × EReal ↦ p.1 * p.2) (a, b) := by
  simp [ContinuousAt, EReal.nhds_coe_coe, ← EReal.coe_mul, Filter.tendsto_map'_iff,
    (· ∘ ·), EReal.tendsto_coe, tendsto_mul]

private lemma continuousAt_mul_top_top :
    ContinuousAt (fun p : EReal × EReal ↦ p.1 * p.2) (⊤, ⊤) := by
  simp only [ContinuousAt, EReal.top_mul_top, EReal.tendsto_nhds_top_iff_real]
  intro x
  rw [_root_.eventually_nhds_iff]
  use (Set.Ioi ((max x 0) : EReal)) ×ˢ (Set.Ioi 1)
  split_ands
  intros p p_in_prod
  simp only [Set.mem_prod, Set.mem_Ioi, max_lt_iff] at p_in_prod
  rcases p_in_prod with ⟨⟨p1_gt_x, p1_pos⟩, p2_gt_1⟩
  have := mul_le_mul_of_nonneg_left (le_of_lt p2_gt_1) (le_of_lt p1_pos)
  rw [mul_one p.1] at this
  exact lt_of_lt_of_le p1_gt_x this
  exact IsOpen.prod isOpen_Ioi isOpen_Ioi
  simp
  rw [Set.mem_Ioi, ← EReal.coe_one]; exact EReal.coe_lt_top 1

private lemma continuousAt_mul_top_pos {a : ℝ} (h : 0 < a) :
    ContinuousAt (fun p : EReal × EReal ↦ p.1 * p.2) (⊤, a) := by
  simp only [ContinuousAt, EReal.top_mul_coe_of_pos h, EReal.tendsto_nhds_top_iff_real]
  intro x
  rw [_root_.eventually_nhds_iff]
  use (Set.Ioi ((2*(max (x+1) 0)/a : ℝ) : EReal)) ×ˢ (Set.Ioi ((a/2 : ℝ) : EReal))
  split_ands
  intros p p_in_prod
  simp only [Set.mem_prod, Set.mem_Ioi] at p_in_prod
  rcases p_in_prod with ⟨p1_gt, p2_gt⟩
  have p1_pos : 0 < p.1
  apply lt_of_le_of_lt _ p1_gt
  rw [EReal.coe_nonneg]
  apply mul_nonneg _ (le_of_lt (inv_pos_of_pos h))
  simp only [gt_iff_lt, Nat.ofNat_pos, mul_nonneg_iff_of_pos_left, le_max_iff, le_refl, or_true]
  have a2_pos : 0 < ((a/2 : ℝ) : EReal)
  rw [EReal.coe_pos]; linarith
  have lock := mul_le_mul_of_nonneg_right (le_of_lt p1_gt) (le_of_lt a2_pos)
  have key := mul_le_mul_of_nonneg_left (le_of_lt p2_gt) (le_of_lt p1_pos)
  replace lock := le_trans lock key
  apply lt_of_lt_of_le _ lock
  rw [← EReal.coe_mul, EReal.coe_lt_coe_iff, div_mul_div_comm, mul_comm,
    ← div_mul_div_comm, mul_div_right_comm]
  simp only [ne_eq, Ne.symm (ne_of_lt h), not_false_eq_true, _root_.div_self, OfNat.ofNat_ne_zero,
    one_mul, lt_max_iff, lt_add_iff_pos_right, zero_lt_one, true_or]
  exact IsOpen.prod isOpen_Ioi isOpen_Ioi
  simp
  simp [h]

private lemma continuousAt_mul_top_ne_zero {a : ℝ} (h : a ≠ 0) :
    ContinuousAt (fun p : EReal × EReal ↦ p.1 * p.2) (⊤, a) := by
  rcases lt_or_gt_of_ne h with a_neg | a_pos
  exact neg_neg a ▸ continuousAt_mul_symm2 (continuousAt_mul_top_pos (neg_pos.2 a_neg))
  exact continuousAt_mul_top_pos a_pos

/-- The multiplication on `EReal` is continuous except at indeterminacies
(i.e. whenever one value is zero and the other infinite). -/
theorem continuousAt_mul {p : EReal × EReal} (h₁ : p.1 ≠ 0 ∨ p.2 ≠ ⊥)
    (h₂ : p.1 ≠ 0 ∨ p.2 ≠ ⊤) (h₃ : p.1 ≠ ⊥ ∨ p.2 ≠ 0) (h₄ : p.1 ≠ ⊤ ∨ p.2 ≠ 0) :
    ContinuousAt (fun p : EReal × EReal ↦ p.1 * p.2) p := by
  rcases p with ⟨x, y⟩
  induction x <;> induction y
  exact continuousAt_mul_symm3 continuousAt_mul_top_top
  simp only [ne_eq, not_true_eq_false, EReal.coe_eq_zero, false_or] at h₃
  exact continuousAt_mul_symm1 (continuousAt_mul_top_ne_zero h₃)
  exact EReal.neg_top ▸ continuousAt_mul_symm1 continuousAt_mul_top_top
  simp only [ne_eq, EReal.coe_eq_zero, not_true_eq_false, or_false] at h₁
  exact continuousAt_mul_symm2 (continuousAt_mul_swap (continuousAt_mul_top_ne_zero h₁))
  exact continuousAt_mul_coe_coe _ _
  simp only [ne_eq, EReal.coe_eq_zero, not_true_eq_false, or_false] at h₂
  exact continuousAt_mul_swap (continuousAt_mul_top_ne_zero h₂)
  exact continuousAt_mul_symm2 continuousAt_mul_top_top
  simp only [ne_eq, not_true_eq_false, EReal.coe_eq_zero, false_or] at h₄
  exact continuousAt_mul_top_ne_zero h₄
  exact continuousAt_mul_top_top

end EReal
