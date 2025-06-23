import Mathlib.Tactic.Have
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.UniformGroup

/-!
# Infinite sums and products in topological groups

Lemmas on topological sums in groups (as opposed to monoids).
-/

noncomputable section

open Filter Finset Function

open scoped Topology

variable {α β γ δ : Type*}

section TopologicalGroup

variable [CommGroup α] [TopologicalSpace α] [TopologicalGroup α]
variable {f g : β → α} {a a₁ a₂ : α}

-- `by simpa using` speeds up elaboration. Why?
@[to_additive]
theorem HasProd.inv (h : HasProd f a) : HasProd (fun b ↦ (f b)⁻¹) a⁻¹ := by
  simpa only using h.map (MonoidHom.id α)⁻¹ continuous_inv

@[to_additive]
theorem Multipliable.inv (hf : Multipliable f) : Multipliable fun b ↦ (f b)⁻¹ :=
  hf.hasProd.inv.multipliable

@[to_additive]
theorem Multipliable.of_inv (hf : Multipliable fun b ↦ (f b)⁻¹) : Multipliable f := by
  simpa only [inv_inv] using hf.inv

@[to_additive]
theorem multipliable_inv_iff : (Multipliable fun b ↦ (f b)⁻¹) ↔ Multipliable f :=
  ⟨Multipliable.of_inv, Multipliable.inv⟩

@[to_additive]
theorem HasProd.div (hf : HasProd f a₁) (hg : HasProd g a₂) :
    HasProd (fun b ↦ f b / g b) (a₁ / a₂) := by
  simp only [div_eq_mul_inv]
  exact hf.mul hg.inv

@[to_additive]
theorem Multipliable.div (hf : Multipliable f) (hg : Multipliable g) :
    Multipliable fun b ↦ f b / g b :=
  (hf.hasProd.div hg.hasProd).multipliable

@[to_additive]
theorem Multipliable.trans_div (hg : Multipliable g) (hfg : Multipliable fun b ↦ f b / g b) :
    Multipliable f := by
  simpa only [div_mul_cancel] using hfg.mul hg

@[to_additive]
theorem multipliable_iff_of_multipliable_div (hfg : Multipliable fun b ↦ f b / g b) :
    Multipliable f ↔ Multipliable g :=
  ⟨fun hf ↦ hf.trans_div <| by simpa only [inv_div] using hfg.inv, fun hg ↦ hg.trans_div hfg⟩

@[to_additive]
theorem HasProd.update (hf : HasProd f a₁) (b : β) [DecidableEq β] (a : α) :
    HasProd (update f b a) (a / f b * a₁) := by
  convert (hasProd_ite_eq b (a / f b)).mul hf with b'
  by_cases h : b' = b
  rw [h, update_same]
  simp [eq_self_iff_true, if_true, sub_add_cancel]
  simp only [h, update_noteq, if_false, Ne, one_mul, not_false_iff]

@[to_additive]
theorem Multipliable.update (hf : Multipliable f) (b : β) [DecidableEq β] (a : α) :
    Multipliable (update f b a) :=
  (hf.hasProd.update b a).multipliable

@[to_additive]
theorem HasProd.hasProd_compl_iff {s : Set β} (hf : HasProd (f ∘ (↑) : s → α) a₁) :
    HasProd (f ∘ (↑) : ↑sᶜ → α) a₂ ↔ HasProd f (a₁ * a₂) := by
  refine ⟨fun h ↦ hf.mul_compl h, fun h ↦ ?_⟩
  rw [hasProd_subtype_iff_mulIndicator] at hf ⊢
  rw [Set.mulIndicator_compl]
  simpa only [div_eq_mul_inv, mul_inv_cancel_comm] using h.div hf

@[to_additive]
theorem HasProd.hasProd_iff_compl {s : Set β} (hf : HasProd (f ∘ (↑) : s → α) a₁) :
    HasProd f a₂ ↔ HasProd (f ∘ (↑) : ↑sᶜ → α) (a₂ / a₁) :=
  Iff.symm <| hf.hasProd_compl_iff.trans <| by rw [mul_div_cancel]

@[to_additive]
theorem Multipliable.multipliable_compl_iff {s : Set β} (hf : Multipliable (f ∘ (↑) : s → α)) :
    Multipliable (f ∘ (↑) : ↑sᶜ → α) ↔ Multipliable f where
  mp := fun ⟨_, ha⟩ ↦ (hf.hasProd.hasProd_compl_iff.1 ha).multipliable
  mpr := fun ⟨_, ha⟩ ↦ (hf.hasProd.hasProd_iff_compl.1 ha).multipliable

@[to_additive]
protected theorem Finset.hasProd_compl_iff (s : Finset β) :
    HasProd (fun x : { x // x ∉ s } ↦ f x) a ↔ HasProd f (a * ∏ i ∈ s, f i) :=
  (s.hasProd f).hasProd_compl_iff.trans <| by rw [mul_comm]

@[to_additive]
protected theorem Finset.hasProd_iff_compl (s : Finset β) :
    HasProd f a ↔ HasProd (fun x : { x // x ∉ s } ↦ f x) (a / ∏ i ∈ s, f i) :=
  (s.hasProd f).hasProd_iff_compl

@[to_additive]
protected theorem Finset.multipliable_compl_iff (s : Finset β) :
    (Multipliable fun x : { x // x ∉ s } ↦ f x) ↔ Multipliable f :=
  (s.multipliable f).multipliable_compl_iff

@[to_additive]
theorem Set.Finite.multipliable_compl_iff {s : Set β} (hs : s.Finite) :
    Multipliable (f ∘ (↑) : ↑sᶜ → α) ↔ Multipliable f :=
  (hs.multipliable f).multipliable_compl_iff

@[to_additive]
theorem hasProd_ite_div_hasProd [DecidableEq β] (hf : HasProd f a) (b : β) :
    HasProd (fun n ↦ ite (n = b) 1 (f n)) (a / f b) := by
  convert hf.update b 1 using 1
  ext n
  rw [Function.update_apply]
  rw [div_mul_eq_mul_div, one_mul]

section tprod

variable [T2Space α]

@[to_additive]
theorem tprod_inv : ∏' b, (f b)⁻¹ = (∏' b, f b)⁻¹ := by
  by_cases hf : Multipliable f
  exact hf.hasProd.inv.tprod_eq
  simp [tprod_eq_one_of_not_multipliable hf,
    tprod_eq_one_of_not_multipliable (mt Multipliable.of_inv hf)]

@[to_additive]
theorem tprod_div (hf : Multipliable f) (hg : Multipliable g) :
    ∏' b, (f b / g b) = (∏' b, f b) / ∏' b, g b :=
  (hf.hasProd.div hg.hasProd).tprod_eq

@[to_additive]
theorem prod_mul_tprod_compl {s : Finset β} (hf : Multipliable f) :
    (∏ x ∈ s, f x) * ∏' x : ↑(s : Set β)ᶜ, f x = ∏' x, f x :=
  ((s.hasProd f).mul_compl (s.multipliable_compl_iff.2 hf).hasProd).tprod_eq.symm

/-- Let `f : β → α` be a multipliable function and let `b ∈ β` be an index.
Lemma `tprod_eq_mul_tprod_ite` writes `∏ n, f n` as `f b` times the product of the
remaining terms. -/
@[to_additive "Let `f : β → α` be a summable function and let `b ∈ β` be an index.
Lemma `tsum_eq_add_tsum_ite` writes `Σ' n, f n` as `f b` plus the sum of the
remaining terms."]
theorem tprod_eq_mul_tprod_ite [DecidableEq β] (hf : Multipliable f) (b : β) :
    ∏' n, f n = f b * ∏' n, ite (n = b) 1 (f n) := by
  rw [(hasProd_ite_div_hasProd hf.hasProd b).tprod_eq]
  exact (mul_div_cancel _ _).symm

end tprod

end TopologicalGroup

section UniformGroup

variable [CommGroup α] [UniformSpace α]

/-- The **Cauchy criterion** for infinite products, also known as the **Cauchy convergence test** -/
@[to_additive "The **Cauchy criterion** for infinite sums, also known as the
**Cauchy convergence test**"]
theorem multipliable_iff_cauchySeq_finset [CompleteSpace α] {f : β → α} :
    Multipliable f ↔ CauchySeq fun s : Finset β ↦ ∏ b ∈ s, f b := by
  classical exact cauchy_map_iff_exists_tendsto.symm

variable [UniformGroup α] {f g : β → α} {a a₁ a₂ : α}

open Classical in
@[to_additive]
theorem cauchySeq_finset_iff_prod_vanishing :
    (CauchySeq fun s : Finset β ↦ ∏ b ∈ s, f b) ↔
      ∀ e ∈ 𝓝 (1 : α), ∃ s : Finset β, ∀ t, Disjoint t s → (∏ b ∈ t, f b) ∈ e := by
  simp only [CauchySeq, cauchy_map_iff, and_iff_right atTop_neBot, prod_atTop_atTop_eq,
    uniformity_eq_comap_nhds_one α, tendsto_comap_iff, (· ∘ ·), atTop_neBot, true_and]
  rw [tendsto_atTop']
  constructor
  intro h e he
  obtain ⟨⟨s₁, s₂⟩, h⟩ := h e he
  use s₁ ∪ s₂
  intro t ht
  specialize h (s₁ ∪ s₂, s₁ ∪ s₂ ∪ t) ⟨le_sup_left, le_sup_of_le_left le_sup_right⟩
  simpa only [Finset.prod_union ht.symm, mul_div_cancel_left] using h
  rintro h e he
  rcases exists_nhds_split_inv he with ⟨d, hd, hde⟩
  rcases h d hd with ⟨s, h⟩
  use (s, s)
  rintro ⟨t₁, t₂⟩ ⟨ht₁, ht₂⟩
  have : ((∏ b ∈ t₂, f b) / ∏ b ∈ t₁, f b) = (∏ b ∈ t₂ \ s, f b) / ∏ b ∈ t₁ \ s, f b
  rw [← Finset.prod_sdiff ht₁, ← Finset.prod_sdiff ht₂, mul_div_mul_right_eq_div]
  simp only [this]
  exact hde _ (h _ Finset.sdiff_disjoint) _ (h _ Finset.sdiff_disjoint)

open Classical in
@[to_additive]
theorem cauchySeq_finset_iff_tprod_vanishing :
    (CauchySeq fun s : Finset β ↦ ∏ b ∈ s, f b) ↔
      ∀ e ∈ 𝓝 (1 : α), ∃ s : Finset β, ∀ t : Set β, Disjoint t s → (∏' b : t, f b) ∈ e := by
  simp_rw [cauchySeq_finset_iff_prod_vanishing, Set.disjoint_left, disjoint_left]
  refine ⟨fun vanish e he ↦ ?_, fun vanish e he ↦ ?_⟩
  obtain ⟨o, ho, o_closed, oe⟩ := exists_mem_nhds_isClosed_subset he
  obtain ⟨s, hs⟩ := vanish o ho
  refine ⟨s, fun t hts ↦ oe ?_⟩
  by_cases ht : Multipliable fun a : t ↦ f a
  refine o_closed.mem_of_tendsto ht.hasProd (eventually_of_forall fun t' ↦ ?_)
  rw [← prod_subtype_map_embedding fun _ _ ↦ by rfl]
  apply hs
  simp_rw [Finset.mem_map]
  rintro _ ⟨b, -, rfl⟩
  exact hts b.prop
  exact tprod_eq_one_of_not_multipliable ht ▸ mem_of_mem_nhds ho
  obtain ⟨s, hs⟩ := vanish _ he
  exact ⟨s, fun t hts ↦ (t.tprod_subtype f).symm ▸ hs _ hts⟩

variable [CompleteSpace α]

@[to_additive]
theorem multipliable_iff_vanishing :
    Multipliable f ↔
    ∀ e ∈ 𝓝 (1 : α), ∃ s : Finset β, ∀ t, Disjoint t s → (∏ b ∈ t, f b) ∈ e := by
  rw [multipliable_iff_cauchySeq_finset, cauchySeq_finset_iff_prod_vanishing]

@[to_additive]
theorem multipliable_iff_tprod_vanishing : Multipliable f ↔
    ∀ e ∈ 𝓝 (1 : α), ∃ s : Finset β, ∀ t : Set β, Disjoint t s → (∏' b : t, f b) ∈ e := by
  rw [multipliable_iff_cauchySeq_finset, cauchySeq_finset_iff_tprod_vanishing]

open Classical in
-- TODO: generalize to monoid with a uniform continuous subtraction operator: `(a + b) - b = a`
@[to_additive]
theorem Multipliable.multipliable_of_eq_one_or_self (hf : Multipliable f)
    (h : ∀ b, g b = 1 ∨ g b = f b) : Multipliable g := by
  exact multipliable_iff_vanishing.2 fun e he ↦
    let ⟨s, hs⟩ := multipliable_iff_vanishing.1 hf e he
    ⟨s, fun t ht ↦
      have eq : ∏ b ∈ t.filter fun b ↦ g b = f b, f b = ∏ b ∈ t, g b :=
        calc
          ∏ b ∈ t.filter fun b ↦ g b = f b, f b = ∏ b ∈ t.filter fun b ↦ g b = f b, g b :=
            Finset.prod_congr rfl fun b hb ↦ (Finset.mem_filter.1 hb).2.symm
          _ = ∏ b ∈ t, g b := by
           {refine Finset.prod_subset (Finset.filter_subset _ _) ?_
            intro b hbt hb
            simp only [Finset.mem_filter, and_iff_right hbt] at hb
            exact (h b).resolve_right hb}
      eq ▸ hs _ <| Finset.disjoint_of_subset_left (Finset.filter_subset _ _) ht⟩

@[to_additive]
protected theorem Multipliable.mulIndicator (hf : Multipliable f) (s : Set β) :
    Multipliable (s.mulIndicator f) :=
  hf.multipliable_of_eq_one_or_self <| Set.mulIndicator_eq_one_or_self _ _

@[to_additive]
theorem Multipliable.comp_injective {i : γ → β} (hf : Multipliable f) (hi : Injective i) :
    Multipliable (f ∘ i) := by
  simpa only [Set.mulIndicator_range_comp] using
    (hi.multipliable_iff (fun x hx ↦ Set.mulIndicator_of_not_mem hx _)).2
    (hf.mulIndicator (Set.range i))

@[to_additive]
theorem Multipliable.subtype (hf : Multipliable f) (s : Set β) : Multipliable (f ∘ (↑) : s → α) :=
  hf.comp_injective Subtype.coe_injective

@[to_additive]
theorem multipliable_subtype_and_compl {s : Set β} :
    ((Multipliable fun x : s ↦ f x) ∧ Multipliable fun x : ↑sᶜ ↦ f x) ↔ Multipliable f :=
  ⟨and_imp.2 Multipliable.mul_compl, fun h ↦ ⟨h.subtype s, h.subtype sᶜ⟩⟩

@[to_additive]
theorem tprod_subtype_mul_tprod_subtype_compl [T2Space α] {f : β → α} (hf : Multipliable f)
    (s : Set β) : (∏' x : s, f x) * ∏' x : ↑sᶜ, f x = ∏' x, f x :=
  ((hf.subtype s).hasProd.mul_compl (hf.subtype { x | x ∉ s }).hasProd).unique hf.hasProd

@[to_additive]
theorem prod_mul_tprod_subtype_compl [T2Space α] {f : β → α} (hf : Multipliable f) (s : Finset β) :
    (∏ x ∈ s, f x) * ∏' x : { x // x ∉ s }, f x = ∏' x, f x := by
  rw [← tprod_subtype_mul_tprod_subtype_compl hf s]
  simp only [Finset.tprod_subtype', mul_right_inj]
  rfl

end UniformGroup

section TopologicalGroup

variable {G : Type*} [TopologicalSpace G] [CommGroup G] [TopologicalGroup G] {f : α → G}

open Classical in
@[to_additive]
theorem Multipliable.vanishing (hf : Multipliable f) ⦃e : Set G⦄ (he : e ∈ 𝓝 (1 : G)) :
    ∃ s : Finset α, ∀ t, Disjoint t s → (∏ k ∈ t, f k) ∈ e := by
  letI : UniformSpace G := TopologicalGroup.toUniformSpace G
  have : UniformGroup G := comm_topologicalGroup_is_uniform
  exact cauchySeq_finset_iff_prod_vanishing.1 hf.hasProd.cauchySeq e he

open Classical in
@[to_additive]
theorem Multipliable.tprod_vanishing (hf : Multipliable f) ⦃e : Set G⦄ (he : e ∈ 𝓝 1) :
    ∃ s : Finset α, ∀ t : Set α, Disjoint t s → (∏' b : t, f b) ∈ e := by
  letI : UniformSpace G := TopologicalGroup.toUniformSpace G
  have : UniformGroup G := comm_topologicalGroup_is_uniform
  exact cauchySeq_finset_iff_tprod_vanishing.1 hf.hasProd.cauchySeq e he

open Classical in
/-- The product over the complement of a finset tends to `1` when the finset grows to cover the
whole space. This does not need a multipliability assumption, as otherwise all such products are
one. -/
@[to_additive "The sum over the complement of a finset tends to `0` when the finset grows to cover
the whole space. This does not need a summability assumption, as otherwise all such sums are zero."]
theorem tendsto_tprod_compl_atTop_one (f : α → G) :
    Tendsto (fun s : Finset α ↦ ∏' a : { x // x ∉ s }, f a) atTop (𝓝 1) := by
  by_cases H : Multipliable f
  intro e he
  obtain ⟨s, hs⟩ := H.tprod_vanishing he
  rw [Filter.mem_map, mem_atTop_sets]
  exact ⟨s, fun t hts ↦ hs _ <| Set.disjoint_left.mpr fun a ha has ↦ ha (hts has)⟩
  refine tendsto_const_nhds.congr fun _ ↦ (tprod_eq_one_of_not_multipliable ?_).symm
  rwa [Finset.multipliable_compl_iff]

/-- Product divergence test: if `f` is unconditionally multipliable, then `f x` tends to one along
`cofinite`. -/
@[to_additive "Series divergence test: if `f` is unconditionally summable, then `f x` tends to zero
along `cofinite`."]
theorem Multipliable.tendsto_cofinite_one (hf : Multipliable f) : Tendsto f cofinite (𝓝 1) := by
  intro e he
  rw [Filter.mem_map]
  rcases hf.vanishing he with ⟨s, hs⟩
  refine s.eventually_cofinite_nmem.mono fun x hx ↦ ?_
  simpa using hs {x} (disjoint_singleton_left.2 hx)

@[to_additive]
theorem Multipliable.countable_mulSupport [FirstCountableTopology G] [T1Space G]
    (hf : Multipliable f) : f.mulSupport.Countable := by
  simpa only [ker_nhds] using hf.tendsto_cofinite_one.countable_compl_preimage_ker

@[to_additive]
theorem multipliable_const_iff [Infinite β] [T2Space G] (a : G) :
    Multipliable (fun _ : β ↦ a) ↔ a = 1 := by
  refine ⟨fun h ↦ ?_, ?_⟩
  by_contra ha
  have : {a}ᶜ ∈ 𝓝 1 := compl_singleton_mem_nhds (Ne.symm ha)
  have : Finite β
  simpa [← Set.finite_univ_iff] using h.tendsto_cofinite_one this
  exact not_finite β
  rintro rfl
  exact multipliable_one

@[to_additive (attr := simp)]
theorem tprod_const [T2Space G] (a : G) : ∏' _ : β, a = a ^ (Nat.card β) := by
  rcases finite_or_infinite β with hβ|hβ
  letI : Fintype β := Fintype.ofFinite β
  rw [tprod_eq_prod (s := univ) (fun x hx ↦ (hx (mem_univ x)).elim)]
  simp only [prod_const, Nat.card_eq_fintype_card, Fintype.card]
  simp only [Nat.card_eq_zero_of_infinite, pow_zero]
  rcases eq_or_ne a 1 with rfl|ha
  simp
  apply tprod_eq_one_of_not_multipliable
  simpa [multipliable_const_iff] using ha

end TopologicalGroup
