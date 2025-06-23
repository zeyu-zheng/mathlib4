import Mathlib.Tactic.Have
/-
Copyright (c) 2019 Jean Lo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean Lo, Bhavik Mehta, Yaël Dillies
-/
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.Bornology.Absorbs

/-!
# Local convexity

This file defines absorbent and balanced sets.

An absorbent set is one that "surrounds" the origin. The idea is made precise by requiring that any
point belongs to all large enough scalings of the set. This is the vector world analog of a
topological neighborhood of the origin.

A balanced set is one that is everywhere around the origin. This means that `a • s ⊆ s` for all `a`
of norm less than `1`.

## Main declarations

For a module over a normed ring:
* `Absorbs`: A set `s` absorbs a set `t` if all large scalings of `s` contain `t`.
* `Absorbent`: A set `s` is absorbent if every point eventually belongs to all large scalings of
  `s`.
* `Balanced`: A set `s` is balanced if `a • s ⊆ s` for all `a` of norm less than `1`.

## References

* [H. H. Schaefer, *Topological Vector Spaces*][schaefer1966]

## Tags

absorbent, balanced, locally convex, LCTVS
-/


open Set

open Pointwise Topology

variable {𝕜 𝕝 E : Type*} {ι : Sort*} {κ : ι → Sort*}

section SeminormedRing

variable [SeminormedRing 𝕜]

section SMul

variable [SMul 𝕜 E] {s t u v A B : Set E}
variable (𝕜)

/-- A set `A` is balanced if `a • A` is contained in `A` whenever `a` has norm at most `1`. -/
def Balanced (A : Set E) :=
  ∀ a : 𝕜, ‖a‖ ≤ 1 → a • A ⊆ A

variable {𝕜}

lemma absorbs_iff_norm : Absorbs 𝕜 A B ↔ ∃ r, ∀ c : 𝕜, r ≤ ‖c‖ → B ⊆ c • A :=
  Filter.atTop_basis.cobounded_of_norm.eventually_iff.trans <| by simp only [true_and]; rfl

alias ⟨_, Absorbs.of_norm⟩ := absorbs_iff_norm

lemma Absorbs.exists_pos (h : Absorbs 𝕜 A B) : ∃ r > 0, ∀ c : 𝕜, r ≤ ‖c‖ → B ⊆ c • A :=
  let ⟨r, hr₁, hr⟩ := (Filter.atTop_basis' 1).cobounded_of_norm.eventually_iff.1 h
  ⟨r, one_pos.trans_le hr₁, hr⟩

theorem balanced_iff_smul_mem : Balanced 𝕜 s ↔ ∀ ⦃a : 𝕜⦄, ‖a‖ ≤ 1 → ∀ ⦃x : E⦄, x ∈ s → a • x ∈ s :=
  forall₂_congr fun _a _ha => smul_set_subset_iff

alias ⟨Balanced.smul_mem, _⟩ := balanced_iff_smul_mem

theorem balanced_iff_closedBall_smul : Balanced 𝕜 s ↔ Metric.closedBall (0 : 𝕜) 1 • s ⊆ s := by
  simp [balanced_iff_smul_mem, smul_subset_iff]

@[simp]
theorem balanced_empty : Balanced 𝕜 (∅ : Set E) := fun _ _ => by rw [smul_set_empty]

@[simp]
theorem balanced_univ : Balanced 𝕜 (univ : Set E) := fun _a _ha => subset_univ _

theorem Balanced.union (hA : Balanced 𝕜 A) (hB : Balanced 𝕜 B) : Balanced 𝕜 (A ∪ B) := fun _a ha =>
  smul_set_union.subset.trans <| union_subset_union (hA _ ha) <| hB _ ha

theorem Balanced.inter (hA : Balanced 𝕜 A) (hB : Balanced 𝕜 B) : Balanced 𝕜 (A ∩ B) := fun _a ha =>
  smul_set_inter_subset.trans <| inter_subset_inter (hA _ ha) <| hB _ ha

theorem balanced_iUnion {f : ι → Set E} (h : ∀ i, Balanced 𝕜 (f i)) : Balanced 𝕜 (⋃ i, f i) :=
  fun _a ha => (smul_set_iUnion _ _).subset.trans <| iUnion_mono fun _ => h _ _ ha

theorem balanced_iUnion₂ {f : ∀ i, κ i → Set E} (h : ∀ i j, Balanced 𝕜 (f i j)) :
    Balanced 𝕜 (⋃ (i) (j), f i j) :=
  balanced_iUnion fun _ => balanced_iUnion <| h _

theorem balanced_iInter {f : ι → Set E} (h : ∀ i, Balanced 𝕜 (f i)) : Balanced 𝕜 (⋂ i, f i) :=
  fun _a ha => (smul_set_iInter_subset _ _).trans <| iInter_mono fun _ => h _ _ ha

theorem balanced_iInter₂ {f : ∀ i, κ i → Set E} (h : ∀ i j, Balanced 𝕜 (f i j)) :
    Balanced 𝕜 (⋂ (i) (j), f i j) :=
  balanced_iInter fun _ => balanced_iInter <| h _

variable [SMul 𝕝 E] [SMulCommClass 𝕜 𝕝 E]

theorem Balanced.smul (a : 𝕝) (hs : Balanced 𝕜 s) : Balanced 𝕜 (a • s) := fun _b hb =>
  (smul_comm _ _ _).subset.trans <| smul_set_mono <| hs _ hb

end SMul

section Module

variable [AddCommGroup E] [Module 𝕜 E] {s s₁ s₂ t t₁ t₂ : Set E}

theorem Balanced.neg : Balanced 𝕜 s → Balanced 𝕜 (-s) :=
  forall₂_imp fun _ _ h => (smul_set_neg _ _).subset.trans <| neg_subset_neg.2 h

@[simp]
theorem balanced_neg : Balanced 𝕜 (-s) ↔ Balanced 𝕜 s :=
  ⟨fun h ↦ neg_neg s ▸ h.neg, fun h ↦ h.neg⟩

theorem Balanced.neg_mem_iff [NormOneClass 𝕜] (h : Balanced 𝕜 s) {x : E} : -x ∈ s ↔ x ∈ s :=
  ⟨fun hx ↦ by simpa using h.smul_mem (a := -1) (by simp) hx,
    fun hx ↦ by simpa using h.smul_mem (a := -1) (by simp) hx⟩

theorem Balanced.neg_eq [NormOneClass 𝕜] (h : Balanced 𝕜 s) : -s = s :=
  Set.ext fun _ ↦ h.neg_mem_iff

theorem Balanced.add (hs : Balanced 𝕜 s) (ht : Balanced 𝕜 t) : Balanced 𝕜 (s + t) := fun _a ha =>
  (smul_add _ _ _).subset.trans <| add_subset_add (hs _ ha) <| ht _ ha

theorem Balanced.sub (hs : Balanced 𝕜 s) (ht : Balanced 𝕜 t) : Balanced 𝕜 (s - t) := by
  simp_rw [sub_eq_add_neg]
  exact hs.add ht.neg

theorem balanced_zero : Balanced 𝕜 (0 : Set E) := fun _a _ha => (smul_zero _).subset

end Module

end SeminormedRing

section NormedDivisionRing

variable [NormedDivisionRing 𝕜] [AddCommGroup E] [Module 𝕜 E] {s t : Set E} {x : E} {a b : 𝕜}

theorem absorbs_iff_eventually_nhdsWithin_zero :
    Absorbs 𝕜 s t ↔ ∀ᶠ c : 𝕜 in 𝓝[≠] 0, MapsTo (c • ·) t s := by
  rw [absorbs_iff_eventually_cobounded_mapsTo, ← Filter.inv_cobounded₀]; rfl

alias ⟨Absorbs.eventually_nhdsWithin_zero, _⟩ := absorbs_iff_eventually_nhdsWithin_zero

theorem absorbent_iff_eventually_nhdsWithin_zero :
    Absorbent 𝕜 s ↔ ∀ x : E, ∀ᶠ c : 𝕜 in 𝓝[≠] 0, c • x ∈ s :=
  forall_congr' fun x ↦ by simp only [absorbs_iff_eventually_nhdsWithin_zero, mapsTo_singleton]

alias ⟨Absorbent.eventually_nhdsWithin_zero, _⟩ := absorbent_iff_eventually_nhdsWithin_zero

theorem absorbs_iff_eventually_nhds_zero (h₀ : 0 ∈ s) :
    Absorbs 𝕜 s t ↔ ∀ᶠ c : 𝕜 in 𝓝 0, MapsTo (c • ·) t s := by
  rw [← nhdsWithin_compl_singleton_sup_pure, Filter.eventually_sup, Filter.eventually_pure,
    ← absorbs_iff_eventually_nhdsWithin_zero, and_iff_left]
  intro x _
  simpa only [zero_smul]

theorem Absorbs.eventually_nhds_zero (h : Absorbs 𝕜 s t) (h₀ : 0 ∈ s) :
    ∀ᶠ c : 𝕜 in 𝓝 0, MapsTo (c • ·) t s :=
  (absorbs_iff_eventually_nhds_zero h₀).1 h

end NormedDivisionRing

section NormedField

variable [NormedField 𝕜] [NormedRing 𝕝] [NormedSpace 𝕜 𝕝] [AddCommGroup E] [Module 𝕜 E]
  [SMulWithZero 𝕝 E] [IsScalarTower 𝕜 𝕝 E] {s t u v A B : Set E} {x : E} {a b : 𝕜}

/-- Scalar multiplication (by possibly different types) of a balanced set is monotone. -/
theorem Balanced.smul_mono (hs : Balanced 𝕝 s) {a : 𝕝} {b : 𝕜} (h : ‖a‖ ≤ ‖b‖) : a • s ⊆ b • s := by
  obtain rfl | hb := eq_or_ne b 0
  rw [norm_zero, norm_le_zero_iff] at h
  simp only [h, ← image_smul, zero_smul, Subset.rfl]
  calc
    a • s = b • (b⁻¹ • a) • s := by rw [smul_assoc, smul_inv_smul₀ hb]
    _ ⊆ b • s := smul_set_mono <| hs _ <| by
      rw [norm_smul, norm_inv, ← div_eq_inv_mul]
      exact div_le_one_of_le h (norm_nonneg _)

theorem Balanced.smul_mem_mono [SMulCommClass 𝕝 𝕜 E] (hs : Balanced 𝕝 s) {a : 𝕜} {b : 𝕝}
    (ha : a • x ∈ s) (hba : ‖b‖ ≤ ‖a‖) : b • x ∈ s := by
  rcases eq_or_ne a 0 with rfl | ha₀
  simp_all
  calc
    b • x = (a⁻¹ • b) • a • x := by rw [smul_comm, smul_assoc, smul_inv_smul₀ ha₀]
    _ ∈ s := by
      refine hs.smul_mem ?_ ha
      rw [norm_smul, norm_inv, ← div_eq_inv_mul]
      exact div_le_one_of_le hba (norm_nonneg _)

theorem Balanced.subset_smul (hA : Balanced 𝕜 A) (ha : 1 ≤ ‖a‖) : A ⊆ a • A := by
  rw [← @norm_one 𝕜] at ha; simpa using hA.smul_mono ha

theorem Balanced.smul_congr (hs : Balanced 𝕜 A) (h : ‖a‖ = ‖b‖) : a • A = b • A :=
  (hs.smul_mono h.le).antisymm (hs.smul_mono h.ge)

theorem Balanced.smul_eq (hA : Balanced 𝕜 A) (ha : ‖a‖ = 1) : a • A = A :=
  (hA _ ha.le).antisymm <| hA.subset_smul ha.ge

/-- A balanced set absorbs itself. -/
theorem Balanced.absorbs_self (hA : Balanced 𝕜 A) : Absorbs 𝕜 A A :=
  .of_norm ⟨1, fun _ => hA.subset_smul⟩

theorem Balanced.smul_mem_iff (hs : Balanced 𝕜 s) (h : ‖a‖ = ‖b‖) : a • x ∈ s ↔ b • x ∈ s :=
  ⟨(hs.smul_mem_mono · h.ge), (hs.smul_mem_mono · h.le)⟩

@[deprecated (since := "2024-02-02")] alias Balanced.mem_smul_iff := Balanced.smul_mem_iff

variable [TopologicalSpace E] [ContinuousSMul 𝕜 E]

/-- Every neighbourhood of the origin is absorbent. -/
theorem absorbent_nhds_zero (hA : A ∈ 𝓝 (0 : E)) : Absorbent 𝕜 A :=
  absorbent_iff_inv_smul.2 fun x ↦ Filter.tendsto_inv₀_cobounded.smul tendsto_const_nhds <| by
    rwa [zero_smul]

/-- The union of `{0}` with the interior of a balanced set is balanced. -/
theorem Balanced.zero_insert_interior (hA : Balanced 𝕜 A) :
    Balanced 𝕜 (insert 0 (interior A)) := by
  intro a ha
  obtain rfl | h := eq_or_ne a 0
  · rw [zero_smul_set]
    exacts [subset_union_left, ⟨0, Or.inl rfl⟩]
  rw [← image_smul, image_insert_eq, smul_zero]
  apply insert_subset_insert
  exact ((isOpenMap_smul₀ h).mapsTo_interior <| hA.smul_mem ha).image_subset

@[deprecated Balanced.zero_insert_interior (since := "2024-02-03")]
theorem balanced_zero_union_interior (hA : Balanced 𝕜 A) : Balanced 𝕜 ((0 : Set E) ∪ interior A) :=
  hA.zero_insert_interior

/-- The interior of a balanced set is balanced if it contains the origin. -/
protected theorem Balanced.interior (hA : Balanced 𝕜 A) (h : (0 : E) ∈ interior A) :
    Balanced 𝕜 (interior A) := by
  rw [← insert_eq_self.2 h]
  exact hA.zero_insert_interior

protected theorem Balanced.closure (hA : Balanced 𝕜 A) : Balanced 𝕜 (closure A) := fun _a ha =>
  (image_closure_subset_closure_image <| continuous_const_smul _).trans <|
    closure_mono <| hA _ ha

end NormedField

section NontriviallyNormedField

variable [NontriviallyNormedField 𝕜] [AddCommGroup E] [Module 𝕜 E] {s : Set E}

@[deprecated Absorbent.zero_mem (since := "2024-02-02")]
theorem Absorbent.zero_mem' (hs : Absorbent 𝕜 s) : (0 : E) ∈ s := hs.zero_mem

variable [Module ℝ E] [SMulCommClass ℝ 𝕜 E]

protected theorem Balanced.convexHull (hs : Balanced 𝕜 s) : Balanced 𝕜 (convexHull ℝ s) := by
  suffices Convex ℝ { x | ∀ a : 𝕜, ‖a‖ ≤ 1 → a • x ∈ convexHull ℝ s } by
    rw [balanced_iff_smul_mem] at hs ⊢
    refine fun a ha x hx => convexHull_min ?_ this hx a ha
    exact fun y hy a ha => subset_convexHull ℝ s (hs ha hy)
  intro x hx y hy u v hu hv huv a ha
  simp only [smul_add, ← smul_comm]
  exact convex_convexHull ℝ s (hx a ha) (hy a ha) hu hv huv

@[deprecated (since := "2024-02-02")] alias balanced_convexHull_of_balanced := Balanced.convexHull

end NontriviallyNormedField

section Real

variable [AddCommGroup E] [Module ℝ E] {s : Set E}

theorem balanced_iff_neg_mem (hs : Convex ℝ s) : Balanced ℝ s ↔ ∀ ⦃x⦄, x ∈ s → -x ∈ s := by
  refine ⟨fun h x => h.neg_mem_iff.2, fun h a ha => smul_set_subset_iff.2 fun x hx => ?_⟩
  rw [Real.norm_eq_abs, abs_le] at ha
  rw [show a = -((1 - a) / 2) + (a - -1) / 2 by ring, add_smul, neg_smul, ← smul_neg]
  exact hs (h hx) hx (div_nonneg (sub_nonneg_of_le ha.2) zero_le_two)
    (div_nonneg (sub_nonneg_of_le ha.1) zero_le_two) (by ring)

end Real
