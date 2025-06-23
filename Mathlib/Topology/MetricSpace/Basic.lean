import Mathlib.Tactic.Have
/-
Copyright (c) 2015, 2017 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Robert Y. Lewis, Johannes Hölzl, Mario Carneiro, Sébastien Gouëzel
-/
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-!
# Metric spaces

This file defines metric spaces and shows some of their basic properties.

Many definitions and theorems expected on metric spaces are already introduced on uniform spaces and
topological spaces. This includes open and closed sets, compactness, completeness, continuity
and uniform continuity.

TODO (anyone): Add "Main results" section.

## Implementation notes
A lot of elementary properties don't require `eq_of_dist_eq_zero`, hence are stated and proven
for `PseudoMetricSpace`s in `PseudoMetric.lean`.

## Tags

metric, pseudo_metric, dist
-/

open Set Filter Bornology
open scoped NNReal Uniformity

universe u v w

variable {α : Type u} {β : Type v} {X ι : Type*}
variable [PseudoMetricSpace α]

/-- We now define `MetricSpace`, extending `PseudoMetricSpace`. -/
class MetricSpace (α : Type u) extends PseudoMetricSpace α : Type u where
  eq_of_dist_eq_zero : ∀ {x y : α}, dist x y = 0 → x = y

/-- Two metric space structures with the same distance coincide. -/
@[ext]
theorem MetricSpace.ext {α : Type*} {m m' : MetricSpace α} (h : m.toDist = m'.toDist) :
    m = m' := by
  cases m; cases m'; congr; ext1; assumption

/-- Construct a metric space structure whose underlying topological space structure
(definitionally) agrees which a pre-existing topology which is compatible with a given distance
function. -/
def MetricSpace.ofDistTopology {α : Type u} [TopologicalSpace α] (dist : α → α → ℝ)
    (dist_self : ∀ x : α, dist x x = 0) (dist_comm : ∀ x y : α, dist x y = dist y x)
    (dist_triangle : ∀ x y z : α, dist x z ≤ dist x y + dist y z)
    (H : ∀ s : Set α, IsOpen s ↔ ∀ x ∈ s, ∃ ε > 0, ∀ y, dist x y < ε → y ∈ s)
    (eq_of_dist_eq_zero : ∀ x y : α, dist x y = 0 → x = y) : MetricSpace α :=
  { PseudoMetricSpace.ofDistTopology dist dist_self dist_comm dist_triangle H with
    eq_of_dist_eq_zero := eq_of_dist_eq_zero _ _ }

variable {γ : Type w} [MetricSpace γ]

theorem eq_of_dist_eq_zero {x y : γ} : dist x y = 0 → x = y :=
  MetricSpace.eq_of_dist_eq_zero

@[simp]
theorem dist_eq_zero {x y : γ} : dist x y = 0 ↔ x = y :=
  Iff.intro eq_of_dist_eq_zero fun this => this ▸ dist_self _

@[simp]
theorem zero_eq_dist {x y : γ} : 0 = dist x y ↔ x = y := by rw [eq_comm, dist_eq_zero]

theorem dist_ne_zero {x y : γ} : dist x y ≠ 0 ↔ x ≠ y := by
  simpa only [not_iff_not] using dist_eq_zero

@[simp]
theorem dist_le_zero {x y : γ} : dist x y ≤ 0 ↔ x = y := by
  simpa [le_antisymm_iff, dist_nonneg] using @dist_eq_zero _ _ x y

@[simp]
theorem dist_pos {x y : γ} : 0 < dist x y ↔ x ≠ y := by
  simpa only [not_le] using not_congr dist_le_zero

theorem eq_of_forall_dist_le {x y : γ} (h : ∀ ε > 0, dist x y ≤ ε) : x = y :=
  eq_of_dist_eq_zero (eq_of_le_of_forall_le_of_dense dist_nonneg h)

/-- Deduce the equality of points from the vanishing of the nonnegative distance-/
theorem eq_of_nndist_eq_zero {x y : γ} : nndist x y = 0 → x = y := by
  simp only [NNReal.eq_iff, ← dist_nndist, imp_self, NNReal.coe_zero, dist_eq_zero]

/-- Characterize the equality of points as the vanishing of the nonnegative distance-/
@[simp]
theorem nndist_eq_zero {x y : γ} : nndist x y = 0 ↔ x = y := by
  simp only [NNReal.eq_iff, ← dist_nndist, imp_self, NNReal.coe_zero, dist_eq_zero]

@[simp]
theorem zero_eq_nndist {x y : γ} : 0 = nndist x y ↔ x = y := by
  simp only [NNReal.eq_iff, ← dist_nndist, imp_self, NNReal.coe_zero, zero_eq_dist]

namespace Metric

variable {x : γ} {s : Set γ}

@[simp] theorem closedBall_zero : closedBall x 0 = {x} := Set.ext fun _ => dist_le_zero

@[simp] theorem sphere_zero : sphere x 0 = {x} := Set.ext fun _ => dist_eq_zero

theorem subsingleton_closedBall (x : γ) {r : ℝ} (hr : r ≤ 0) : (closedBall x r).Subsingleton := by
  rcases hr.lt_or_eq with (hr | rfl)
  rw [closedBall_eq_empty.2 hr]
  exact subsingleton_empty
  rw [closedBall_zero]
  exact subsingleton_singleton

theorem subsingleton_sphere (x : γ) {r : ℝ} (hr : r ≤ 0) : (sphere x r).Subsingleton :=
  (subsingleton_closedBall x hr).anti sphere_subset_closedBall

-- see Note [lower instance priority]
instance (priority := 100) _root_.MetricSpace.instT0Space : T0Space γ where
  t0 _ _ h := eq_of_dist_eq_zero <| Metric.inseparable_iff.1 h

/-- A map between metric spaces is a uniform embedding if and only if the distance between `f x`
and `f y` is controlled in terms of the distance between `x` and `y` and conversely. -/
theorem uniformEmbedding_iff' [MetricSpace β] {f : γ → β} :
    UniformEmbedding f ↔
      (∀ ε > 0, ∃ δ > 0, ∀ {a b : γ}, dist a b < δ → dist (f a) (f b) < ε) ∧
        ∀ δ > 0, ∃ ε > 0, ∀ {a b : γ}, dist (f a) (f b) < ε → dist a b < δ := by
  rw [uniformEmbedding_iff_uniformInducing, uniformInducing_iff, uniformContinuous_iff]

/-- If a `PseudoMetricSpace` is a T₀ space, then it is a `MetricSpace`. -/
abbrev _root_.MetricSpace.ofT0PseudoMetricSpace (α : Type*) [PseudoMetricSpace α] [T0Space α] :
    MetricSpace α where
  toPseudoMetricSpace := ‹_›
  eq_of_dist_eq_zero hdist := (Metric.inseparable_iff.2 hdist).eq

-- see Note [lower instance priority]
/-- A metric space induces an emetric space -/
instance (priority := 100) _root_.MetricSpace.toEMetricSpace : EMetricSpace γ :=
  .ofT0PseudoEMetricSpace γ

theorem isClosed_of_pairwise_le_dist {s : Set γ} {ε : ℝ} (hε : 0 < ε)
    (hs : s.Pairwise fun x y => ε ≤ dist x y) : IsClosed s :=
  isClosed_of_spaced_out (dist_mem_uniformity hε) <| by simpa using hs

theorem closedEmbedding_of_pairwise_le_dist {α : Type*} [TopologicalSpace α] [DiscreteTopology α]
    {ε : ℝ} (hε : 0 < ε) {f : α → γ} (hf : Pairwise fun x y => ε ≤ dist (f x) (f y)) :
    ClosedEmbedding f :=
  closedEmbedding_of_spaced_out (dist_mem_uniformity hε) <| by simpa using hf

/-- If `f : β → α` sends any two distinct points to points at distance at least `ε > 0`, then
`f` is a uniform embedding with respect to the discrete uniformity on `β`. -/
theorem uniformEmbedding_bot_of_pairwise_le_dist {β : Type*} {ε : ℝ} (hε : 0 < ε) {f : β → α}
    (hf : Pairwise fun x y => ε ≤ dist (f x) (f y)) :
    @UniformEmbedding _ _ ⊥ (by infer_instance) f :=
  uniformEmbedding_of_spaced_out (dist_mem_uniformity hε) <| by simpa using hf

end Metric

/-- Build a new metric space from an old one where the bundled uniform structure is provably
(but typically non-definitionaly) equal to some given uniform structure.
See Note [forgetful inheritance].
-/
def MetricSpace.replaceUniformity {γ} [U : UniformSpace γ] (m : MetricSpace γ)
    (H : 𝓤[U] = 𝓤[PseudoEMetricSpace.toUniformSpace]) : MetricSpace γ where
  toPseudoMetricSpace := PseudoMetricSpace.replaceUniformity m.toPseudoMetricSpace H
  eq_of_dist_eq_zero := @eq_of_dist_eq_zero _ _

theorem MetricSpace.replaceUniformity_eq {γ} [U : UniformSpace γ] (m : MetricSpace γ)
    (H : 𝓤[U] = 𝓤[PseudoEMetricSpace.toUniformSpace]) : m.replaceUniformity H = m := by
  ext; rfl

/-- Build a new metric space from an old one where the bundled topological structure is provably
(but typically non-definitionaly) equal to some given topological structure.
See Note [forgetful inheritance].
-/
abbrev MetricSpace.replaceTopology {γ} [U : TopologicalSpace γ] (m : MetricSpace γ)
    (H : U = m.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace) : MetricSpace γ :=
  @MetricSpace.replaceUniformity γ (m.toUniformSpace.replaceTopology H) m rfl

theorem MetricSpace.replaceTopology_eq {γ} [U : TopologicalSpace γ] (m : MetricSpace γ)
    (H : U = m.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace) :
    m.replaceTopology H = m := by
  ext; rfl

/-- One gets a metric space from an emetric space if the edistance
is everywhere finite, by pushing the edistance to reals. We set it up so that the edist and the
uniformity are defeq in the metric space and the emetric space. In this definition, the distance
is given separately, to be able to prescribe some expression which is not defeq to the push-forward
of the edistance to reals. -/
abbrev EMetricSpace.toMetricSpaceOfDist {α : Type u} [EMetricSpace α] (dist : α → α → ℝ)
    (edist_ne_top : ∀ x y : α, edist x y ≠ ⊤) (h : ∀ x y, dist x y = ENNReal.toReal (edist x y)) :
    MetricSpace α :=
  @MetricSpace.ofT0PseudoMetricSpace _
    (PseudoEMetricSpace.toPseudoMetricSpaceOfDist dist edist_ne_top h) _

/-- One gets a metric space from an emetric space if the edistance
is everywhere finite, by pushing the edistance to reals. We set it up so that the edist and the
uniformity are defeq in the metric space and the emetric space. -/
def EMetricSpace.toMetricSpace {α : Type u} [EMetricSpace α] (h : ∀ x y : α, edist x y ≠ ⊤) :
    MetricSpace α :=
  EMetricSpace.toMetricSpaceOfDist (fun x y => ENNReal.toReal (edist x y)) h fun _ _ => rfl

/-- Build a new metric space from an old one where the bundled bornology structure is provably
(but typically non-definitionaly) equal to some given bornology structure.
See Note [forgetful inheritance].
-/
def MetricSpace.replaceBornology {α} [B : Bornology α] (m : MetricSpace α)
    (H : ∀ s, @IsBounded _ B s ↔ @IsBounded _ PseudoMetricSpace.toBornology s) : MetricSpace α :=
  { PseudoMetricSpace.replaceBornology _ H, m with toBornology := B }

theorem MetricSpace.replaceBornology_eq {α} [m : MetricSpace α] [B : Bornology α]
    (H : ∀ s, @IsBounded _ B s ↔ @IsBounded _ PseudoMetricSpace.toBornology s) :
    MetricSpace.replaceBornology _ H = m := by
  ext
  rfl

/-- Metric space structure pulled back by an injective function. Injectivity is necessary to
ensure that `dist x y = 0` only if `x = y`. -/
abbrev MetricSpace.induced {γ β} (f : γ → β) (hf : Function.Injective f) (m : MetricSpace β) :
    MetricSpace γ :=
  { PseudoMetricSpace.induced f m.toPseudoMetricSpace with
    eq_of_dist_eq_zero := fun h => hf (dist_eq_zero.1 h) }

/-- Pull back a metric space structure by a uniform embedding. This is a version of
`MetricSpace.induced` useful in case if the domain already has a `UniformSpace` structure. -/
abbrev UniformEmbedding.comapMetricSpace {α β} [UniformSpace α] [m : MetricSpace β] (f : α → β)
    (h : UniformEmbedding f) : MetricSpace α :=
  .replaceUniformity (.induced f h.inj m) h.comap_uniformity.symm

/-- Pull back a metric space structure by an embedding. This is a version of
`MetricSpace.induced` useful in case if the domain already has a `TopologicalSpace` structure. -/
abbrev Embedding.comapMetricSpace {α β} [TopologicalSpace α] [m : MetricSpace β] (f : α → β)
    (h : Embedding f) : MetricSpace α :=
  .replaceTopology (.induced f h.inj m) h.induced

instance Subtype.metricSpace {α : Type*} {p : α → Prop} [MetricSpace α] :
    MetricSpace (Subtype p) :=
  .induced Subtype.val Subtype.coe_injective ‹_›

@[to_additive]
instance {α : Type*} [MetricSpace α] : MetricSpace αᵐᵒᵖ :=
  MetricSpace.induced MulOpposite.unop MulOpposite.unop_injective ‹_›

instance : MetricSpace Empty where
  dist _ _ := 0
  dist_self _ := rfl
  dist_comm _ _ := rfl
  edist _ _ := 0
  eq_of_dist_eq_zero _ := Subsingleton.elim _ _
  dist_triangle _ _ _ := show (0 : ℝ) ≤ 0 + 0 by rw [add_zero]
  toUniformSpace := inferInstance
  uniformity_dist := Subsingleton.elim _ _

instance : MetricSpace PUnit.{u + 1} where
  dist _ _ := 0
  dist_self _ := rfl
  dist_comm _ _ := rfl
  edist _ _ := 0
  eq_of_dist_eq_zero _ := Subsingleton.elim _ _
  dist_triangle _ _ _ := show (0 : ℝ) ≤ 0 + 0 by rw [add_zero]
  toUniformSpace := inferInstance
  uniformity_dist := by
    simp (config := { contextual := true }) [principal_univ, eq_top_of_neBot (𝓤 PUnit)]

section Real

/-- Instantiate the reals as a metric space. -/
instance Real.metricSpace : MetricSpace ℝ := .ofT0PseudoMetricSpace ℝ

end Real

section NNReal

instance : MetricSpace ℝ≥0 :=
  Subtype.metricSpace

end NNReal

instance [MetricSpace β] : MetricSpace (ULift β) :=
  MetricSpace.induced ULift.down ULift.down_injective ‹_›

section Prod

instance Prod.metricSpaceMax [MetricSpace β] : MetricSpace (γ × β) := .ofT0PseudoMetricSpace _

end Prod

section Pi

open Finset

variable {π : β → Type*} [Fintype β] [∀ b, MetricSpace (π b)]

/-- A finite product of metric spaces is a metric space, with the sup distance. -/
instance metricSpacePi : MetricSpace (∀ b, π b) := .ofT0PseudoMetricSpace _

end Pi

namespace Metric

section SecondCountable

open TopologicalSpace

-- Porting note (#11215): TODO: use `Countable` instead of `Encodable`
/-- A metric space is second countable if one can reconstruct up to any `ε>0` any element of the
space from countably many data. -/
theorem secondCountable_of_countable_discretization {α : Type u} [MetricSpace α]
    (H : ∀ ε > (0 : ℝ), ∃ (β : Type*) (_ : Encodable β) (F : α → β),
      ∀ x y, F x = F y → dist x y ≤ ε) :
    SecondCountableTopology α := by
  refine secondCountable_of_almost_dense_set fun ε ε0 => ?_
  rcases H ε ε0 with ⟨β, fβ, F, hF⟩
  let Finv := rangeSplitting F
  refine ⟨range Finv, ⟨countable_range _, fun x => ?_⟩⟩
  let x' := Finv ⟨F x, mem_range_self _⟩
  have : F x' = F x := apply_rangeSplitting F _
  exact ⟨x', mem_range_self _, hF _ _ this.symm⟩

end SecondCountable

end Metric

section EqRel

-- TODO: add `dist_congr` similar to `edist_congr`?
instance SeparationQuotient.instDist {α : Type u} [PseudoMetricSpace α] :
    Dist (SeparationQuotient α) where
  dist := lift₂ dist fun x y x' y' hx hy ↦ by rw [dist_edist, dist_edist, ← edist_mk x,
    ← edist_mk x', mk_eq_mk.2 hx, mk_eq_mk.2 hy]

theorem SeparationQuotient.dist_mk {α : Type u} [PseudoMetricSpace α] (p q : α) :
    dist (mk p) (mk q) = dist p q :=
  rfl

instance SeparationQuotient.instMetricSpace {α : Type u} [PseudoMetricSpace α] :
    MetricSpace (SeparationQuotient α) :=
  EMetricSpace.toMetricSpaceOfDist dist (surjective_mk.forall₂.2 edist_ne_top) <|
    surjective_mk.forall₂.2 dist_edist

end EqRel

/-!
### `Additive`, `Multiplicative`

The distance on those type synonyms is inherited without change.
-/


open Additive Multiplicative

section

variable [Dist X]

instance : Dist (Additive X) := ‹Dist X›
instance : Dist (Multiplicative X) := ‹Dist X›

@[simp] theorem dist_ofMul (a b : X) : dist (ofMul a) (ofMul b) = dist a b := rfl

@[simp] theorem dist_ofAdd (a b : X) : dist (ofAdd a) (ofAdd b) = dist a b := rfl

@[simp] theorem dist_toMul (a b : Additive X) : dist (toMul a) (toMul b) = dist a b := rfl

@[simp] theorem dist_toAdd (a b : Multiplicative X) : dist (toAdd a) (toAdd b) = dist a b := rfl

end

section

variable [PseudoMetricSpace X]

instance : PseudoMetricSpace (Additive X) := ‹PseudoMetricSpace X›
instance : PseudoMetricSpace (Multiplicative X) := ‹PseudoMetricSpace X›

@[simp] theorem nndist_ofMul (a b : X) : nndist (ofMul a) (ofMul b) = nndist a b := rfl

@[simp] theorem nndist_ofAdd (a b : X) : nndist (ofAdd a) (ofAdd b) = nndist a b := rfl

@[simp] theorem nndist_toMul (a b : Additive X) : nndist (toMul a) (toMul b) = nndist a b := rfl

@[simp]
theorem nndist_toAdd (a b : Multiplicative X) : nndist (toAdd a) (toAdd b) = nndist a b := rfl

end

instance [MetricSpace X] : MetricSpace (Additive X) := ‹MetricSpace X›
instance [MetricSpace X] : MetricSpace (Multiplicative X) := ‹MetricSpace X›

instance MulOpposite.instMetricSpace [MetricSpace X] : MetricSpace Xᵐᵒᵖ :=
  MetricSpace.induced unop unop_injective ‹_›

/-!
### Order dual

The distance on this type synonym is inherited without change.
-/

open OrderDual

section

variable [Dist X]

instance : Dist Xᵒᵈ := ‹Dist X›

@[simp] theorem dist_toDual (a b : X) : dist (toDual a) (toDual b) = dist a b := rfl

@[simp] theorem dist_ofDual (a b : Xᵒᵈ) : dist (ofDual a) (ofDual b) = dist a b := rfl

end

section

variable [PseudoMetricSpace X]

instance : PseudoMetricSpace Xᵒᵈ := ‹PseudoMetricSpace X›

@[simp] theorem nndist_toDual (a b : X) : nndist (toDual a) (toDual b) = nndist a b := rfl

@[simp] theorem nndist_ofDual (a b : Xᵒᵈ) : nndist (ofDual a) (ofDual b) = nndist a b := rfl

end

instance [MetricSpace X] : MetricSpace Xᵒᵈ := ‹MetricSpace X›
