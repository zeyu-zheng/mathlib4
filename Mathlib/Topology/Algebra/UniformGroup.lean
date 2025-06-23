import Mathlib.Tactic.Have
/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Johannes Hölzl
-/
import Mathlib.Topology.UniformSpace.UniformConvergence
import Mathlib.Topology.UniformSpace.UniformEmbedding
import Mathlib.Topology.UniformSpace.CompleteSeparated
import Mathlib.Topology.UniformSpace.Compact
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.DiscreteSubset
import Mathlib.Tactic.Abel

/-!
# Uniform structure on topological groups

This file defines uniform groups and its additive counterpart. These typeclasses should be
preferred over using `[TopologicalSpace α] [TopologicalGroup α]` since every topological
group naturally induces a uniform structure.

## Main declarations
* `UniformGroup` and `UniformAddGroup`: Multiplicative and additive uniform groups, that
  i.e., groups with uniformly continuous `(*)` and `(⁻¹)` / `(+)` and `(-)`.

## Main results

* `TopologicalAddGroup.toUniformSpace` and `comm_topologicalAddGroup_is_uniform` can be used
  to construct a canonical uniformity for a topological add group.

* extension of ℤ-bilinear maps to complete groups (useful for ring completions)

* `QuotientGroup.completeSpace` and `QuotientAddGroup.completeSpace` guarantee that quotients
  of first countable topological groups by normal subgroups are themselves complete. In particular,
  the quotient of a Banach space by a subspace is complete.
-/


noncomputable section

open scoped Classical
open Uniformity Topology Filter Pointwise

section UniformGroup

open Filter Set

variable {α : Type*} {β : Type*}

/-- A uniform group is a group in which multiplication and inversion are uniformly continuous. -/
class UniformGroup (α : Type*) [UniformSpace α] [Group α] : Prop where
  uniformContinuous_div : UniformContinuous fun p : α × α => p.1 / p.2

/-- A uniform additive group is an additive group in which addition
  and negation are uniformly continuous. -/
class UniformAddGroup (α : Type*) [UniformSpace α] [AddGroup α] : Prop where
  uniformContinuous_sub : UniformContinuous fun p : α × α => p.1 - p.2

attribute [to_additive] UniformGroup

@[to_additive]
theorem UniformGroup.mk' {α} [UniformSpace α] [Group α]
    (h₁ : UniformContinuous fun p : α × α => p.1 * p.2) (h₂ : UniformContinuous fun p : α => p⁻¹) :
    UniformGroup α :=
  ⟨by simpa only [div_eq_mul_inv] using
    h₁.comp (uniformContinuous_fst.prod_mk (h₂.comp uniformContinuous_snd))⟩

variable [UniformSpace α] [Group α] [UniformGroup α]

@[to_additive]
theorem uniformContinuous_div : UniformContinuous fun p : α × α => p.1 / p.2 :=
  UniformGroup.uniformContinuous_div

@[to_additive]
theorem UniformContinuous.div [UniformSpace β] {f : β → α} {g : β → α} (hf : UniformContinuous f)
    (hg : UniformContinuous g) : UniformContinuous fun x => f x / g x :=
  uniformContinuous_div.comp (hf.prod_mk hg)

@[to_additive]
theorem UniformContinuous.inv [UniformSpace β] {f : β → α} (hf : UniformContinuous f) :
    UniformContinuous fun x => (f x)⁻¹ := by
  have : UniformContinuous fun x => 1 / f x := uniformContinuous_const.div hf
  simp_all

@[to_additive]
theorem uniformContinuous_inv : UniformContinuous fun x : α => x⁻¹ :=
  uniformContinuous_id.inv

@[to_additive]
theorem UniformContinuous.mul [UniformSpace β] {f : β → α} {g : β → α} (hf : UniformContinuous f)
    (hg : UniformContinuous g) : UniformContinuous fun x => f x * g x := by
  have : UniformContinuous fun x => f x / (g x)⁻¹ := hf.div hg.inv
  simp_all

@[to_additive]
theorem uniformContinuous_mul : UniformContinuous fun p : α × α => p.1 * p.2 :=
  uniformContinuous_fst.mul uniformContinuous_snd

@[to_additive UniformContinuous.const_nsmul]
theorem UniformContinuous.pow_const [UniformSpace β] {f : β → α} (hf : UniformContinuous f) :
    ∀ n : ℕ, UniformContinuous fun x => f x ^ n
  | 0 => by
    simp_rw [pow_zero]
    exact uniformContinuous_const
  | n + 1 => by
    simp_rw [pow_succ']
    exact hf.mul (hf.pow_const n)

@[to_additive uniformContinuous_const_nsmul]
theorem uniformContinuous_pow_const (n : ℕ) : UniformContinuous fun x : α => x ^ n :=
  uniformContinuous_id.pow_const n

@[to_additive UniformContinuous.const_zsmul]
theorem UniformContinuous.zpow_const [UniformSpace β] {f : β → α} (hf : UniformContinuous f) :
    ∀ n : ℤ, UniformContinuous fun x => f x ^ n
  | (n : ℕ) => by
    simp_rw [zpow_natCast]
    exact hf.pow_const _
  | Int.negSucc n => by
    simp_rw [zpow_negSucc]
    exact (hf.pow_const _).inv

@[to_additive uniformContinuous_const_zsmul]
theorem uniformContinuous_zpow_const (n : ℤ) : UniformContinuous fun x : α => x ^ n :=
  uniformContinuous_id.zpow_const n

@[to_additive]
instance (priority := 10) UniformGroup.to_topologicalGroup : TopologicalGroup α where
  continuous_mul := uniformContinuous_mul.continuous
  continuous_inv := uniformContinuous_inv.continuous

@[to_additive]
instance [UniformSpace β] [Group β] [UniformGroup β] : UniformGroup (α × β) :=
  ⟨((uniformContinuous_fst.comp uniformContinuous_fst).div
          (uniformContinuous_fst.comp uniformContinuous_snd)).prod_mk
      ((uniformContinuous_snd.comp uniformContinuous_fst).div
        (uniformContinuous_snd.comp uniformContinuous_snd))⟩

@[to_additive]
instance Pi.instUniformGroup {ι : Type*} {G : ι → Type*} [∀ i, UniformSpace (G i)]
    [∀ i, Group (G i)] [∀ i, UniformGroup (G i)] : UniformGroup (∀ i, G i) where
  uniformContinuous_div := uniformContinuous_pi.mpr fun i ↦
    (uniformContinuous_proj G i).comp uniformContinuous_fst |>.div <|
      (uniformContinuous_proj G i).comp uniformContinuous_snd

@[to_additive]
theorem uniformity_translate_mul (a : α) : ((𝓤 α).map fun x : α × α => (x.1 * a, x.2 * a)) = 𝓤 α :=
  le_antisymm (uniformContinuous_id.mul uniformContinuous_const)
    (calc
      𝓤 α =
          ((𝓤 α).map fun x : α × α => (x.1 * a⁻¹, x.2 * a⁻¹)).map fun x : α × α =>
            (x.1 * a, x.2 * a) := by simp [Filter.map_map, (· ∘ ·)]
      _ ≤ (𝓤 α).map fun x : α × α => (x.1 * a, x.2 * a) :=
        Filter.map_mono (uniformContinuous_id.mul uniformContinuous_const)
      )

@[to_additive]
theorem uniformEmbedding_translate_mul (a : α) : UniformEmbedding fun x : α => x * a :=
  { comap_uniformity := by
      nth_rw 1 [← uniformity_translate_mul a, comap_map]
      rintro ⟨p₁, p₂⟩ ⟨q₁, q₂⟩
      simp only [Prod.mk.injEq, mul_left_inj, imp_self]
    inj := mul_left_injective a }

namespace MulOpposite

@[to_additive]
instance : UniformGroup αᵐᵒᵖ :=
  ⟨uniformContinuous_op.comp
      ((uniformContinuous_unop.comp uniformContinuous_snd).inv.mul <|
        uniformContinuous_unop.comp uniformContinuous_fst)⟩

end MulOpposite

section LatticeOps

variable [Group β]

@[to_additive]
theorem uniformGroup_sInf {us : Set (UniformSpace β)} (h : ∀ u ∈ us, @UniformGroup β u _) :
    @UniformGroup β (sInf us) _ :=
  -- Porting note: {_} does not find `sInf us` instance, see `continuousSMul_sInf`
  @UniformGroup.mk β (_) _ <|
    uniformContinuous_sInf_rng.mpr fun u hu =>
      uniformContinuous_sInf_dom₂ hu hu (@UniformGroup.uniformContinuous_div β u _ (h u hu))

@[to_additive]
theorem uniformGroup_iInf {ι : Sort*} {us' : ι → UniformSpace β}
    (h' : ∀ i, @UniformGroup β (us' i) _) : @UniformGroup β (⨅ i, us' i) _ := by
  rw [← sInf_range]
  exact uniformGroup_sInf (Set.forall_mem_range.mpr h')

@[to_additive]
theorem uniformGroup_inf {u₁ u₂ : UniformSpace β} (h₁ : @UniformGroup β u₁ _)
    (h₂ : @UniformGroup β u₂ _) : @UniformGroup β (u₁ ⊓ u₂) _ := by
  rw [inf_eq_iInf]
  refine uniformGroup_iInf fun b => ?_
  cases b <;> assumption

@[to_additive]
lemma UniformInducing.uniformGroup {γ : Type*} [Group γ] [UniformSpace γ] [UniformGroup γ]
    [UniformSpace β] {F : Type*} [FunLike F β γ] [MonoidHomClass F β γ]
    (f : F) (hf : UniformInducing f) :
    UniformGroup β where
  uniformContinuous_div := by
    simp_rw [hf.uniformContinuous_iff, Function.comp_def, map_div]
    exact uniformContinuous_div.comp (hf.uniformContinuous.prod_map hf.uniformContinuous)

@[to_additive]
protected theorem UniformGroup.comap {γ : Type*} [Group γ] {u : UniformSpace γ} [UniformGroup γ]
    {F : Type*} [FunLike F β γ] [MonoidHomClass F β γ] (f : F) : @UniformGroup β (u.comap f) _ :=
  letI : UniformSpace β := u.comap f; UniformInducing.uniformGroup f ⟨rfl⟩

end LatticeOps

namespace Subgroup

@[to_additive]
instance uniformGroup (S : Subgroup α) : UniformGroup S := .comap S.subtype

end Subgroup

section

variable (α)

@[to_additive]
theorem uniformity_eq_comap_nhds_one : 𝓤 α = comap (fun x : α × α => x.2 / x.1) (𝓝 (1 : α)) := by
  rw [nhds_eq_comap_uniformity, Filter.comap_comap]
  refine le_antisymm (Filter.map_le_iff_le_comap.1 ?_) ?_
  intro s hs
  rcases mem_uniformity_of_uniformContinuous_invariant uniformContinuous_div hs with ⟨t, ht, hts⟩
  refine mem_map.2 (mem_of_superset ht ?_)
  rintro ⟨a, b⟩
  simpa [subset_def] using hts a b a
  intro s hs
  rcases mem_uniformity_of_uniformContinuous_invariant uniformContinuous_mul hs with ⟨t, ht, hts⟩
  refine ⟨_, ht, ?_⟩
  rintro ⟨a, b⟩
  simpa [subset_def] using hts 1 (b / a) a

@[to_additive]
theorem uniformity_eq_comap_nhds_one_swapped :
    𝓤 α = comap (fun x : α × α => x.1 / x.2) (𝓝 (1 : α)) := by
  rw [← comap_swap_uniformity, uniformity_eq_comap_nhds_one, comap_comap]
  rfl

@[to_additive]
theorem UniformGroup.ext {G : Type*} [Group G] {u v : UniformSpace G} (hu : @UniformGroup G u _)
    (hv : @UniformGroup G v _)
    (h : @nhds _ u.toTopologicalSpace 1 = @nhds _ v.toTopologicalSpace 1) : u = v :=
  UniformSpace.ext <| by
    rw [@uniformity_eq_comap_nhds_one _ u _ hu, @uniformity_eq_comap_nhds_one _ v _ hv, h]

@[to_additive]
theorem UniformGroup.ext_iff {G : Type*} [Group G] {u v : UniformSpace G}
    (hu : @UniformGroup G u _) (hv : @UniformGroup G v _) :
    u = v ↔ @nhds _ u.toTopologicalSpace 1 = @nhds _ v.toTopologicalSpace 1 :=
  ⟨fun h => h ▸ rfl, hu.ext hv⟩

variable {α}

@[to_additive]
theorem UniformGroup.uniformity_countably_generated [(𝓝 (1 : α)).IsCountablyGenerated] :
    (𝓤 α).IsCountablyGenerated := by
  rw [uniformity_eq_comap_nhds_one]
  exact Filter.comap.isCountablyGenerated _ _

open MulOpposite

@[to_additive]
theorem uniformity_eq_comap_inv_mul_nhds_one :
    𝓤 α = comap (fun x : α × α => x.1⁻¹ * x.2) (𝓝 (1 : α)) := by
  rw [← comap_uniformity_mulOpposite, uniformity_eq_comap_nhds_one, ← op_one, ← comap_unop_nhds,
    comap_comap, comap_comap]
  simp [(· ∘ ·)]

@[to_additive]
theorem uniformity_eq_comap_inv_mul_nhds_one_swapped :
    𝓤 α = comap (fun x : α × α => x.2⁻¹ * x.1) (𝓝 (1 : α)) := by
  rw [← comap_swap_uniformity, uniformity_eq_comap_inv_mul_nhds_one, comap_comap]
  rfl

end

@[to_additive]
theorem Filter.HasBasis.uniformity_of_nhds_one {ι} {p : ι → Prop} {U : ι → Set α}
    (h : (𝓝 (1 : α)).HasBasis p U) :
    (𝓤 α).HasBasis p fun i => { x : α × α | x.2 / x.1 ∈ U i } := by
  rw [uniformity_eq_comap_nhds_one]
  exact h.comap _

@[to_additive]
theorem Filter.HasBasis.uniformity_of_nhds_one_inv_mul {ι} {p : ι → Prop} {U : ι → Set α}
    (h : (𝓝 (1 : α)).HasBasis p U) :
    (𝓤 α).HasBasis p fun i => { x : α × α | x.1⁻¹ * x.2 ∈ U i } := by
  rw [uniformity_eq_comap_inv_mul_nhds_one]
  exact h.comap _

@[to_additive]
theorem Filter.HasBasis.uniformity_of_nhds_one_swapped {ι} {p : ι → Prop} {U : ι → Set α}
    (h : (𝓝 (1 : α)).HasBasis p U) :
    (𝓤 α).HasBasis p fun i => { x : α × α | x.1 / x.2 ∈ U i } := by
  rw [uniformity_eq_comap_nhds_one_swapped]
  exact h.comap _

@[to_additive]
theorem Filter.HasBasis.uniformity_of_nhds_one_inv_mul_swapped {ι} {p : ι → Prop} {U : ι → Set α}
    (h : (𝓝 (1 : α)).HasBasis p U) :
    (𝓤 α).HasBasis p fun i => { x : α × α | x.2⁻¹ * x.1 ∈ U i } := by
  rw [uniformity_eq_comap_inv_mul_nhds_one_swapped]
  exact h.comap _

@[to_additive]
theorem uniformContinuous_of_tendsto_one {hom : Type*} [UniformSpace β] [Group β] [UniformGroup β]
    [FunLike hom α β] [MonoidHomClass hom α β] {f : hom} (h : Tendsto f (𝓝 1) (𝓝 1)) :
    UniformContinuous f := by
  have :
    ((fun x : β × β => x.2 / x.1) ∘ fun x : α × α => (f x.1, f x.2)) = fun x : α × α =>
      f (x.2 / x.1) := by ext; simp only [Function.comp_apply, map_div]
  rw [UniformContinuous, uniformity_eq_comap_nhds_one α, uniformity_eq_comap_nhds_one β,
    tendsto_comap_iff, this]
  exact Tendsto.comp h tendsto_comap

/-- A group homomorphism (a bundled morphism of a type that implements `MonoidHomClass`) between
two uniform groups is uniformly continuous provided that it is continuous at one. See also
`continuous_of_continuousAt_one`. -/
@[to_additive "An additive group homomorphism (a bundled morphism of a type that implements
`AddMonoidHomClass`) between two uniform additive groups is uniformly continuous provided that it
is continuous at zero. See also `continuous_of_continuousAt_zero`."]
theorem uniformContinuous_of_continuousAt_one {hom : Type*} [UniformSpace β] [Group β]
    [UniformGroup β] [FunLike hom α β] [MonoidHomClass hom α β]
    (f : hom) (hf : ContinuousAt f 1) :
    UniformContinuous f :=
  uniformContinuous_of_tendsto_one (by simpa using hf.tendsto)

@[to_additive]
theorem MonoidHom.uniformContinuous_of_continuousAt_one [UniformSpace β] [Group β] [UniformGroup β]
    (f : α →* β) (hf : ContinuousAt f 1) : UniformContinuous f :=
  _root_.uniformContinuous_of_continuousAt_one f hf

/-- A homomorphism from a uniform group to a discrete uniform group is continuous if and only if
its kernel is open. -/
@[to_additive "A homomorphism from a uniform additive group to a discrete uniform additive group is
continuous if and only if its kernel is open."]
theorem UniformGroup.uniformContinuous_iff_open_ker {hom : Type*} [UniformSpace β]
    [DiscreteTopology β] [Group β] [UniformGroup β] [FunLike hom α β] [MonoidHomClass hom α β]
    {f : hom} :
    UniformContinuous f ↔ IsOpen ((f : α →* β).ker : Set α) := by
  refine ⟨fun hf => ?_, fun hf => ?_⟩
  apply (isOpen_discrete ({1} : Set β)).preimage hf.continuous
  apply uniformContinuous_of_continuousAt_one
  rw [ContinuousAt, nhds_discrete β, map_one, tendsto_pure]
  exact hf.mem_nhds (map_one f)

@[to_additive]
theorem uniformContinuous_monoidHom_of_continuous {hom : Type*} [UniformSpace β] [Group β]
    [UniformGroup β] [FunLike hom α β] [MonoidHomClass hom α β] {f : hom} (h : Continuous f) :
    UniformContinuous f :=
  uniformContinuous_of_tendsto_one <|
    suffices Tendsto f (𝓝 1) (𝓝 (f 1)) by rwa [map_one] at this
    h.tendsto 1

@[to_additive]
theorem CauchySeq.mul {ι : Type*} [Preorder ι] {u v : ι → α} (hu : CauchySeq u)
    (hv : CauchySeq v) : CauchySeq (u * v) :=
  uniformContinuous_mul.comp_cauchySeq (hu.prod hv)

@[to_additive]
theorem CauchySeq.mul_const {ι : Type*} [Preorder ι] {u : ι → α} {x : α} (hu : CauchySeq u) :
    CauchySeq fun n => u n * x :=
  (uniformContinuous_id.mul uniformContinuous_const).comp_cauchySeq hu

@[to_additive]
theorem CauchySeq.const_mul {ι : Type*} [Preorder ι] {u : ι → α} {x : α} (hu : CauchySeq u) :
    CauchySeq fun n => x * u n :=
  (uniformContinuous_const.mul uniformContinuous_id).comp_cauchySeq hu

@[to_additive]
theorem CauchySeq.inv {ι : Type*} [Preorder ι] {u : ι → α} (h : CauchySeq u) :
    CauchySeq u⁻¹ :=
  uniformContinuous_inv.comp_cauchySeq h

@[to_additive]
theorem totallyBounded_iff_subset_finite_iUnion_nhds_one {s : Set α} :
    TotallyBounded s ↔ ∀ U ∈ 𝓝 (1 : α), ∃ t : Set α, t.Finite ∧ s ⊆ ⋃ y ∈ t, y • U :=
  (𝓝 (1 : α)).basis_sets.uniformity_of_nhds_one_inv_mul_swapped.totallyBounded_iff.trans <| by
    simp [← preimage_smul_inv, preimage]

section UniformConvergence

variable {ι : Type*} {l : Filter ι} {l' : Filter β} {f f' : ι → β → α} {g g' : β → α} {s : Set β}

@[to_additive]
theorem TendstoUniformlyOnFilter.mul (hf : TendstoUniformlyOnFilter f g l l')
    (hf' : TendstoUniformlyOnFilter f' g' l l') : TendstoUniformlyOnFilter (f * f') (g * g') l l' :=
  fun u hu =>
  ((uniformContinuous_mul.comp_tendstoUniformlyOnFilter (hf.prod hf')) u hu).diag_of_prod_left

@[to_additive]
theorem TendstoUniformlyOnFilter.div (hf : TendstoUniformlyOnFilter f g l l')
    (hf' : TendstoUniformlyOnFilter f' g' l l') : TendstoUniformlyOnFilter (f / f') (g / g') l l' :=
  fun u hu =>
  ((uniformContinuous_div.comp_tendstoUniformlyOnFilter (hf.prod hf')) u hu).diag_of_prod_left

@[to_additive]
theorem TendstoUniformlyOn.mul (hf : TendstoUniformlyOn f g l s)
    (hf' : TendstoUniformlyOn f' g' l s) : TendstoUniformlyOn (f * f') (g * g') l s := fun u hu =>
  ((uniformContinuous_mul.comp_tendstoUniformlyOn (hf.prod hf')) u hu).diag_of_prod

@[to_additive]
theorem TendstoUniformlyOn.div (hf : TendstoUniformlyOn f g l s)
    (hf' : TendstoUniformlyOn f' g' l s) : TendstoUniformlyOn (f / f') (g / g') l s := fun u hu =>
  ((uniformContinuous_div.comp_tendstoUniformlyOn (hf.prod hf')) u hu).diag_of_prod

@[to_additive]
theorem TendstoUniformly.mul (hf : TendstoUniformly f g l) (hf' : TendstoUniformly f' g' l) :
    TendstoUniformly (f * f') (g * g') l := fun u hu =>
  ((uniformContinuous_mul.comp_tendstoUniformly (hf.prod hf')) u hu).diag_of_prod

@[to_additive]
theorem TendstoUniformly.div (hf : TendstoUniformly f g l) (hf' : TendstoUniformly f' g' l) :
    TendstoUniformly (f / f') (g / g') l := fun u hu =>
  ((uniformContinuous_div.comp_tendstoUniformly (hf.prod hf')) u hu).diag_of_prod

@[to_additive]
theorem UniformCauchySeqOn.mul (hf : UniformCauchySeqOn f l s) (hf' : UniformCauchySeqOn f' l s) :
    UniformCauchySeqOn (f * f') l s := fun u hu => by
  simpa using (uniformContinuous_mul.comp_uniformCauchySeqOn (hf.prod' hf')) u hu

@[to_additive]
theorem UniformCauchySeqOn.div (hf : UniformCauchySeqOn f l s) (hf' : UniformCauchySeqOn f' l s) :
    UniformCauchySeqOn (f / f') l s := fun u hu => by
  simpa using (uniformContinuous_div.comp_uniformCauchySeqOn (hf.prod' hf')) u hu

end UniformConvergence

end UniformGroup

section TopologicalGroup

open Filter

variable (G : Type*) [Group G] [TopologicalSpace G] [TopologicalGroup G]

/-- The right uniformity on a topological group (as opposed to the left uniformity).

Warning: in general the right and left uniformities do not coincide and so one does not obtain a
`UniformGroup` structure. Two important special cases where they _do_ coincide are for
commutative groups (see `comm_topologicalGroup_is_uniform`) and for compact groups (see
`topologicalGroup_is_uniform_of_compactSpace`). -/
@[to_additive "The right uniformity on a topological additive group (as opposed to the left
uniformity).

Warning: in general the right and left uniformities do not coincide and so one does not obtain a
`UniformAddGroup` structure. Two important special cases where they _do_ coincide are for
commutative additive groups (see `comm_topologicalAddGroup_is_uniform`) and for compact
additive groups (see `topologicalAddGroup_is_uniform_of_compactSpace`)."]
def TopologicalGroup.toUniformSpace : UniformSpace G where
  uniformity := comap (fun p : G × G => p.2 / p.1) (𝓝 1)
  symm :=
    have : Tendsto (fun p : G × G ↦ (p.2 / p.1)⁻¹) (comap (fun p : G × G ↦ p.2 / p.1) (𝓝 1))
      (𝓝 1⁻¹) := tendsto_id.inv.comp tendsto_comap
    by simpa [tendsto_comap_iff]
  comp := Tendsto.le_comap fun U H ↦ by
    rcases exists_nhds_one_split H with ⟨V, V_nhds, V_mul⟩
    refine mem_map.2 (mem_of_superset (mem_lift' <| preimage_mem_comap V_nhds) ?_)
    rintro ⟨x, y⟩ ⟨z, hz₁, hz₂⟩
    simpa using V_mul _ hz₂ _ hz₁
  nhds_eq_comap_uniformity _ := by simp only [comap_comap, (· ∘ ·), nhds_translation_div]

attribute [local instance] TopologicalGroup.toUniformSpace

@[to_additive]
theorem uniformity_eq_comap_nhds_one' : 𝓤 G = comap (fun p : G × G => p.2 / p.1) (𝓝 (1 : G)) :=
  rfl

@[to_additive]
theorem topologicalGroup_is_uniform_of_compactSpace [CompactSpace G] : UniformGroup G :=
  ⟨by
    apply CompactSpace.uniformContinuous_of_continuous
    exact continuous_div'⟩

variable {G}

@[to_additive]
instance Subgroup.isClosed_of_discrete [T2Space G] {H : Subgroup G} [DiscreteTopology H] :
    IsClosed (H : Set G) := by
  obtain ⟨V, V_in, VH⟩ : ∃ (V : Set G), V ∈ 𝓝 (1 : G) ∧ V ∩ (H : Set G) = {1} :=
    nhds_inter_eq_singleton_of_mem_discrete H.one_mem
  have : (fun p : G × G => p.2 / p.1) ⁻¹' V ∈ 𝓤 G := preimage_mem_comap V_in
  apply isClosed_of_spaced_out this
  intro h h_in h' h'_in
  contrapose!
  simp only [Set.mem_preimage, not_not]
  rintro (hyp : h' / h ∈ V)
  have : h' / h ∈ ({1} : Set G) := VH ▸ Set.mem_inter hyp (H.div_mem h'_in h_in)
  exact (eq_of_div_eq_one this).symm

@[to_additive]
lemma Subgroup.tendsto_coe_cofinite_of_discrete [T2Space G] (H : Subgroup G) [DiscreteTopology H] :
    Tendsto ((↑) : H → G) cofinite (cocompact _) :=
  IsClosed.tendsto_coe_cofinite_of_discreteTopology inferInstance inferInstance

@[to_additive]
lemma MonoidHom.tendsto_coe_cofinite_of_discrete [T2Space G] {H : Type*} [Group H] {f : H →* G}
    (hf : Function.Injective f) (hf' : DiscreteTopology f.range) :
    Tendsto f cofinite (cocompact _) := by
  replace hf : Function.Injective f.rangeRestrict := by simpa
  exact f.range.tendsto_coe_cofinite_of_discrete.comp hf.tendsto_cofinite

@[to_additive]
theorem TopologicalGroup.tendstoUniformly_iff {ι α : Type*} (F : ι → α → G) (f : α → G)
    (p : Filter ι) :
    @TendstoUniformly α G ι (TopologicalGroup.toUniformSpace G) F f p ↔
      ∀ u ∈ 𝓝 (1 : G), ∀ᶠ i in p, ∀ a, F i a / f a ∈ u :=
  ⟨fun h u hu => h _ ⟨u, hu, fun _ => id⟩, fun h _ ⟨u, hu, hv⟩ =>
    mem_of_superset (h u hu) fun _ hi a => hv (hi a)⟩

@[to_additive]
theorem TopologicalGroup.tendstoUniformlyOn_iff {ι α : Type*} (F : ι → α → G) (f : α → G)
    (p : Filter ι) (s : Set α) :
    @TendstoUniformlyOn α G ι (TopologicalGroup.toUniformSpace G) F f p s ↔
      ∀ u ∈ 𝓝 (1 : G), ∀ᶠ i in p, ∀ a ∈ s, F i a / f a ∈ u :=
  ⟨fun h u hu => h _ ⟨u, hu, fun _ => id⟩, fun h _ ⟨u, hu, hv⟩ =>
    mem_of_superset (h u hu) fun _ hi a ha => hv (hi a ha)⟩

@[to_additive]
theorem TopologicalGroup.tendstoLocallyUniformly_iff {ι α : Type*} [TopologicalSpace α]
    (F : ι → α → G) (f : α → G) (p : Filter ι) :
    @TendstoLocallyUniformly α G ι (TopologicalGroup.toUniformSpace G) _ F f p ↔
      ∀ u ∈ 𝓝 (1 : G), ∀ (x : α), ∃ t ∈ 𝓝 x, ∀ᶠ i in p, ∀ a ∈ t, F i a / f a ∈ u :=
    ⟨fun h u hu => h _ ⟨u, hu, fun _ => id⟩, fun h _ ⟨u, hu, hv⟩ x =>
      Exists.imp (fun _ ⟨h, hp⟩ => ⟨h, mem_of_superset hp fun _ hi a ha => hv (hi a ha)⟩)
        (h u hu x)⟩

@[to_additive]
theorem TopologicalGroup.tendstoLocallyUniformlyOn_iff {ι α : Type*} [TopologicalSpace α]
    (F : ι → α → G) (f : α → G) (p : Filter ι) (s : Set α) :
    @TendstoLocallyUniformlyOn α G ι (TopologicalGroup.toUniformSpace G) _ F f p s ↔
      ∀ u ∈ 𝓝 (1 : G), ∀ x ∈ s, ∃ t ∈ 𝓝[s] x, ∀ᶠ i in p, ∀ a ∈ t, F i a / f a ∈ u :=
  ⟨fun h u hu => h _ ⟨u, hu, fun _ => id⟩, fun h _ ⟨u, hu, hv⟩ x =>
    (Exists.imp fun _ ⟨h, hp⟩ => ⟨h, mem_of_superset hp fun _ hi a ha => hv (hi a ha)⟩) ∘
      h u hu x⟩

end TopologicalGroup

section TopologicalCommGroup

universe u v w x

open Filter

variable (G : Type*) [CommGroup G] [TopologicalSpace G] [TopologicalGroup G]

section

attribute [local instance] TopologicalGroup.toUniformSpace

variable {G}

@[to_additive]
-- Porting note: renamed theorem to conform to naming convention
theorem comm_topologicalGroup_is_uniform : UniformGroup G := by
  have :
    Tendsto
      ((fun p : G × G => p.1 / p.2) ∘ fun p : (G × G) × G × G => (p.1.2 / p.1.1, p.2.2 / p.2.1))
      (comap (fun p : (G × G) × G × G => (p.1.2 / p.1.1, p.2.2 / p.2.1)) ((𝓝 1).prod (𝓝 1)))
      (𝓝 (1 / 1)) :=
    (tendsto_fst.div' tendsto_snd).comp tendsto_comap
  constructor
  rw [UniformContinuous, uniformity_prod_eq_prod, tendsto_map'_iff, uniformity_eq_comap_nhds_one' G,
    tendsto_comap_iff, prod_comap_comap_eq]
  simp only [Function.comp, div_eq_mul_inv, mul_inv_rev, inv_inv, mul_comm, mul_left_comm] at *
  simp only [inv_one, mul_one, ← mul_assoc] at this
  simp_rw [← mul_assoc, mul_comm]
  assumption

open Set

end

@[to_additive]
theorem UniformGroup.toUniformSpace_eq {G : Type*} [u : UniformSpace G] [Group G]
    [UniformGroup G] : TopologicalGroup.toUniformSpace G = u := by
  ext : 1
  rw [uniformity_eq_comap_nhds_one' G, uniformity_eq_comap_nhds_one G]

end TopologicalCommGroup

open Filter Set Function

section

variable {α : Type*} {β : Type*} {hom : Type*}
variable [TopologicalSpace α] [Group α] [TopologicalGroup α]

-- β is a dense subgroup of α, inclusion is denoted by e
variable [TopologicalSpace β] [Group β]
variable [FunLike hom β α] [MonoidHomClass hom β α] {e : hom} (de : DenseInducing e)

@[to_additive]
theorem tendsto_div_comap_self (x₀ : α) :
    Tendsto (fun t : β × β => t.2 / t.1) ((comap fun p : β × β => (e p.1, e p.2)) <| 𝓝 (x₀, x₀))
      (𝓝 1) := by
  have comm : ((fun x : α × α => x.2 / x.1) ∘ fun t : β × β => (e t.1, e t.2)) =
      e ∘ fun t : β × β => t.2 / t.1 := by
    ext t
    change e t.2 / e t.1 = e (t.2 / t.1)
    rw [← map_div e t.2 t.1]
  have lim : Tendsto (fun x : α × α => x.2 / x.1) (𝓝 (x₀, x₀)) (𝓝 (e 1))
  simpa using (continuous_div'.comp (@continuous_swap α α _ _)).tendsto (x₀, x₀)
  simpa using de.tendsto_comap_nhds_nhds lim comm

end

namespace DenseInducing

variable {α : Type*} {β : Type*} {γ : Type*} {δ : Type*}
variable {G : Type*}

-- β is a dense subgroup of α, inclusion is denoted by e
-- δ is a dense subgroup of γ, inclusion is denoted by f
variable [TopologicalSpace α] [AddCommGroup α] [TopologicalAddGroup α]
variable [TopologicalSpace β] [AddCommGroup β] [TopologicalAddGroup β]
variable [TopologicalSpace γ] [AddCommGroup γ] [TopologicalAddGroup γ]
variable [TopologicalSpace δ] [AddCommGroup δ] [TopologicalAddGroup δ]
variable [UniformSpace G] [AddCommGroup G] [UniformAddGroup G] [T0Space G] [CompleteSpace G]
variable {e : β →+ α} (de : DenseInducing e)
variable {f : δ →+ γ} (df : DenseInducing f)
variable {φ : β →+ δ →+ G}
variable (hφ : Continuous (fun p : β × δ => φ p.1 p.2))
variable {W' : Set G} (W'_nhd : W' ∈ 𝓝 (0 : G))

private theorem extend_Z_bilin_aux (x₀ : α) (y₁ : δ) : ∃ U₂ ∈ comap e (𝓝 x₀), ∀ x ∈ U₂, ∀ x' ∈ U₂,
    (fun p : β × δ => φ p.1 p.2) (x' - x, y₁) ∈ W' := by
  let Nx := 𝓝 x₀
  let ee := fun u : β × β => (e u.1, e u.2)
  have lim1 : Tendsto (fun a : β × β => (a.2 - a.1, y₁))
      (comap e Nx ×ˢ comap e Nx) (𝓝 (0, y₁)) := by
    have := Tendsto.prod_mk (tendsto_sub_comap_self de x₀)
      (tendsto_const_nhds : Tendsto (fun _ : β × β => y₁) (comap ee <| 𝓝 (x₀, x₀)) (𝓝 y₁))
    rw [nhds_prod_eq, prod_comap_comap_eq, ← nhds_prod_eq]
    exact (this : _)
  have lim2 : Tendsto (fun p : β × δ => φ p.1 p.2) (𝓝 (0, y₁)) (𝓝 0)
  simpa using hφ.tendsto (0, y₁)
  have lim := lim2.comp lim1
  rw [tendsto_prod_self_iff] at lim
  simp_rw [forall_mem_comm]
  exact lim W' W'_nhd

private theorem extend_Z_bilin_key (x₀ : α) (y₀ : γ) : ∃ U ∈ comap e (𝓝 x₀), ∃ V ∈ comap f (𝓝 y₀),
    ∀ x ∈ U, ∀ x' ∈ U, ∀ (y) (_ : y ∈ V) (y') (_ : y' ∈ V),
    (fun p : β × δ => φ p.1 p.2) (x', y') - (fun p : β × δ => φ p.1 p.2) (x, y) ∈ W' := by
  let ee := fun u : β × β => (e u.1, e u.2)
  let ff := fun u : δ × δ => (f u.1, f u.2)
  have lim_φ : Filter.Tendsto (fun p : β × δ => φ p.1 p.2) (𝓝 (0, 0)) (𝓝 0)
  simpa using hφ.tendsto (0, 0)
  have lim_φ_sub_sub :
    Tendsto (fun p : (β × β) × δ × δ => (fun p : β × δ => φ p.1 p.2) (p.1.2 - p.1.1, p.2.2 - p.2.1))
      ((comap ee <| 𝓝 (x₀, x₀)) ×ˢ (comap ff <| 𝓝 (y₀, y₀))) (𝓝 0) := by
    have lim_sub_sub :
      Tendsto (fun p : (β × β) × δ × δ => (p.1.2 - p.1.1, p.2.2 - p.2.1))
        (comap ee (𝓝 (x₀, x₀)) ×ˢ comap ff (𝓝 (y₀, y₀))) (𝓝 0 ×ˢ 𝓝 0) := by
      have := Filter.prod_mono (tendsto_sub_comap_self de x₀) (tendsto_sub_comap_self df y₀)
      rwa [prod_map_map_eq] at this
    rw [← nhds_prod_eq] at lim_sub_sub
    exact Tendsto.comp lim_φ lim_sub_sub
  rcases exists_nhds_zero_quarter W'_nhd with ⟨W, W_nhd, W4⟩
  have :
    ∃ U₁ ∈ comap e (𝓝 x₀), ∃ V₁ ∈ comap f (𝓝 y₀), ∀ (x) (_ : x ∈ U₁) (x') (_ : x' ∈ U₁),
      ∀ (y) (_ : y ∈ V₁) (y') (_ : y' ∈ V₁), (fun p : β × δ => φ p.1 p.2) (x' - x, y' - y) ∈ W := by
    rcases tendsto_prod_iff.1 lim_φ_sub_sub W W_nhd with ⟨U, U_in, V, V_in, H⟩
    rw [nhds_prod_eq, ← prod_comap_comap_eq, mem_prod_same_iff] at U_in V_in
    rcases U_in with ⟨U₁, U₁_in, HU₁⟩
    rcases V_in with ⟨V₁, V₁_in, HV₁⟩
    exists U₁, U₁_in, V₁, V₁_in
    intro x x_in x' x'_in y y_in y' y'_in
    exact H _ _ (HU₁ (mk_mem_prod x_in x'_in)) (HV₁ (mk_mem_prod y_in y'_in))
  rcases this with ⟨U₁, U₁_nhd, V₁, V₁_nhd, H⟩
  obtain ⟨x₁, x₁_in⟩ : U₁.Nonempty := (de.comap_nhds_neBot _).nonempty_of_mem U₁_nhd
  obtain ⟨y₁, y₁_in⟩ : V₁.Nonempty := (df.comap_nhds_neBot _).nonempty_of_mem V₁_nhd
  have cont_flip : Continuous fun p : δ × β => φ.flip p.1 p.2
  show Continuous ((fun p : β × δ => φ p.1 p.2) ∘ Prod.swap)
  exact hφ.comp continuous_swap
  rcases extend_Z_bilin_aux de hφ W_nhd x₀ y₁ with ⟨U₂, U₂_nhd, HU⟩
  rcases extend_Z_bilin_aux df cont_flip W_nhd y₀ x₁ with ⟨V₂, V₂_nhd, HV⟩
  exists U₁ ∩ U₂, inter_mem U₁_nhd U₂_nhd, V₁ ∩ V₂, inter_mem V₁_nhd V₂_nhd
  rintro x ⟨xU₁, xU₂⟩ x' ⟨x'U₁, x'U₂⟩ y ⟨yV₁, yV₂⟩ y' ⟨y'V₁, y'V₂⟩
  have key_formula : φ x' y' - φ x y
    = φ (x' - x) y₁ + φ (x' - x) (y' - y₁) + φ x₁ (y' - y) + φ (x - x₁) (y' - y) := by simp; abel
  rw [key_formula]
  have h₁ := HU x xU₂ x' x'U₂
  have h₂ := H x xU₁ x' x'U₁ y₁ y₁_in y' y'V₁
  have h₃ := HV y yV₂ y' y'V₂
  have h₄ := H x₁ x₁_in x xU₁ y yV₁ y' y'V₁
  exact W4 h₁ h₂ h₃ h₄

open DenseInducing

/-- Bourbaki GT III.6.5 Theorem I:
ℤ-bilinear continuous maps from dense images into a complete Hausdorff group extend by continuity.
Note: Bourbaki assumes that α and β are also complete Hausdorff, but this is not necessary. -/
theorem extend_Z_bilin : Continuous (extend (de.prod df) (fun p : β × δ => φ p.1 p.2)) := by
  refine continuous_extend_of_cauchy _ ?_
  rintro ⟨x₀, y₀⟩
  constructor
  apply NeBot.map
  apply comap_neBot
  intro U h
  rcases mem_closure_iff_nhds.1 ((de.prod df).dense (x₀, y₀)) U h with ⟨x, x_in, ⟨z, z_x⟩⟩
  exists z
  aesop
  suffices map (fun p : (β × δ) × β × δ => (fun p : β × δ => φ p.1 p.2) p.2 -
    (fun p : β × δ => φ p.1 p.2) p.1)
      (comap (fun p : (β × δ) × β × δ => ((e p.1.1, f p.1.2), (e p.2.1, f p.2.2)))
      (𝓝 (x₀, y₀) ×ˢ 𝓝 (x₀, y₀))) ≤ 𝓝 0 by
    rwa [uniformity_eq_comap_nhds_zero G, prod_map_map_eq, ← map_le_iff_le_comap, Filter.map_map,
      prod_comap_comap_eq]
  intro W' W'_nhd
  have key := extend_Z_bilin_key de df hφ W'_nhd x₀ y₀
  rcases key with ⟨U, U_nhd, V, V_nhd, h⟩
  rw [mem_comap] at U_nhd
  rcases U_nhd with ⟨U', U'_nhd, U'_sub⟩
  rw [mem_comap] at V_nhd
  rcases V_nhd with ⟨V', V'_nhd, V'_sub⟩
  rw [mem_map, mem_comap, nhds_prod_eq]
  exists (U' ×ˢ V') ×ˢ U' ×ˢ V'
  rw [mem_prod_same_iff]
  simp only [exists_prop]
  constructor
  have := prod_mem_prod U'_nhd V'_nhd
  tauto
  intro p h'
  simp only [Set.mem_preimage, Set.prod_mk_mem_set_prod_eq] at h'
  rcases p with ⟨⟨x, y⟩, ⟨x', y'⟩⟩
  apply h <;> tauto

end DenseInducing

section CompleteQuotient

universe u

open TopologicalSpace

open Classical in
/-- The quotient `G ⧸ N` of a complete first countable topological group `G` by a normal subgroup
is itself complete. [N. Bourbaki, *General Topology*, IX.3.1 Proposition 4][bourbaki1966b]

Because a topological group is not equipped with a `UniformSpace` instance by default, we must
explicitly provide it in order to consider completeness. See `QuotientGroup.completeSpace` for a
version in which `G` is already equipped with a uniform structure. -/
@[to_additive "The quotient `G ⧸ N` of a complete first countable topological additive group
`G` by a normal additive subgroup is itself complete. Consequently, quotients of Banach spaces by
subspaces are complete. [N. Bourbaki, *General Topology*, IX.3.1 Proposition 4][bourbaki1966b]

Because an additive topological group is not equipped with a `UniformSpace` instance by default,
we must explicitly provide it in order to consider completeness. See
`QuotientAddGroup.completeSpace` for a version in which `G` is already equipped with a uniform
structure."]
instance QuotientGroup.completeSpace' (G : Type u) [Group G] [TopologicalSpace G]
    [TopologicalGroup G] [FirstCountableTopology G] (N : Subgroup G) [N.Normal]
    [@CompleteSpace G (TopologicalGroup.toUniformSpace G)] :
    @CompleteSpace (G ⧸ N) (TopologicalGroup.toUniformSpace (G ⧸ N)) := by
  /- Since `G ⧸ N` is a topological group it is a uniform space, and since `G` is first countable
    the uniformities of both `G` and `G ⧸ N` are countably generated. Moreover, we may choose a
    sequential antitone neighborhood basis `u` for `𝓝 (1 : G)` so that `(u (n + 1)) ^ 2 ⊆ u n`, and
    this descends to an antitone neighborhood basis `v` for `𝓝 (1 : G ⧸ N)`. Since `𝓤 (G ⧸ N)` is
    countably generated, it suffices to show any Cauchy sequence `x` converges. -/
  letI : UniformSpace (G ⧸ N) := TopologicalGroup.toUniformSpace (G ⧸ N)
  letI : UniformSpace G := TopologicalGroup.toUniformSpace G
  haveI : (𝓤 (G ⧸ N)).IsCountablyGenerated := comap.isCountablyGenerated _ _
  obtain ⟨u, hu, u_mul⟩ := TopologicalGroup.exists_antitone_basis_nhds_one G
  obtain ⟨hv, v_anti⟩ := hu.map ((↑) : G → G ⧸ N)
  rw [← QuotientGroup.nhds_eq N 1, QuotientGroup.mk_one] at hv
  refine UniformSpace.complete_of_cauchySeq_tendsto fun x hx => ?_
  /- Given `n : ℕ`, for sufficiently large `a b : ℕ`, given any lift of `x b`, we can find a lift
    of `x a` such that the quotient of the lifts lies in `u n`. -/
  have key₀ : ∀ i j : ℕ, ∃ M : ℕ, j < M ∧ ∀ a b : ℕ, M ≤ a → M ≤ b →
      ∀ g : G, x b = g → ∃ g' : G, g / g' ∈ u i ∧ x a = g' := by
    have h𝓤GN : (𝓤 (G ⧸ N)).HasBasis (fun _ ↦ True) fun i ↦ { x | x.snd / x.fst ∈ (↑) '' u i } := by
      simpa [uniformity_eq_comap_nhds_one'] using hv.comap _
    rw [h𝓤GN.cauchySeq_iff] at hx
    simp only [mem_setOf_eq, forall_true_left, mem_image] at hx
    intro i j
    rcases hx i with ⟨M, hM⟩
    refine ⟨max j M + 1, (le_max_left _ _).trans_lt (lt_add_one _), fun a b ha hb g hg => ?_⟩
    obtain ⟨y, y_mem, hy⟩ :=
      hM a (((le_max_right j _).trans (lt_add_one _).le).trans ha) b
        (((le_max_right j _).trans (lt_add_one _).le).trans hb)
    refine
      ⟨y⁻¹ * g, by
        simpa only [div_eq_mul_inv, mul_inv_rev, inv_inv, mul_inv_cancel_left] using y_mem, ?_⟩
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, hy, hg, inv_div, div_mul_cancel]
  /- Inductively construct a subsequence `φ : ℕ → ℕ` using `key₀` so that if `a b : ℕ` exceed
    `φ (n + 1)`, then we may find lifts whose quotients lie within `u n`. -/
  set φ : ℕ → ℕ := fun n => Nat.recOn n (choose <| key₀ 0 0) fun k yk => choose <| key₀ (k + 1) yk
  have hφ :
    ∀ n : ℕ,
      φ n < φ (n + 1) ∧
        ∀ a b : ℕ,
          φ (n + 1) ≤ a →
            φ (n + 1) ≤ b → ∀ g : G, x b = g → ∃ g' : G, g / g' ∈ u (n + 1) ∧ x a = g' :=
    fun n => choose_spec (key₀ (n + 1) (φ n))
  /- Inductively construct a sequence `x' n : G` of lifts of `x (φ (n + 1))` such that quotients of
    successive terms lie in `x' n / x' (n + 1) ∈ u (n + 1)`. We actually need the proofs that each
    term is a lift to construct the next term, so we use a Σ-type. -/
  set x' : ∀ n, PSigma fun g : G => x (φ (n + 1)) = g := fun n =>
    Nat.recOn n
      ⟨choose (QuotientGroup.mk_surjective (x (φ 1))),
        (choose_spec (QuotientGroup.mk_surjective (x (φ 1)))).symm⟩
      fun k hk =>
      ⟨choose <| (hφ k).2 _ _ (hφ (k + 1)).1.le le_rfl hk.fst hk.snd,
        (choose_spec <| (hφ k).2 _ _ (hφ (k + 1)).1.le le_rfl hk.fst hk.snd).2⟩
  have hx' : ∀ n : ℕ, (x' n).fst / (x' (n + 1)).fst ∈ u (n + 1) := fun n =>
    (choose_spec <| (hφ n).2 _ _ (hφ (n + 1)).1.le le_rfl (x' n).fst (x' n).snd).1
  /- The sequence `x'` is Cauchy. This is where we exploit the condition on `u`. The key idea
    is to show by decreasing induction that `x' m / x' n ∈ u m` if `m ≤ n`. -/
  have x'_cauchy : CauchySeq fun n => (x' n).fst := by
    have h𝓤G : (𝓤 G).HasBasis (fun _ => True) fun i => { x | x.snd / x.fst ∈ u i } := by
      simpa [uniformity_eq_comap_nhds_one'] using hu.toHasBasis.comap _
    rw [h𝓤G.cauchySeq_iff']
    simp only [mem_setOf_eq, forall_true_left]
    exact fun m =>
      ⟨m, fun n hmn =>
        Nat.decreasingInduction'
          (fun k _ _ hk => u_mul k ⟨_, hx' k, _, hk, div_mul_div_cancel' _ _ _⟩) hmn
          (by simpa only [div_self'] using mem_of_mem_nhds (hu.mem _))⟩
  /- Since `G` is complete, `x'` converges to some `x₀`, and so the image of this sequence under
    the quotient map converges to `↑x₀`. The image of `x'` is a convergent subsequence of `x`, and
    since `x` is Cauchy, this implies it converges. -/
  rcases cauchySeq_tendsto_of_complete x'_cauchy with ⟨x₀, hx₀⟩
  refine
    ⟨↑x₀,
      tendsto_nhds_of_cauchySeq_of_subseq hx
        (strictMono_nat_of_lt_succ fun n => (hφ (n + 1)).1).tendsto_atTop ?_⟩
  convert ((continuous_coinduced_rng : Continuous ((↑) : G → G ⧸ N)).tendsto x₀).comp hx₀
  exact funext fun n => (x' n).snd

/-- The quotient `G ⧸ N` of a complete first countable uniform group `G` by a normal subgroup
is itself complete. In contrast to `QuotientGroup.completeSpace'`, in this version `G` is
already equipped with a uniform structure.
[N. Bourbaki, *General Topology*, IX.3.1 Proposition 4][bourbaki1966b]

Even though `G` is equipped with a uniform structure, the quotient `G ⧸ N` does not inherit a
uniform structure, so it is still provided manually via `TopologicalGroup.toUniformSpace`.
In the most common use cases, this coincides (definitionally) with the uniform structure on the
quotient obtained via other means.  -/
@[to_additive "The quotient `G ⧸ N` of a complete first countable uniform additive group
`G` by a normal additive subgroup is itself complete. Consequently, quotients of Banach spaces by
subspaces are complete. In contrast to `QuotientAddGroup.completeSpace'`, in this version
`G` is already equipped with a uniform structure.
[N. Bourbaki, *General Topology*, IX.3.1 Proposition 4][bourbaki1966b]

Even though `G` is equipped with a uniform structure, the quotient `G ⧸ N` does not inherit a
uniform structure, so it is still provided manually via `TopologicalAddGroup.toUniformSpace`.
In the most common use case ─ quotients of normed additive commutative groups by subgroups ─
significant care was taken so that the uniform structure inherent in that setting coincides
(definitionally) with the uniform structure provided here."]
instance QuotientGroup.completeSpace (G : Type u) [Group G] [us : UniformSpace G] [UniformGroup G]
    [FirstCountableTopology G] (N : Subgroup G) [N.Normal] [hG : CompleteSpace G] :
    @CompleteSpace (G ⧸ N) (TopologicalGroup.toUniformSpace (G ⧸ N)) := by
  rw [← @UniformGroup.toUniformSpace_eq _ us _ _] at hG
  infer_instance

end CompleteQuotient
