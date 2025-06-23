import Mathlib.Tactic.Have
/-
Copyright (c) 2023 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker, Etienne Marion
-/
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.StoneCech

/-!
# A map is proper iff it is continuous and universally closed
-/

open Filter

universe u v

/-- A map `f : X → Y` is proper if and only if it is continuous and the map
`(Prod.map f id : X × Ultrafilter X → Y × Ultrafilter X)` is closed. This is stronger than
`isProperMap_iff_universally_closed` since it shows that there's only one space to check to get
properness, but in most cases it doesn't matter. -/
theorem isProperMap_iff_isClosedMap_ultrafilter {X : Type u} {Y : Type v} [TopologicalSpace X]
    [TopologicalSpace Y] {f : X → Y} :
    IsProperMap f ↔ Continuous f ∧ IsClosedMap
      (Prod.map f id : X × Ultrafilter X → Y × Ultrafilter X) := by
  -- The proof is basically the same as above.
  constructor <;> intro H
  exact ⟨H.continuous, H.universally_closed _⟩
  rw [isProperMap_iff_ultrafilter]
  refine ⟨H.1, fun 𝒰 y hy ↦ ?_⟩
  let F : Set (X × Ultrafilter X) := closure {xℱ | xℱ.2 = pure xℱ.1}
  have := H.2 F isClosed_closure
  have : (y, 𝒰) ∈ Prod.map f id '' F :=
    this.mem_of_tendsto (hy.prod_mk_nhds (Ultrafilter.tendsto_pure_self 𝒰))
      (eventually_of_forall fun x ↦ ⟨⟨x, pure x⟩, subset_closure rfl, rfl⟩)
  rcases this with ⟨⟨x, _⟩, hx, ⟨_, _⟩⟩
  refine ⟨x, rfl, fun U hU ↦ Ultrafilter.compl_not_mem_iff.mp fun hUc ↦ ?_⟩
  rw [mem_closure_iff_nhds] at hx
  rcases hx (U ×ˢ {𝒢 | Uᶜ ∈ 𝒢}) (prod_mem_nhds hU ((ultrafilter_isOpen_basic _).mem_nhds hUc))
    with ⟨⟨y, 𝒢⟩, ⟨⟨hy : y ∈ U, hy' : Uᶜ ∈ 𝒢⟩, rfl : 𝒢 = pure y⟩⟩
  exact hy' hy

/-- A map `f : X → Y` is proper if and only if it is continuous and **universally closed**, in the
sense that for any topological space `Z`, the map `Prod.map f id : X × Z → Y × Z` is closed. Note
that `Z` lives in the same universe as `X` here, but `IsProperMap.universally_closed` does not
have this restriction.

This is taken as the definition of properness in
[N. Bourbaki, *General Topology*][bourbaki1966]. -/
theorem isProperMap_iff_universally_closed {X : Type u} {Y : Type v} [TopologicalSpace X]
    [TopologicalSpace Y] {f : X → Y} :
    IsProperMap f ↔ Continuous f ∧ ∀ (Z : Type u) [TopologicalSpace Z],
      IsClosedMap (Prod.map f id : X × Z → Y × Z) := by
  constructor <;> intro H
  exact ⟨H.continuous, fun Z ↦ H.universally_closed _⟩
  rw [isProperMap_iff_isClosedMap_ultrafilter]
  exact ⟨H.1, H.2 _⟩
