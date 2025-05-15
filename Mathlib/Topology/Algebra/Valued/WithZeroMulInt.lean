/-
Copyright (c) 2025 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
import Mathlib.Algebra.Order.GroupWithZero.Int
import Mathlib.Topology.Algebra.Valued.ValuationTopology

/-!
# Topological results for integer-valued rings

This file contains topological results for valuation rings taking values in the
multiplicative integers with zero adjoined. These are useful for cases where there
is a `Valued R ℤₘ₀` instance but no canonical base with which to embed this into
`NNReal`.
-/

open Multiplicative WithZero

open scoped Topology

namespace Valued.WithZeroMulInt

variable {R : Type*} [Ring R] [Valued R ℤₘ₀]

open Set Filter in
/-- In a `ℤₘ₀`-valued ring, powers of `x` tend to zero if `v x ≤ ofAdd (-1 : ℤ)`. -/
theorem tendsto_zero_pow_of_le_neg_one {x : R} (hx : v x ≤ ofAdd (-1 : ℤ)) :
    Tendsto (fun (n : ℕ) => x ^ n) atTop (𝓝 0) := by
  simp only [(hasBasis_nhds_zero _ _).tendsto_right_iff, mem_setOf_eq, map_pow, eventually_atTop]
  intro γ _
  by_cases hγ : γ.val ≤ 1
  · refine ⟨- (unitsMultiplicativeEquiv γ - 1) |>.toNat, fun b hb => ?_⟩
    apply lt_of_le_of_lt (pow_le_pow_of_le_one zero_le' (hx.trans <| le_of_lt ofAdd_neg_one_lt) hb)
    exact lt_of_le_of_lt (pow_le_pow_left₀ zero_le' hx _) <| by rw [ofAdd_neg_one_pow_lt]; omega
  · refine ⟨1, fun b hb => lt_of_le_of_lt
      (pow_le_pow_of_le_one zero_le' (le_trans hx <| le_of_lt ofAdd_neg_one_lt) hb) ?_⟩
    apply pow_one (v x) ▸ lt_trans (lt_of_le_of_lt hx ofAdd_neg_one_lt) (lt_of_not_le hγ)

open Filter in
theorem exists_pow_lt_of_le_neg_one {x : R} (hx : v x ≤ ofAdd (-1 : ℤ)) (γ : ℤₘ₀ˣ) :
    ∃ n, v x ^ n < γ := by
  let ⟨n, hn⟩ := eventually_atTop.1 <|
     (hasBasis_nhds_zero _ _ |>.tendsto_right_iff).1 (tendsto_zero_pow_of_le_neg_one hx) γ trivial
  exact ⟨n, by simpa using hn n le_rfl⟩

end Valued.WithZeroMulInt
