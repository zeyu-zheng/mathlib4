import Mathlib.Tactic.Have
/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Representation of `FormalMultilinearSeries.radius` as a `liminf`

In this file we prove that the radius of convergence of a `FormalMultilinearSeries` is equal to
$\liminf_{n\to\infty} \frac{1}{\sqrt[n]{‖p n‖}}$. This lemma can't go to `Analysis.Analytic.Basic`
because this would create a circular dependency once we redefine `exp` using
`FormalMultilinearSeries`.
-/


variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

open scoped Topology Classical NNReal ENNReal

open Filter Asymptotics

namespace FormalMultilinearSeries

variable (p : FormalMultilinearSeries 𝕜 E F)

/-- The radius of a formal multilinear series is equal to
$\liminf_{n\to\infty} \frac{1}{\sqrt[n]{‖p n‖}}$. The actual statement uses `ℝ≥0` and some
coercions. -/
theorem radius_eq_liminf :
    p.radius = liminf (fun n => (1 / (‖p n‖₊ ^ (1 / (n : ℝ)) : ℝ≥0) : ℝ≥0∞)) atTop := by
  -- Porting note: added type ascription to make elaborated statement match Lean 3 version
  have :
    ∀ (r : ℝ≥0) {n : ℕ},
      0 < n → ((r : ℝ≥0∞) ≤ 1 / ↑(‖p n‖₊ ^ (1 / (n : ℝ))) ↔ ‖p n‖₊ * r ^ n ≤ 1) := by
    intro r n hn
    have : 0 < (n : ℝ) := Nat.cast_pos.2 hn
    conv_lhs =>
      rw [one_div, ENNReal.le_inv_iff_mul_le, ← ENNReal.coe_mul, ENNReal.coe_le_one_iff, one_div, ←
        NNReal.rpow_one r, ← mul_inv_cancel this.ne', NNReal.rpow_mul, ← NNReal.mul_rpow, ←
        NNReal.one_rpow n⁻¹, NNReal.rpow_le_rpow_iff (inv_pos.2 this), mul_comm,
        NNReal.rpow_natCast]
  apply le_antisymm <;> refine ENNReal.le_of_forall_nnreal_lt fun r hr => ?_
  have := ((TFAE_exists_lt_isLittleO_pow (fun n => ‖p n‖ * r ^ n) 1).out 1 7).1
    (p.isLittleO_of_lt_radius hr)
  obtain ⟨a, ha, H⟩ := this
  apply le_liminf_of_le
  infer_param
  rw [← eventually_map]
  refine
    H.mp ((eventually_gt_atTop 0).mono fun n hn₀ hn => (this _ hn₀).2 (NNReal.coe_le_coe.1 ?_))
  push_cast
  exact (le_abs_self _).trans (hn.trans (pow_le_one _ ha.1.le ha.2.le))
  refine p.le_radius_of_isBigO (IsBigO.of_bound 1 ?_)
  refine (eventually_lt_of_lt_liminf hr).mp ((eventually_gt_atTop 0).mono fun n hn₀ hn => ?_)
  simpa using NNReal.coe_le_coe.2 ((this _ hn₀).1 hn.le)

end FormalMultilinearSeries
