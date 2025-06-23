import Mathlib.Tactic.Have
/-
Copyright (c) 2022 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.RemovableSingularity

/-!
# Schwarz lemma

In this file we prove several versions of the Schwarz lemma.

* `Complex.norm_deriv_le_div_of_mapsTo_ball`, `Complex.abs_deriv_le_div_of_mapsTo_ball`: if
  `f : ℂ → E` sends an open disk with center `c` and a positive radius `R₁` to an open ball with
  center `f c` and radius `R₂`, then the absolute value of the derivative of `f` at `c` is at most
  the ratio `R₂ / R₁`;

* `Complex.dist_le_div_mul_dist_of_mapsTo_ball`: if `f : ℂ → E` sends an open disk with center `c`
  and radius `R₁` to an open disk with center `f c` and radius `R₂`, then for any `z` in the former
  disk we have `dist (f z) (f c) ≤ (R₂ / R₁) * dist z c`;

* `Complex.abs_deriv_le_one_of_mapsTo_ball`: if `f : ℂ → ℂ` sends an open disk of positive radius
  to itself and the center of this disk to itself, then the absolute value of the derivative of `f`
  at the center of this disk is at most `1`;

* `Complex.dist_le_dist_of_mapsTo_ball_self`: if `f : ℂ → ℂ` sends an open disk to itself and the
  center `c` of this disk to itself, then for any point `z` of this disk we have
  `dist (f z) c ≤ dist z c`;

* `Complex.abs_le_abs_of_mapsTo_ball_self`: if `f : ℂ → ℂ` sends an open disk with center `0` to
  itself, then for any point `z` of this disk we have `abs (f z) ≤ abs z`.

## Implementation notes

We prove some versions of the Schwarz lemma for a map `f : ℂ → E` taking values in any normed space
over complex numbers.

## TODO

* Prove that these inequalities are strict unless `f` is an affine map.

* Prove that any diffeomorphism of the unit disk to itself is a Möbius map.

## Tags

Schwarz lemma
-/


open Metric Set Function Filter TopologicalSpace

open scoped Topology

namespace Complex

section Space

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {R R₁ R₂ : ℝ} {f : ℂ → E}
  {c z z₀ : ℂ}

/-- An auxiliary lemma for `Complex.norm_dslope_le_div_of_mapsTo_ball`. -/
theorem schwarz_aux {f : ℂ → ℂ} (hd : DifferentiableOn ℂ f (ball c R₁))
    (h_maps : MapsTo f (ball c R₁) (ball (f c) R₂)) (hz : z ∈ ball c R₁) :
    ‖dslope f c z‖ ≤ R₂ / R₁ := by
  have hR₁ : 0 < R₁ := nonempty_ball.1 ⟨z, hz⟩
  suffices ∀ᶠ r in 𝓝[<] R₁, ‖dslope f c z‖ ≤ R₂ / r by
    refine ge_of_tendsto ?_ this
    exact (tendsto_const_nhds.div tendsto_id hR₁.ne').mono_left nhdsWithin_le_nhds
  rw [mem_ball] at hz
  filter_upwards [Ioo_mem_nhdsWithin_Iio ⟨hz, le_rfl⟩] with r hr
  have hr₀ : 0 < r := dist_nonneg.trans_lt hr.1
  replace hd : DiffContOnCl ℂ (dslope f c) (ball c r) := by
    refine DifferentiableOn.diffContOnCl ?_
    rw [closure_ball c hr₀.ne']
    exact ((differentiableOn_dslope <| ball_mem_nhds _ hR₁).mpr hd).mono
      (closedBall_subset_ball hr.2)
  refine norm_le_of_forall_mem_frontier_norm_le isBounded_ball hd ?_ ?_
  rw [frontier_ball c hr₀.ne']
  intro z hz
  have hz' : z ≠ c := ne_of_mem_sphere hz hr₀.ne'
  rw [dslope_of_ne _ hz', slope_def_module, norm_smul, norm_inv, mem_sphere_iff_norm.1 hz, ←
    div_eq_inv_mul, div_le_div_right hr₀, ← dist_eq_norm]
  exact le_of_lt (h_maps (mem_ball.2 (by rw [mem_sphere.1 hz]; exact hr.2)))
  rw [closure_ball c hr₀.ne', mem_closedBall]
  exact hr.1.le

/-- Two cases of the **Schwarz Lemma** (derivative and distance), merged together. -/
theorem norm_dslope_le_div_of_mapsTo_ball (hd : DifferentiableOn ℂ f (ball c R₁))
    (h_maps : MapsTo f (ball c R₁) (ball (f c) R₂)) (hz : z ∈ ball c R₁) :
    ‖dslope f c z‖ ≤ R₂ / R₁ := by
  have hR₁ : 0 < R₁ := nonempty_ball.1 ⟨z, hz⟩
  have hR₂ : 0 < R₂ := nonempty_ball.1 ⟨f z, h_maps hz⟩
  rcases eq_or_ne (dslope f c z) 0 with hc | hc
  rw [hc, norm_zero]; exact div_nonneg hR₂.le hR₁.le
  rcases exists_dual_vector ℂ _ hc with ⟨g, hg, hgf⟩
  have hg' : ‖g‖₊ = 1 := NNReal.eq hg
  have hg₀ : ‖g‖₊ ≠ 0
  simpa only [hg'] using one_ne_zero
  calc
    ‖dslope f c z‖ = ‖dslope (g ∘ f) c z‖ := by
      rw [g.dslope_comp, hgf, RCLike.norm_ofReal, abs_norm]
      exact fun _ => hd.differentiableAt (ball_mem_nhds _ hR₁)
    _ ≤ R₂ / R₁ := by
      refine schwarz_aux (g.differentiable.comp_differentiableOn hd) (MapsTo.comp ?_ h_maps) hz
      simpa only [hg', NNReal.coe_one, one_mul] using g.lipschitz.mapsTo_ball hg₀ (f c) R₂

/-- Equality case in the **Schwarz Lemma**: in the setup of `norm_dslope_le_div_of_mapsTo_ball`, if
`‖dslope f c z₀‖ = R₂ / R₁` holds at a point in the ball then the map `f` is affine. -/
theorem affine_of_mapsTo_ball_of_exists_norm_dslope_eq_div [CompleteSpace E] [StrictConvexSpace ℝ E]
    (hd : DifferentiableOn ℂ f (ball c R₁)) (h_maps : Set.MapsTo f (ball c R₁) (ball (f c) R₂))
    (h_z₀ : z₀ ∈ ball c R₁) (h_eq : ‖dslope f c z₀‖ = R₂ / R₁) :
    Set.EqOn f (fun z => f c + (z - c) • dslope f c z₀) (ball c R₁) := by
  set g := dslope f c
  rintro z hz
  by_cases h : z = c; · simp [h]
  have h_R₁ : 0 < R₁ := nonempty_ball.mp ⟨_, h_z₀⟩
  have g_le_div : ∀ z ∈ ball c R₁, ‖g z‖ ≤ R₂ / R₁ := fun z hz =>
    norm_dslope_le_div_of_mapsTo_ball hd h_maps hz
  have g_max : IsMaxOn (norm ∘ g) (ball c R₁) z₀ :=
    isMaxOn_iff.mpr fun z hz => by simpa [h_eq] using g_le_div z hz
  have g_diff : DifferentiableOn ℂ g (ball c R₁) :=
    (differentiableOn_dslope (isOpen_ball.mem_nhds (mem_ball_self h_R₁))).mpr hd
  have : g z = g z₀ := eqOn_of_isPreconnected_of_isMaxOn_norm (convex_ball c R₁).isPreconnected
    isOpen_ball g_diff h_z₀ g_max hz
  simp only [g] at this
  simp [g, ← this]

theorem affine_of_mapsTo_ball_of_exists_norm_dslope_eq_div' [CompleteSpace E]
    [StrictConvexSpace ℝ E] (hd : DifferentiableOn ℂ f (ball c R₁))
    (h_maps : Set.MapsTo f (ball c R₁) (ball (f c) R₂))
    (h_z₀ : ∃ z₀ ∈ ball c R₁, ‖dslope f c z₀‖ = R₂ / R₁) :
    ∃ C : E, ‖C‖ = R₂ / R₁ ∧ Set.EqOn f (fun z => f c + (z - c) • C) (ball c R₁) :=
  let ⟨z₀, h_z₀, h_eq⟩ := h_z₀
  ⟨dslope f c z₀, h_eq, affine_of_mapsTo_ball_of_exists_norm_dslope_eq_div hd h_maps h_z₀ h_eq⟩

/-- The **Schwarz Lemma**: if `f : ℂ → E` sends an open disk with center `c` and a positive radius
`R₁` to an open ball with center `f c` and radius `R₂`, then the absolute value of the derivative of
`f` at `c` is at most the ratio `R₂ / R₁`. -/
theorem norm_deriv_le_div_of_mapsTo_ball (hd : DifferentiableOn ℂ f (ball c R₁))
    (h_maps : MapsTo f (ball c R₁) (ball (f c) R₂)) (h₀ : 0 < R₁) : ‖deriv f c‖ ≤ R₂ / R₁ := by
  simpa only [dslope_same] using norm_dslope_le_div_of_mapsTo_ball hd h_maps (mem_ball_self h₀)

/-- The **Schwarz Lemma**: if `f : ℂ → E` sends an open disk with center `c` and radius `R₁` to an
open ball with center `f c` and radius `R₂`, then for any `z` in the former disk we have
`dist (f z) (f c) ≤ (R₂ / R₁) * dist z c`. -/
theorem dist_le_div_mul_dist_of_mapsTo_ball (hd : DifferentiableOn ℂ f (ball c R₁))
    (h_maps : MapsTo f (ball c R₁) (ball (f c) R₂)) (hz : z ∈ ball c R₁) :
    dist (f z) (f c) ≤ R₂ / R₁ * dist z c := by
  rcases eq_or_ne z c with (rfl | hne)
  simp only [dist_self, mul_zero, le_rfl]
  simpa only [dslope_of_ne _ hne, slope_def_module, norm_smul, norm_inv, ← div_eq_inv_mul, ←
    dist_eq_norm, div_le_iff (dist_pos.2 hne)] using norm_dslope_le_div_of_mapsTo_ball hd h_maps hz

end Space

variable {f : ℂ → ℂ} {c z : ℂ} {R R₁ R₂ : ℝ}

/-- The **Schwarz Lemma**: if `f : ℂ → ℂ` sends an open disk with center `c` and a positive radius
`R₁` to an open disk with center `f c` and radius `R₂`, then the absolute value of the derivative of
`f` at `c` is at most the ratio `R₂ / R₁`. -/
theorem abs_deriv_le_div_of_mapsTo_ball (hd : DifferentiableOn ℂ f (ball c R₁))
    (h_maps : MapsTo f (ball c R₁) (ball (f c) R₂)) (h₀ : 0 < R₁) : abs (deriv f c) ≤ R₂ / R₁ :=
  norm_deriv_le_div_of_mapsTo_ball hd h_maps h₀

/-- The **Schwarz Lemma**: if `f : ℂ → ℂ` sends an open disk of positive radius to itself and the
center of this disk to itself, then the absolute value of the derivative of `f` at the center of
this disk is at most `1`. -/
theorem abs_deriv_le_one_of_mapsTo_ball (hd : DifferentiableOn ℂ f (ball c R))
    (h_maps : MapsTo f (ball c R) (ball c R)) (hc : f c = c) (h₀ : 0 < R) : abs (deriv f c) ≤ 1 :=
  (norm_deriv_le_div_of_mapsTo_ball hd (by rwa [hc]) h₀).trans_eq (div_self h₀.ne')

/-- The **Schwarz Lemma**: if `f : ℂ → ℂ` sends an open disk to itself and the center `c` of this
disk to itself, then for any point `z` of this disk we have `dist (f z) c ≤ dist z c`. -/
theorem dist_le_dist_of_mapsTo_ball_self (hd : DifferentiableOn ℂ f (ball c R))
    (h_maps : MapsTo f (ball c R) (ball c R)) (hc : f c = c) (hz : z ∈ ball c R) :
    dist (f z) c ≤ dist z c := by
  -- Porting note: `simp` was failing to use `div_self`
  have := dist_le_div_mul_dist_of_mapsTo_ball hd (by rwa [hc]) hz
  rwa [hc, div_self, one_mul] at this
  exact (nonempty_ball.1 ⟨z, hz⟩).ne'

/-- The **Schwarz Lemma**: if `f : ℂ → ℂ` sends an open disk with center `0` to itself, then for any
point `z` of this disk we have `abs (f z) ≤ abs z`. -/
theorem abs_le_abs_of_mapsTo_ball_self (hd : DifferentiableOn ℂ f (ball 0 R))
    (h_maps : MapsTo f (ball 0 R) (ball 0 R)) (h₀ : f 0 = 0) (hz : abs z < R) :
    abs (f z) ≤ abs z := by
  replace hz : z ∈ ball (0 : ℂ) R := mem_ball_zero_iff.2 hz
  simpa only [dist_zero_right] using dist_le_dist_of_mapsTo_ball_self hd h_maps h₀ hz

end Complex
