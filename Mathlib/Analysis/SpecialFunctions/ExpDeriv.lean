import Mathlib.Tactic.Have
/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne
-/
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Complex and real exponential

In this file we prove that `Complex.exp` and `Real.exp` are infinitely smooth functions.

## Tags

exp, derivative
-/


noncomputable section

open Filter Asymptotics Set Function

open scoped Classical Topology

/-! ## `Complex.exp` -/

namespace Complex

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedAlgebra 𝕜 ℂ]

/-- The complex exponential is everywhere differentiable, with the derivative `exp x`. -/
theorem hasDerivAt_exp (x : ℂ) : HasDerivAt exp (exp x) x := by
  rw [hasDerivAt_iff_isLittleO_nhds_zero]
  have : (1 : ℕ) < 2
  norm_num
  refine (IsBigO.of_bound ‖exp x‖ ?_).trans_isLittleO (isLittleO_pow_id this)
  filter_upwards [Metric.ball_mem_nhds (0 : ℂ) zero_lt_one]
  simp only [Metric.mem_ball, dist_zero_right, norm_pow]
  exact fun z hz => exp_bound_sq x z hz.le

theorem differentiable_exp : Differentiable 𝕜 exp := fun x =>
  (hasDerivAt_exp x).differentiableAt.restrictScalars 𝕜

theorem differentiableAt_exp {x : ℂ} : DifferentiableAt 𝕜 exp x :=
  differentiable_exp x

@[simp]
theorem deriv_exp : deriv exp = exp :=
  funext fun x => (hasDerivAt_exp x).deriv

@[simp]
theorem iter_deriv_exp : ∀ n : ℕ, deriv^[n] exp = exp
  | 0 => rfl
  | n + 1 => by rw [iterate_succ_apply, deriv_exp, iter_deriv_exp n]

theorem contDiff_exp : ∀ {n}, ContDiff 𝕜 n exp := by
  -- Porting note: added `@` due to `∀ {n}` weirdness above
  refine @(contDiff_all_iff_nat.2 fun n => ?_)
  have : ContDiff ℂ (↑n) exp
  induction' n with n ihn
  exact contDiff_zero.2 continuous_exp
  rw [contDiff_succ_iff_deriv]
  use differentiable_exp
  rwa [deriv_exp]
  exact this.restrict_scalars 𝕜

theorem hasStrictDerivAt_exp (x : ℂ) : HasStrictDerivAt exp (exp x) x :=
  contDiff_exp.contDiffAt.hasStrictDerivAt' (hasDerivAt_exp x) le_rfl

theorem hasStrictFDerivAt_exp_real (x : ℂ) : HasStrictFDerivAt exp (exp x • (1 : ℂ →L[ℝ] ℂ)) x :=
  (hasStrictDerivAt_exp x).complexToReal_fderiv

end Complex

section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedAlgebra 𝕜 ℂ] {f : 𝕜 → ℂ} {f' : ℂ} {x : 𝕜}
  {s : Set 𝕜}

theorem HasStrictDerivAt.cexp (hf : HasStrictDerivAt f f' x) :
    HasStrictDerivAt (fun x => Complex.exp (f x)) (Complex.exp (f x) * f') x :=
  (Complex.hasStrictDerivAt_exp (f x)).comp x hf

theorem HasDerivAt.cexp (hf : HasDerivAt f f' x) :
    HasDerivAt (fun x => Complex.exp (f x)) (Complex.exp (f x) * f') x :=
  (Complex.hasDerivAt_exp (f x)).comp x hf

theorem HasDerivWithinAt.cexp (hf : HasDerivWithinAt f f' s x) :
    HasDerivWithinAt (fun x => Complex.exp (f x)) (Complex.exp (f x) * f') s x :=
  (Complex.hasDerivAt_exp (f x)).comp_hasDerivWithinAt x hf

theorem derivWithin_cexp (hf : DifferentiableWithinAt 𝕜 f s x) (hxs : UniqueDiffWithinAt 𝕜 s x) :
    derivWithin (fun x => Complex.exp (f x)) s x = Complex.exp (f x) * derivWithin f s x :=
  hf.hasDerivWithinAt.cexp.derivWithin hxs

@[simp]
theorem deriv_cexp (hc : DifferentiableAt 𝕜 f x) :
    deriv (fun x => Complex.exp (f x)) x = Complex.exp (f x) * deriv f x :=
  hc.hasDerivAt.cexp.deriv

end

section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedAlgebra 𝕜 ℂ] {E : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] {f : E → ℂ} {f' : E →L[𝕜] ℂ} {x : E} {s : Set E}

theorem HasStrictFDerivAt.cexp (hf : HasStrictFDerivAt f f' x) :
    HasStrictFDerivAt (fun x => Complex.exp (f x)) (Complex.exp (f x) • f') x :=
  (Complex.hasStrictDerivAt_exp (f x)).comp_hasStrictFDerivAt x hf

theorem HasFDerivWithinAt.cexp (hf : HasFDerivWithinAt f f' s x) :
    HasFDerivWithinAt (fun x => Complex.exp (f x)) (Complex.exp (f x) • f') s x :=
  (Complex.hasDerivAt_exp (f x)).comp_hasFDerivWithinAt x hf

theorem HasFDerivAt.cexp (hf : HasFDerivAt f f' x) :
    HasFDerivAt (fun x => Complex.exp (f x)) (Complex.exp (f x) • f') x :=
  hasFDerivWithinAt_univ.1 <| hf.hasFDerivWithinAt.cexp

theorem DifferentiableWithinAt.cexp (hf : DifferentiableWithinAt 𝕜 f s x) :
    DifferentiableWithinAt 𝕜 (fun x => Complex.exp (f x)) s x :=
  hf.hasFDerivWithinAt.cexp.differentiableWithinAt

@[simp]
theorem DifferentiableAt.cexp (hc : DifferentiableAt 𝕜 f x) :
    DifferentiableAt 𝕜 (fun x => Complex.exp (f x)) x :=
  hc.hasFDerivAt.cexp.differentiableAt

theorem DifferentiableOn.cexp (hc : DifferentiableOn 𝕜 f s) :
    DifferentiableOn 𝕜 (fun x => Complex.exp (f x)) s := fun x h => (hc x h).cexp

@[simp]
theorem Differentiable.cexp (hc : Differentiable 𝕜 f) :
    Differentiable 𝕜 fun x => Complex.exp (f x) := fun x => (hc x).cexp

theorem ContDiff.cexp {n} (h : ContDiff 𝕜 n f) : ContDiff 𝕜 n fun x => Complex.exp (f x) :=
  Complex.contDiff_exp.comp h

theorem ContDiffAt.cexp {n} (hf : ContDiffAt 𝕜 n f x) :
    ContDiffAt 𝕜 n (fun x => Complex.exp (f x)) x :=
  Complex.contDiff_exp.contDiffAt.comp x hf

theorem ContDiffOn.cexp {n} (hf : ContDiffOn 𝕜 n f s) :
    ContDiffOn 𝕜 n (fun x => Complex.exp (f x)) s :=
  Complex.contDiff_exp.comp_contDiffOn hf

theorem ContDiffWithinAt.cexp {n} (hf : ContDiffWithinAt 𝕜 n f s x) :
    ContDiffWithinAt 𝕜 n (fun x => Complex.exp (f x)) s x :=
  Complex.contDiff_exp.contDiffAt.comp_contDiffWithinAt x hf

end

open Complex in
@[simp]
theorem iteratedDeriv_cexp_const_mul (n : ℕ) (c : ℂ) :
    (iteratedDeriv n fun s : ℂ => exp (c * s)) = fun s => c ^ n * exp (c * s) := by
  rw [iteratedDeriv_const_mul contDiff_exp, iteratedDeriv_eq_iterate, iter_deriv_exp]


/-! ## `Real.exp` -/

namespace Real

variable {x y z : ℝ}

theorem hasStrictDerivAt_exp (x : ℝ) : HasStrictDerivAt exp (exp x) x :=
  (Complex.hasStrictDerivAt_exp x).real_of_complex

theorem hasDerivAt_exp (x : ℝ) : HasDerivAt exp (exp x) x :=
  (Complex.hasDerivAt_exp x).real_of_complex

theorem contDiff_exp {n} : ContDiff ℝ n exp :=
  Complex.contDiff_exp.real_of_complex

theorem differentiable_exp : Differentiable ℝ exp := fun x => (hasDerivAt_exp x).differentiableAt

theorem differentiableAt_exp : DifferentiableAt ℝ exp x :=
  differentiable_exp x

@[simp]
theorem deriv_exp : deriv exp = exp :=
  funext fun x => (hasDerivAt_exp x).deriv

@[simp]
theorem iter_deriv_exp : ∀ n : ℕ, deriv^[n] exp = exp
  | 0 => rfl
  | n + 1 => by rw [iterate_succ_apply, deriv_exp, iter_deriv_exp n]

end Real

section

/-! Register lemmas for the derivatives of the composition of `Real.exp` with a differentiable
function, for standalone use and use with `simp`. -/


variable {f : ℝ → ℝ} {f' x : ℝ} {s : Set ℝ}

theorem HasStrictDerivAt.exp (hf : HasStrictDerivAt f f' x) :
    HasStrictDerivAt (fun x => Real.exp (f x)) (Real.exp (f x) * f') x :=
  (Real.hasStrictDerivAt_exp (f x)).comp x hf

theorem HasDerivAt.exp (hf : HasDerivAt f f' x) :
    HasDerivAt (fun x => Real.exp (f x)) (Real.exp (f x) * f') x :=
  (Real.hasDerivAt_exp (f x)).comp x hf

theorem HasDerivWithinAt.exp (hf : HasDerivWithinAt f f' s x) :
    HasDerivWithinAt (fun x => Real.exp (f x)) (Real.exp (f x) * f') s x :=
  (Real.hasDerivAt_exp (f x)).comp_hasDerivWithinAt x hf

theorem derivWithin_exp (hf : DifferentiableWithinAt ℝ f s x) (hxs : UniqueDiffWithinAt ℝ s x) :
    derivWithin (fun x => Real.exp (f x)) s x = Real.exp (f x) * derivWithin f s x :=
  hf.hasDerivWithinAt.exp.derivWithin hxs

@[simp]
theorem deriv_exp (hc : DifferentiableAt ℝ f x) :
    deriv (fun x => Real.exp (f x)) x = Real.exp (f x) * deriv f x :=
  hc.hasDerivAt.exp.deriv

end

section

/-! Register lemmas for the derivatives of the composition of `Real.exp` with a differentiable
function, for standalone use and use with `simp`. -/


variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → ℝ} {f' : E →L[ℝ] ℝ} {x : E}
  {s : Set E}

theorem ContDiff.exp {n} (hf : ContDiff ℝ n f) : ContDiff ℝ n fun x => Real.exp (f x) :=
  Real.contDiff_exp.comp hf

theorem ContDiffAt.exp {n} (hf : ContDiffAt ℝ n f x) : ContDiffAt ℝ n (fun x => Real.exp (f x)) x :=
  Real.contDiff_exp.contDiffAt.comp x hf

theorem ContDiffOn.exp {n} (hf : ContDiffOn ℝ n f s) : ContDiffOn ℝ n (fun x => Real.exp (f x)) s :=
  Real.contDiff_exp.comp_contDiffOn hf

theorem ContDiffWithinAt.exp {n} (hf : ContDiffWithinAt ℝ n f s x) :
    ContDiffWithinAt ℝ n (fun x => Real.exp (f x)) s x :=
  Real.contDiff_exp.contDiffAt.comp_contDiffWithinAt x hf

theorem HasFDerivWithinAt.exp (hf : HasFDerivWithinAt f f' s x) :
    HasFDerivWithinAt (fun x => Real.exp (f x)) (Real.exp (f x) • f') s x :=
  (Real.hasDerivAt_exp (f x)).comp_hasFDerivWithinAt x hf

theorem HasFDerivAt.exp (hf : HasFDerivAt f f' x) :
    HasFDerivAt (fun x => Real.exp (f x)) (Real.exp (f x) • f') x :=
  (Real.hasDerivAt_exp (f x)).comp_hasFDerivAt x hf

theorem HasStrictFDerivAt.exp (hf : HasStrictFDerivAt f f' x) :
    HasStrictFDerivAt (fun x => Real.exp (f x)) (Real.exp (f x) • f') x :=
  (Real.hasStrictDerivAt_exp (f x)).comp_hasStrictFDerivAt x hf

theorem DifferentiableWithinAt.exp (hf : DifferentiableWithinAt ℝ f s x) :
    DifferentiableWithinAt ℝ (fun x => Real.exp (f x)) s x :=
  hf.hasFDerivWithinAt.exp.differentiableWithinAt

@[simp]
theorem DifferentiableAt.exp (hc : DifferentiableAt ℝ f x) :
    DifferentiableAt ℝ (fun x => Real.exp (f x)) x :=
  hc.hasFDerivAt.exp.differentiableAt

theorem DifferentiableOn.exp (hc : DifferentiableOn ℝ f s) :
    DifferentiableOn ℝ (fun x => Real.exp (f x)) s := fun x h => (hc x h).exp

@[simp]
theorem Differentiable.exp (hc : Differentiable ℝ f) : Differentiable ℝ fun x => Real.exp (f x) :=
  fun x => (hc x).exp

theorem fderivWithin_exp (hf : DifferentiableWithinAt ℝ f s x) (hxs : UniqueDiffWithinAt ℝ s x) :
    fderivWithin ℝ (fun x => Real.exp (f x)) s x = Real.exp (f x) • fderivWithin ℝ f s x :=
  hf.hasFDerivWithinAt.exp.fderivWithin hxs

@[simp]
theorem fderiv_exp (hc : DifferentiableAt ℝ f x) :
    fderiv ℝ (fun x => Real.exp (f x)) x = Real.exp (f x) • fderiv ℝ f x :=
  hc.hasFDerivAt.exp.fderiv

end

open Real in
@[simp]
theorem iteratedDeriv_exp_const_mul (n : ℕ) (c : ℝ) :
    (iteratedDeriv n fun s => exp (c * s)) = fun s => c ^ n * exp (c * s) := by
  rw [iteratedDeriv_const_mul contDiff_exp, iteratedDeriv_eq_iterate, iter_deriv_exp]
