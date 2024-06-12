/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Johannes Hölzl
-/
import Mathlib.Algebra.Algebra.NonUnitalSubalgebra
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Group.Lemmas

#align_import analysis.normed.field.basic from "leanprover-community/mathlib"@"f06058e64b7e8397234455038f3f8aec83aaba5a"

/-!
# Normed fields

In this file we define (semi)normed rings and fields. We also prove some theorems about these
definitions.
-/

variable {α : Type*} {β : Type*} {γ : Type*} {ι : Type*}

open Filter Metric Bornology
open scoped Topology NNReal ENNReal uniformity Pointwise

instance PUnit.normedCommRing : NormedCommRing PUnit :=
  { PUnit.normedAddCommGroup, PUnit.commRing with
    norm_mul := fun _ _ => by simp }

section NonUnitalSeminormedRing

variable [NonUnitalSeminormedRing α]

theorem Filter.Tendsto.zero_mul_isBoundedUnder_le {f g : ι → α} {l : Filter ι}
    (hf : Tendsto f l (𝓝 0)) (hg : IsBoundedUnder (· ≤ ·) l ((‖·‖) ∘ g)) :
    Tendsto (fun x => f x * g x) l (𝓝 0) :=
  hf.op_zero_isBoundedUnder_le hg (· * ·) norm_mul_le
#align filter.tendsto.zero_mul_is_bounded_under_le Filter.Tendsto.zero_mul_isBoundedUnder_le

theorem Filter.isBoundedUnder_le_mul_tendsto_zero {f g : ι → α} {l : Filter ι}
    (hf : IsBoundedUnder (· ≤ ·) l (norm ∘ f)) (hg : Tendsto g l (𝓝 0)) :
    Tendsto (fun x => f x * g x) l (𝓝 0) :=
  hg.op_zero_isBoundedUnder_le hf (flip (· * ·)) fun x y =>
    (norm_mul_le y x).trans_eq (mul_comm _ _)
#align filter.is_bounded_under_le.mul_tendsto_zero Filter.isBoundedUnder_le_mul_tendsto_zero


/-- A non-unital subalgebra of a non-unital seminormed ring is also a non-unital seminormed ring,
with the restriction of the norm.  -/
instance NonUnitalSubalgebra.nonUnitalSeminormedRing {𝕜 : Type*} [CommRing 𝕜] {E : Type*}
    [NonUnitalSeminormedRing E] [Module 𝕜 E] (s : NonUnitalSubalgebra 𝕜 E) :
    NonUnitalSeminormedRing s :=
  { s.toSubmodule.seminormedAddCommGroup, s.toNonUnitalRing with
    norm_mul := fun a b => norm_mul_le a.1 b.1 }

/-- A non-unital subalgebra of a non-unital normed ring is also a non-unital normed ring, with the
restriction of the norm.  -/
instance NonUnitalSubalgebra.nonUnitalNormedRing {𝕜 : Type*} [CommRing 𝕜] {E : Type*}
    [NonUnitalNormedRing E] [Module 𝕜 E] (s : NonUnitalSubalgebra 𝕜 E) : NonUnitalNormedRing s :=
  { s.nonUnitalSeminormedRing with
    eq_of_dist_eq_zero := eq_of_dist_eq_zero }

instance ULift.nonUnitalSeminormedRing : NonUnitalSeminormedRing (ULift α) :=
  { ULift.seminormedAddCommGroup, ULift.nonUnitalRing with
    norm_mul := fun x y => (norm_mul_le x.down y.down : _) }

end NonUnitalSeminormedRing

section SeminormedRing

variable [SeminormedRing α]

/-- A subalgebra of a seminormed ring is also a seminormed ring, with the restriction of the
norm. -/
instance Subalgebra.seminormedRing {𝕜 : Type*} [CommRing 𝕜] {E : Type*} [SeminormedRing E]
    [Algebra 𝕜 E] (s : Subalgebra 𝕜 E) : SeminormedRing s :=
  { s.toSubmodule.seminormedAddCommGroup, s.toRing with
    norm_mul := fun a b => norm_mul_le a.1 b.1 }
#align subalgebra.semi_normed_ring Subalgebra.seminormedRing

/-- A subalgebra of a normed ring is also a normed ring, with the restriction of the norm. -/
instance Subalgebra.normedRing {𝕜 : Type*} [CommRing 𝕜] {E : Type*} [NormedRing E]
    [Algebra 𝕜 E] (s : Subalgebra 𝕜 E) : NormedRing s :=
  { s.seminormedRing with
    eq_of_dist_eq_zero := eq_of_dist_eq_zero }
#align subalgebra.normed_ring Subalgebra.normedRing

instance ULift.seminormedRing : SeminormedRing (ULift α) :=
  { ULift.nonUnitalSeminormedRing, ULift.ring with }

end SeminormedRing

section NonUnitalNormedRing

variable [NonUnitalNormedRing α]

instance ULift.nonUnitalNormedRing : NonUnitalNormedRing (ULift α) :=
  { ULift.nonUnitalSeminormedRing, ULift.normedAddCommGroup with }

end NonUnitalNormedRing

section NormedRing

variable [NormedRing α]

instance ULift.normedRing : NormedRing (ULift α) :=
  { ULift.seminormedRing, ULift.normedAddCommGroup with }

end NormedRing

section NonUnitalSeminormedCommRing

variable [NonUnitalSeminormedCommRing α]

instance ULift.nonUnitalSeminormedCommRing : NonUnitalSeminormedCommRing (ULift α) :=
  { ULift.nonUnitalSeminormedRing, ULift.nonUnitalCommRing with }

end NonUnitalSeminormedCommRing

section NonUnitalNormedCommRing

variable [NonUnitalNormedCommRing α]

/-- A non-unital subalgebra of a non-unital seminormed commutative ring is also a non-unital
seminormed commutative ring, with the restriction of the norm.  -/
instance NonUnitalSubalgebra.nonUnitalSeminormedCommRing {𝕜 : Type*} [CommRing 𝕜] {E : Type*}
    [NonUnitalSeminormedCommRing E] [Module 𝕜 E] (s : NonUnitalSubalgebra 𝕜 E) :
    NonUnitalSeminormedCommRing s :=
  { s.nonUnitalSeminormedRing, s.toNonUnitalCommRing with }

/-- A non-unital subalgebra of a non-unital normed commutative ring is also a non-unital normed
commutative ring, with the restriction of the norm.  -/
instance NonUnitalSubalgebra.nonUnitalNormedCommRing {𝕜 : Type*} [CommRing 𝕜] {E : Type*}
    [NonUnitalNormedCommRing E] [Module 𝕜 E] (s : NonUnitalSubalgebra 𝕜 E) :
    NonUnitalNormedCommRing s :=
  { s.nonUnitalSeminormedCommRing, s.nonUnitalNormedRing with }

instance ULift.nonUnitalNormedCommRing : NonUnitalNormedCommRing (ULift α) :=
  { ULift.nonUnitalSeminormedCommRing, ULift.normedAddCommGroup with }

end NonUnitalNormedCommRing

section SeminormedCommRing

variable [SeminormedCommRing α]

instance ULift.seminormedCommRing : SeminormedCommRing (ULift α) :=
  { ULift.nonUnitalSeminormedRing, ULift.commRing with }

end SeminormedCommRing

section NormedCommRing

/-- A subalgebra of a seminormed commutative ring is also a seminormed commutative ring, with the
restriction of the norm.  -/
instance Subalgebra.seminormedCommRing {𝕜 : Type*} [CommRing 𝕜] {E : Type*} [SeminormedCommRing E]
    [Algebra 𝕜 E] (s : Subalgebra 𝕜 E) : SeminormedCommRing s :=
  { s.seminormedRing, s.toCommRing with }

/-- A subalgebra of a normed commutative ring is also a normed commutative ring, with the
restriction of the norm.  -/
instance Subalgebra.normedCommRing {𝕜 : Type*} [CommRing 𝕜] {E : Type*} [NormedCommRing E]
    [Algebra 𝕜 E] (s : Subalgebra 𝕜 E) : NormedCommRing s :=
  { s.seminormedCommRing, s.normedRing with }

variable [NormedCommRing α]

instance ULift.normedCommRing : NormedCommRing (ULift α) :=
  { ULift.normedRing (α := α), ULift.seminormedCommRing with }

end NormedCommRing

-- see Note [lower instance priority]
instance (priority := 100) semi_normed_ring_top_monoid [NonUnitalSeminormedRing α] :
    ContinuousMul α :=
  ⟨continuous_iff_continuousAt.2 fun x =>
      tendsto_iff_norm_sub_tendsto_zero.2 <| by
        have : ∀ e : α × α,
            ‖e.1 * e.2 - x.1 * x.2‖ ≤ ‖e.1‖ * ‖e.2 - x.2‖ + ‖e.1 - x.1‖ * ‖x.2‖ := by
          intro e
          calc
            ‖e.1 * e.2 - x.1 * x.2‖ ≤ ‖e.1 * (e.2 - x.2) + (e.1 - x.1) * x.2‖ := by
              rw [_root_.mul_sub, _root_.sub_mul, sub_add_sub_cancel]
            -- Porting note: `ENNReal.{mul_sub, sub_mul}` should be protected
            _ ≤ ‖e.1‖ * ‖e.2 - x.2‖ + ‖e.1 - x.1‖ * ‖x.2‖ :=
              norm_add_le_of_le (norm_mul_le _ _) (norm_mul_le _ _)
        refine squeeze_zero (fun e => norm_nonneg _) this ?_
        convert
          ((continuous_fst.tendsto x).norm.mul
                ((continuous_snd.tendsto x).sub tendsto_const_nhds).norm).add
            (((continuous_fst.tendsto x).sub tendsto_const_nhds).norm.mul _)
        -- Porting note: `show` used to select a goal to work on
        rotate_right
        · show Tendsto _ _ _
          exact tendsto_const_nhds
        · simp⟩
#align semi_normed_ring_top_monoid semi_normed_ring_top_monoid

-- see Note [lower instance priority]
/-- A seminormed ring is a topological ring. -/
instance (priority := 100) semi_normed_top_ring [NonUnitalSeminormedRing α] :
    TopologicalRing α where
#align semi_normed_top_ring semi_normed_top_ring

section NormedDivisionRing

variable [NormedDivisionRing α] {a : α}

-- see Note [lower instance priority]
instance (priority := 100) NormedDivisionRing.to_hasContinuousInv₀ : HasContinuousInv₀ α := by
  refine ⟨fun r r0 => tendsto_iff_norm_sub_tendsto_zero.2 ?_⟩
  have r0' : 0 < ‖r‖ := norm_pos_iff.2 r0
  rcases exists_between r0' with ⟨ε, ε0, εr⟩
  have : ∀ᶠ e in 𝓝 r, ‖e⁻¹ - r⁻¹‖ ≤ ‖r - e‖ / ‖r‖ / ε := by
    filter_upwards [(isOpen_lt continuous_const continuous_norm).eventually_mem εr] with e he
    have e0 : e ≠ 0 := norm_pos_iff.1 (ε0.trans he)
    calc
      ‖e⁻¹ - r⁻¹‖ = ‖r‖⁻¹ * ‖r - e‖ * ‖e‖⁻¹ := by
        rw [← norm_inv, ← norm_inv, ← norm_mul, ← norm_mul, _root_.mul_sub, _root_.sub_mul,
          mul_assoc _ e, inv_mul_cancel r0, mul_inv_cancel e0, one_mul, mul_one]
      -- Porting note: `ENNReal.{mul_sub, sub_mul}` should be `protected`
      _ = ‖r - e‖ / ‖r‖ / ‖e‖ := by field_simp [mul_comm]
      _ ≤ ‖r - e‖ / ‖r‖ / ε := by gcongr
  refine squeeze_zero' (eventually_of_forall fun _ => norm_nonneg _) this ?_
  refine (((continuous_const.sub continuous_id).norm.div_const _).div_const _).tendsto' _ _ ?_
  simp
#align normed_division_ring.to_has_continuous_inv₀ NormedDivisionRing.to_hasContinuousInv₀

-- see Note [lower instance priority]
/-- A normed division ring is a topological division ring. -/
instance (priority := 100) NormedDivisionRing.to_topologicalDivisionRing :
    TopologicalDivisionRing α where
#align normed_division_ring.to_topological_division_ring NormedDivisionRing.to_topologicalDivisionRing


end NormedDivisionRing

namespace NNReal

open NNReal

lemma lipschitzWith_sub : LipschitzWith 2 (fun (p : ℝ≥0 × ℝ≥0) ↦ p.1 - p.2) := by
  rw [← isometry_subtype_coe.lipschitzWith_iff]
  have : Isometry (Prod.map ((↑) : ℝ≥0 → ℝ) ((↑) : ℝ≥0 → ℝ)) :=
    isometry_subtype_coe.prod_map isometry_subtype_coe
  convert (((LipschitzWith.prod_fst.comp this.lipschitz).sub
    (LipschitzWith.prod_snd.comp this.lipschitz)).max_const 0)
  norm_num

end NNReal

instance Int.instNormedCommRing : NormedCommRing ℤ where
  __ := instCommRing
  __ := instNormedAddCommGroup
  norm_mul m n := by simp only [norm, Int.cast_mul, abs_mul, le_rfl]

instance Int.instNormOneClass : NormOneClass ℤ :=
  ⟨by simp [← Int.norm_cast_real]⟩

instance Rat.instNormedField : NormedField ℚ where
  __ := instField
  __ := instNormedAddCommGroup
  norm_mul' a b := by simp only [norm, Rat.cast_mul, abs_mul]

instance Rat.instDenselyNormedField : DenselyNormedField ℚ where
  lt_norm_lt r₁ r₂ h₀ hr :=
    let ⟨q, h⟩ := exists_rat_btwn hr
    ⟨q, by rwa [← Rat.norm_cast_real, Real.norm_eq_abs, abs_of_pos (h₀.trans_lt h.1)]⟩


-- Guard against import creep.
assert_not_exists RestrictScalars
