import Mathlib.Tactic.Have
/-
Copyright (c) 2022 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
import Mathlib.Analysis.Normed.Group.Completion
import Mathlib.Analysis.NormedSpace.OperatorNorm.NormedSpace
import Mathlib.Topology.Algebra.UniformRing

/-!
# Normed space structure on the completion of a normed space

If `E` is a normed space over `𝕜`, then so is `UniformSpace.Completion E`. In this file we provide
necessary instances and define `UniformSpace.Completion.toComplₗᵢ` - coercion
`E → UniformSpace.Completion E` as a bundled linear isometry.

We also show that if `A` is a normed algebra over `𝕜`, then so is `UniformSpace.Completion A`.

TODO: Generalise the results here from the concrete `completion` to any `AbstractCompletion`.
-/


noncomputable section

namespace UniformSpace

namespace Completion

variable (𝕜 E : Type*) [NormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

instance (priority := 100) NormedSpace.to_uniformContinuousConstSMul :
    UniformContinuousConstSMul 𝕜 E :=
  ⟨fun c => (lipschitzWith_smul c).uniformContinuous⟩

instance : NormedSpace 𝕜 (Completion E) :=
  { Completion.instModule with
    norm_smul_le := fun c x =>
      induction_on x
        (isClosed_le (continuous_const_smul _).norm (continuous_const.mul continuous_norm)) fun y =>
        by simp only [← coe_smul, norm_coe, norm_smul, le_rfl] }

variable {𝕜 E}

/-- Embedding of a normed space to its completion as a linear isometry. -/
def toComplₗᵢ : E →ₗᵢ[𝕜] Completion E :=
  { toCompl with
    toFun := (↑)
    map_smul' := coe_smul
    norm_map' := norm_coe }

@[simp]
theorem coe_toComplₗᵢ : ⇑(toComplₗᵢ : E →ₗᵢ[𝕜] Completion E) = ((↑) : E → Completion E) :=
  rfl

/-- Embedding of a normed space to its completion as a continuous linear map. -/
def toComplL : E →L[𝕜] Completion E :=
  toComplₗᵢ.toContinuousLinearMap

@[simp]
theorem coe_toComplL : ⇑(toComplL : E →L[𝕜] Completion E) = ((↑) : E → Completion E) :=
  rfl

@[simp]
theorem norm_toComplL {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] [Nontrivial E] : ‖(toComplL : E →L[𝕜] Completion E)‖ = 1 :=
  (toComplₗᵢ : E →ₗᵢ[𝕜] Completion E).norm_toContinuousLinearMap

section Algebra

variable (𝕜) (A : Type*)

instance [SeminormedRing A] : NormedRing (Completion A) :=
  { Completion.ring,
    Completion.instMetricSpace with
    dist_eq := fun x y => by
      refine Completion.induction_on₂ x y ?_ ?_ <;> clear x y
      refine isClosed_eq (Completion.uniformContinuous_extension₂ _).continuous ?_
      exact Continuous.comp Completion.continuous_extension continuous_sub
      intro x y
      rw [← Completion.coe_sub, norm_coe, Completion.dist_eq, dist_eq_norm]
    norm_mul := fun x y => by
      refine Completion.induction_on₂ x y ?_ ?_ <;> clear x y
      exact
        isClosed_le (Continuous.comp continuous_norm continuous_mul)
          (Continuous.comp _root_.continuous_mul
            (Continuous.prod_map continuous_norm continuous_norm))
      intro x y
      simp only [← coe_mul, norm_coe]
      exact norm_mul_le x y }

instance [SeminormedCommRing A] [NormedAlgebra 𝕜 A] [UniformContinuousConstSMul 𝕜 A] :
    NormedAlgebra 𝕜 (Completion A) :=
  { Completion.algebra A 𝕜 with
    norm_smul_le := fun r x => by
      refine Completion.induction_on x ?_ ?_ <;> clear x
      exact
        isClosed_le (Continuous.comp continuous_norm (continuous_const_smul r))
          (Continuous.comp (continuous_mul_left _) continuous_norm)
      intro x
      simp only [← coe_smul, norm_coe]
      exact norm_smul_le r x }

end Algebra

end Completion

end UniformSpace
