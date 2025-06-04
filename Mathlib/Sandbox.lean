import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.NumberTheory.NumberField.Basic

variable (K : Type*) [Field K] [NumberField K] (E F : IntermediateField ℚ K)

open NumberField nonZeroDivisors

example : 1 = 0 := by
  let D := differentIdeal ℤ (𝓞 K)
  let D₀ := Ideal.map (NumberField.RingOfIntegers.mapRingHom F.val) (differentIdeal ℤ (𝓞 F))
  let D₁ := differentIdeal (𝓞 F) (𝓞 K)
  have : (D : FractionalIdeal (𝓞 K)⁰ K) = D₀ * D₁ := by
    unfold D D₀ D₁
    rw [coeIdeal_differentIdeal ]
    ext x
