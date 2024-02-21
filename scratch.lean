import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.RingTheory.GradedAlgebra.Basic

namespace ExteriorAlgebra

variable (R : Type*) [CommRing R] (n : ℕ) (M : Type*) [AddCommGroup M] [Module R M]

open scoped DirectSum

-- abbrev ExteriorPower := (LinearMap.range (ι R : M →ₗ[R] ExteriorAlgebra R M) ^ n)
/-
[synthInstance] ❌ CommSemiring (ExteriorAlgebra R M) ▼
        [] result <not-available> (cached)
-/
set_option synthInstance.maxHeartbeats 0 in
set_option trace.Meta.synthInstance true in
set_option trace.Meta.isDefEq true in
set_option profiler true in
#synth Zero (⨁ i : ℕ, ↥(ExteriorPower R i M))  -- no
#synth NegZeroClass (⨁ i : ℕ, ↥(ExteriorPower R i M)) -- yes
set_option trace.Meta.synthInstance true in
set_option trace.Meta.isDefEq true in
#synth CommSemiring <| ExteriorAlgebra R M
#synth AddCommGroup (⨁ i : ℕ, ↥(ExteriorPower R i M)) -- yes
#synth NonUnitalNonAssocRing (⨁ i : ℕ, ↥(ExteriorPower R i M)) -- no

attribute [-instance] SetLike.gcommSemiring
attribute [-instance] SetLike.gcommRing

#synth Zero (⨁ i : ℕ, ↥(ExteriorPower R i M)) -- yes
#synth SubtractionCommMonoid (⨁ i : ℕ, ↥(ExteriorPower R i M)) -- yes
#synth AddCommGroup (⨁ i : ℕ, ↥(ExteriorPower R i M)) -- yes
#synth CommSemiring <| ExteriorAlgebra R M
#synth NonUnitalNonAssocRing (⨁ i : ℕ, ↥(ExteriorPower R i M)) -- no

instance why : SetLike.GradedMonoid fun (i : ℕ) ↦ (ExteriorPower R i M) :=
  Submodule.nat_power_gradedMonoid (LinearMap.range (ι R : M →ₗ[R] ExteriorAlgebra R M))

#synth Zero (⨁ i : ℕ, ↥(ExteriorPower R i M)) -- yes
#synth AddCommGroup (⨁ i : ℕ, ↥(ExteriorPower R i M)) -- yes
#synth NonUnitalNonAssocRing (⨁ i : ℕ, ↥(ExteriorPower R i M)) -- yes
#synth CommSemiring <| ExteriorAlgebra R M

attribute [instance] SetLike.gcommSemiring
attribute [instance] SetLike.gcommRing

#synth Zero (⨁ i : ℕ, ↥(ExteriorPower R i M)) -- no
#synth AddCommGroup (⨁ i : ℕ, ↥(ExteriorPower R i M)) -- yes
#synth NonUnitalNonAssocRing (⨁ i : ℕ, ↥(ExteriorPower R i M)) -- yes

