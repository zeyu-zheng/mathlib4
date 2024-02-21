import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.RingTheory.GradedAlgebra.Basic

namespace ExteriorAlgebra

variable (R : Type*) [CommRing R] (n : ℕ) (M : Type*) [AddCommGroup M] [Module R M]

open scoped DirectSum

-- @[default_instance]
-- instance foo : NonUnitalNonAssocSemiring ℕ :=
--   { Nat.semiring with }

-- attribute [default_instance] Nat.commSemiring
-- abbrev ExteriorPower := (LinearMap.range (ι R : M →ₗ[R] ExteriorAlgebra R M) ^ n)
/-
[synthInstance] ❌ CommSemiring (ExteriorAlgebra R M) ▼
        [] result <not-available> (cached)
-/
set_option synthInstance.maxHeartbeats 21000 in
set_option trace.Meta.synthInstance true in
set_option trace.Meta.isDefEq true in
set_option profiler true in
#synth Zero (⨁ i : ℕ, ↥(ExteriorPower R i M))  -- no
#synth NegZeroClass (⨁ i : ℕ, ↥(ExteriorPower R i M)) -- yes
set_option trace.Meta.synthInstance true in
set_option trace.Meta.isDefEq true in
#synth AddCommGroup (⨁ i : ℕ, ↥(ExteriorPower R i M)) -- yes
set_option synthInstance.maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option trace.Meta.isDefEq true in
set_option trace.Meta.synthInstance true in
#synth NonUnitalNonAssocRing (⨁ i : ℕ, ↥(ExteriorPower R i M)) -- no

/-
[] ✅ apply @SetLike.GradedMonoid.toGradedMul to SetLike.GradedMul fun i => (Λ[R]^i) M ▼
    [tryResolve] ✅ SetLike.GradedMul fun i => (Λ[R]^i) M ≟ SetLike.GradedMul fun i => (Λ[R]^i) M ▶
    [] new goal SetLike.GradedMonoid fun i => (Λ[R]^i) M ▼
      [instances] #[@GradedRing.toGradedMonoid]
  [] ✅ apply @GradedRing.toGradedMonoid to SetLike.GradedMonoid fun i => (Λ[R]^i) M ▼
    [tryResolve] ✅ SetLike.GradedMonoid fun i => (Λ[R]^i) M ≟ SetLike.GradedMonoid fun i => (Λ[R]^i) M ▼
      [isDefEq] ✅ SetLike.GradedMonoid fun i => (Λ[R]^i) M =?= SetLike.GradedMonoid ?m.31614 ▶
      [isDefEq] ✅ ?m.28650 =?= GradedRing.toGradedMonoid ▶

-/
#check GradedRing
#check GradedRing.toGradedMonoid
#check CommSemiring.directSumGCommSemiring
#check StrictOrderedCommRing
set_option trace.Meta.synthInstance true in
#synth NonUnitalNonAssocSemiring ℕ

#check DirectSum.nonAssocRing
#synth AddCommMonoid (ExteriorPower R n M)

attribute [-instance] SetLike.gcommSemiring
attribute [-instance] SetLike.gcommRing

#synth Zero (⨁ i : ℕ, ↥(ExteriorPower R i M)) -- yes
#synth SubtractionCommMonoid (⨁ i : ℕ, ↥(ExteriorPower R i M)) -- yes
#synth AddCommGroup (⨁ i : ℕ, ↥(ExteriorPower R i M)) -- yes
#synth NonUnitalNonAssocRing (⨁ i : ℕ, ↥(ExteriorPower R i M)) -- no

instance why : SetLike.GradedMonoid fun (i : ℕ) ↦ (ExteriorPower R i M) :=
  Submodule.nat_power_gradedMonoid (LinearMap.range (ι R : M →ₗ[R] ExteriorAlgebra R M))

#synth Zero (⨁ i : ℕ, ↥(ExteriorPower R i M)) -- yes
#synth AddCommGroup (⨁ i : ℕ, ↥(ExteriorPower R i M)) -- yes
#synth NonUnitalNonAssocRing (⨁ i : ℕ, ↥(ExteriorPower R i M)) -- yes

attribute [instance] SetLike.gcommSemiring
attribute [instance] SetLike.gcommRing

#synth Zero (⨁ i : ℕ, ↥(ExteriorPower R i M)) -- no
#synth AddCommGroup (⨁ i : ℕ, ↥(ExteriorPower R i M)) -- yes
set_option trace.Meta.synthInstance true in
#synth NonUnitalNonAssocRing (⨁ i : ℕ, ↥(ExteriorPower R i M)) -- yes

