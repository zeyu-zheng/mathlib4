/-
Copyright (c) 2024 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.DedekindDomain.Frobenius

import Mathlib.RingTheory.DedekindDomain.Ideal
import Mathlib.RingTheory.IntegralRestrict
import Mathlib.RingTheory.Ideal.QuotientOperations
import Mathlib.FieldTheory.Cardinality

/-!

# Frobenius elements in number fields

-/

-- let `K ⊆ L` be number fields
variable (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]

-- Let `A ⊆ B` be subrings of `K` and `L`
variable (A B : Type*) [CommRing A] [CommRing B] [Algebra A B] [Algebra A K] [Algebra B L]
  [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]

-- Assume K is the field of fractions of A and L is the field of fractions of B

variable [IsFractionRing A K] [IsFractionRing B L]

-- Assume that `B` is the integral closure of `A` in `L`
variable [IsIntegralClosure B A L]

-- may need these later

--  [IsDomain A] [IsDomain B]
--  [IsIntegralClosure B A L] [FiniteDimensional K L]
--  [IsDedekindDomain A] [IsDedekindDomain B]

#check galRestrict A K L B

-- let P be a maximal ideal of A

variable (P : Ideal A) [P.IsMaximal]

/-

Maths quetion. If K = fof(A) is a number field, if P is a maximal ideal of A
and if P isn't 0 then A/P is finite.

Need: if 0 ≠ r ∈ O_K then r divides some N in ℕ+. So if 0 ≠ k in K then
there's some N ∈ ℕ+ with kN ∈ O_K.

Need O_K ⊗[ℤ] ℚ → K is an iso.

Deduce that P≠0 => P contains r for some nonzero r in 𝓞_K. In fact can we prove
that P contains a finite index subgroup of O_K? I guess we know that A ∩ O_K is
a subring of O_K

 and now if a in A then can
we prove that a+P contains an element of O_K, giving a not at all well-defined
set-theoretic injection A/P → O_K/(r)?


-/
