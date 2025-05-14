/-
Copyright (c) 2025 Yaël Dillies, Patrick Luo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Patrick Luo
-/
import Mathlib.Algebra.AffineMonoid.Embedding
import Mathlib.Algebra.FreeAbelianGroup.UniqueSums
import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors

/-!
# Affine monoid algebras are domains

This file proves that the monoid algebra of a finitely generated cancellative torsion-free
commutative monoid over a domain is a domain.
-/

open AffineAddMonoid

variable {R M : Type*} [CommRing R]

namespace AddMonoidAlgebra
variable [AddCancelCommMonoid M] [AddMonoid.FG M] [IsAddTorsionFree M]

instance instNoZeroDivisorsOfFG [NoZeroDivisors R] : NoZeroDivisors R[M] :=
  (mapDomain_injective embedding_injective).noZeroDivisors (mapDomainRingHom R <| embedding M)
    (map_zero _) (map_mul _)

instance instIsDomainOfFG [IsDomain R] : IsDomain R[M] :=
  (mapDomain_injective embedding_injective).isDomain <| mapDomainRingHom R <| embedding M

end AddMonoidAlgebra

namespace MonoidAlgebra
variable [CancelCommMonoid M] [Monoid.FG M] [IsMulTorsionFree M]

instance instNoZeroDivisorsOfFG [NoZeroDivisors R] : NoZeroDivisors (MonoidAlgebra R M) :=
  AddMonoidAlgebra.instNoZeroDivisorsOfFG (R := R) (M := Additive M)

instance instIsDomainOfFG [IsDomain R] : IsDomain (MonoidAlgebra R M) :=
  AddMonoidAlgebra.instIsDomainOfFG (R := R) (M := Additive M)

end MonoidAlgebra
