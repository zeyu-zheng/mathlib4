import Mathlib.LinearAlgebra.LinearPMap
import Mathlib.Topology.Algebra.Module.LinearMap

structure ContinuousLinearPMap (R E F : Type*) [Ring R] [AddCommGroup E] [Module R E]
    [TopologicalSpace E] [AddCommGroup F] [Module R F] [TopologicalSpace F]
    extends E →ₗ.[R] F where
  cont : Continuous toFun

@[inherit_doc] notation:25 E " →L.[" R:25 "] " F:0 => ContinuousLinearPMap R E F

class ContinuousSemilinearPMapClass (F : Type*) {R S : outParam Type*} [Semiring R]
    [Semiring S] (σ : outParam (R →+* S)) (M γ N : outParam Type*) [SetLike γ M]
    [AddCommMonoid M] [TopologicalSpace M] [AddCommMonoid N] [TopologicalSpace N] [Module R M]
    [Module S N] [PFunLike F M γ N] [AddMemClass γ M] [SMulMemClass γ R M]
    extends SemilinearPMapClass F σ M γ N where
  cont : ∀ (f : F), Continuous f

abbrev ContinuousLinearPMapClass (F : Type*) (R : outParam Type*) [Semiring R]
    (M γ N : outParam Type*) [SetLike γ M] [AddCommMonoid M] [TopologicalSpace M] [AddCommMonoid N]
    [TopologicalSpace N] [Module R M] [Module R N] [PFunLike F M γ N] [AddMemClass γ M]
    [SMulMemClass γ R M] := ContinuousSemilinearPMapClass F (RingHom.id R) M γ N

namespace ContinuousLinearPMap

variable {R E F : Type*} [Ring R] [AddCommGroup E] [Module R E] [TopologicalSpace E]
  [AddCommGroup F] [Module R F] [TopologicalSpace F]

instance PFunLike : PFunLike (E →L.[R] F) E (Submodule R E) F where
  domain f := f.domain
  coe f := f.toFun
  coe_injective := by
    rintro ⟨f, _⟩ ⟨g, _⟩ hd h
    rw [mk.injEq]
    exact LinearPMap.ext hd h

instance ContinuousLinearPMapClass :
    ContinuousLinearPMapClass (E →L.[R] F) R E (Submodule R E) F where
  pmap_add f := f.toFun.map_add
  pmap_smulₛₗ f := f.toFun.map_smul
  cont f := f.cont



end ContinuousLinearPMap
