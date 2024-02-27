/-
Copyright (c) 2023 Ali Ramsey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ali Ramsey, Eric Wieser
-/
import Mathlib.LinearAlgebra.Finsupp
import Mathlib.LinearAlgebra.Prod
import Mathlib.LinearAlgebra.TensorProduct

/-!
# Coalgebras

In this file we define `Coalgebra`, and provide instances for:

* Commutative semirings: `CommSemiring.toCoalgebra`
* Binary products: `Prod.instCoalgebra`
* Finitely supported functions: `Finsupp.instCoalgebra`

## References

* <https://en.wikipedia.org/wiki/Coalgebra>
-/

suppress_compilation

universe u v w

open scoped TensorProduct

/-- Data fields for `Coalgebra`, to allow API to be constructed before proving `Coalgebra.coassoc`.

See `Coalgebra` for documentation. -/
class CoalgebraStruct (R : Type u) (A : Type v)
    [CommSemiring R] [AddCommMonoid A] [Module R A] where
  /-- The comultiplication of the coalgebra. Use `comul` instead. -/
  comul' : A →ₗ[R] A ⊗[R] A
  /-- The counit of the coalgebra. Use `counit` instead. -/
  counit' : A →ₗ[R] R

namespace CoalgebraStruct

variable (R : Type u) (A : Type v)
variable [CommSemiring R] [AddCommMonoid A] [Module R A] [CoalgebraStruct R A]

/-- The comultiplication of the coalgebra -/
def comul : A →ₗ[R] A ⊗[R] A := comul'

/-- The counit of the coalgebra. -/
def counit : A →ₗ[R] R := counit'

end CoalgebraStruct

namespace Coalgebra

variable (R : Type u) (A : Type v)
variable [CommSemiring R] [AddCommMonoid A] [Module R A] [CoalgebraStruct R A]

export CoalgebraStruct (comul' counit' comul counit)

@[simp] lemma comul'_def : comul' = comul R A := rfl

@[simp] lemma counit'_def : counit' = counit R A := rfl

end Coalgebra

/-- A coalgebra over a commutative (semi)ring `R` is an `R`-module equipped with a coassociative
comultiplication `Δ` and a counit `ε` obeying the left and right counitality laws. -/
class Coalgebra (R : Type u) (A : Type v)
    [CommSemiring R] [AddCommMonoid A] [Module R A] extends CoalgebraStruct R A where
  /-- The comultiplication is coassociative. -/
  coassoc : TensorProduct.assoc R A A A ∘ₗ (Coalgebra.comul R A).rTensor A ∘ₗ Coalgebra.comul R A =
    (Coalgebra.comul R A).lTensor A ∘ₗ Coalgebra.comul R A
  /-- The counit satisfies the left counitality law. -/
  rTensor_counit_comp_comul : (Coalgebra.counit R A).rTensor A ∘ₗ Coalgebra.comul R A =
    TensorProduct.mk R _ _ 1
  /-- The counit satisfies the right counitality law. -/
  lTensor_counit_comp_comul : (Coalgebra.counit R A).lTensor A ∘ₗ Coalgebra.comul R A =
    (TensorProduct.mk R _ _).flip 1

namespace Coalgebra
variable {R : Type u} {A : Type v}
variable [CommSemiring R] [AddCommMonoid A] [Module R A] [Coalgebra R A]

@[simp]
theorem coassoc_apply (a : A) :
    TensorProduct.assoc R A A A ((comul R A).rTensor A (comul R A a)) =
    (comul R A).lTensor A (comul R A a) :=

  LinearMap.congr_fun coassoc a

@[simp]
theorem coassoc_symm_apply (a : A) :
    (TensorProduct.assoc R A A A).symm ((comul R A).lTensor A (comul R A a)) =
    (comul R A).rTensor A (comul R A a) := by
  rw [(TensorProduct.assoc R A A A).symm_apply_eq, coassoc_apply a]

@[simp]
theorem coassoc_symm :
    (TensorProduct.assoc R A A A).symm ∘ₗ (comul R A).lTensor A ∘ₗ comul R A =
    (comul R A).rTensor A ∘ₗ (comul R A) :=
  LinearMap.ext coassoc_symm_apply

@[simp]
theorem rTensor_counit_comul (a : A) : (counit R A).rTensor A (comul R A a) = 1 ⊗ₜ[R] a :=
  LinearMap.congr_fun rTensor_counit_comp_comul a

@[simp]
theorem lTensor_counit_comul (a : A) : (counit R A).lTensor A (comul R A a) = a ⊗ₜ[R] 1 :=
  LinearMap.congr_fun lTensor_counit_comp_comul a

end Coalgebra
section CommSemiring

open Coalgebra

namespace CommSemiring
variable (R : Type u) [CommSemiring R]

/-- Every commutative (semi)ring is a coalgebra over itself, with `Δ r = 1 ⊗ₜ r`. -/
instance toCoalgebra : Coalgebra R R where
  comul' := (TensorProduct.mk R R R) 1
  counit' := .id
  coassoc := rfl
  rTensor_counit_comp_comul := by ext; rfl
  lTensor_counit_comp_comul := by ext; rfl

@[simp]
theorem comul_apply (r : R) : comul R R r = 1 ⊗ₜ[R] r := rfl

@[simp]
theorem counit_apply (r : R) : counit R R r = r := rfl

end CommSemiring

namespace Prod
variable (R : Type u) (A : Type v) (B : Type w)
variable [CommSemiring R] [AddCommMonoid A] [AddCommMonoid B] [Module R A] [Module R B]
variable [Coalgebra R A] [Coalgebra R B]

open LinearMap

instance instCoalgebraStruct : CoalgebraStruct R (A × B) where
  comul' := .coprod
    (TensorProduct.map (.inl R A B) (.inl R A B) ∘ₗ comul R _)
    (TensorProduct.map (.inr R A B) (.inr R A B) ∘ₗ comul R _)
  counit' := .coprod (counit R _) (counit R _)

@[simp]
theorem comul_apply (r : A × B) : comul R _ r =
    TensorProduct.map (.inl R A B) (.inl R A B) (comul R _ r.1) +
    TensorProduct.map (.inr R A B) (.inr R A B) (comul R _ r.2) := rfl

@[simp]
theorem counit_apply (r : A × B) : counit R _ r = counit R _ r.1 + counit R _ r.2 := rfl

theorem comul_comp_inl :
    comul R _ ∘ₗ inl R A B = TensorProduct.map (.inl R A B) (.inl R A B) ∘ₗ comul R _ := by
  ext; simp

theorem comul_comp_inr :
    comul R _ ∘ₗ inr R A B = TensorProduct.map (.inr R A B) (.inr R A B) ∘ₗ comul R _ := by
  ext; simp

theorem comul_comp_fst :
    comul R _ ∘ₗ .fst R A B = TensorProduct.map (.fst R A B) (.fst R A B) ∘ₗ comul R _ := by
  ext : 1
  · rw [comp_assoc, fst_comp_inl, comp_id, comp_assoc, comul_comp_inl, ← comp_assoc,
      ← TensorProduct.map_comp, fst_comp_inl, TensorProduct.map_id, id_comp]
  · rw [comp_assoc, fst_comp_inr, comp_zero, comp_assoc, comul_comp_inr, ← comp_assoc,
      ← TensorProduct.map_comp, fst_comp_inr, TensorProduct.map_zero_left, zero_comp]

theorem comul_comp_snd :
    comul R _ ∘ₗ .snd R A B = TensorProduct.map (.snd R A B) (.snd R A B) ∘ₗ comul R _ := by
  ext : 1
  · rw [comp_assoc, snd_comp_inl, comp_zero, comp_assoc, comul_comp_inl, ← comp_assoc,
      ← TensorProduct.map_comp, snd_comp_inl, TensorProduct.map_zero_left, zero_comp]
  · rw [comp_assoc, snd_comp_inr, comp_id, comp_assoc, comul_comp_inr, ← comp_assoc,
      ← TensorProduct.map_comp, snd_comp_inr, TensorProduct.map_id, id_comp]

@[simp] theorem counit_comp_inr : counit R _ ∘ₗ inr R A B = counit R _ := by ext; simp

@[simp] theorem counit_comp_inl : counit R _ ∘ₗ inl R A B = counit R _ := by ext; simp

instance instCoalgebra : Coalgebra R (A × B) where
  rTensor_counit_comp_comul := by
    ext : 1
    · rw [comp_assoc, comul_comp_inl, ← comp_assoc, rTensor_comp_map, counit_comp_inl,
        ← lTensor_comp_rTensor, comp_assoc, rTensor_counit_comp_comul, lTensor_comp_mk]
    · rw [comp_assoc, comul_comp_inr, ← comp_assoc, rTensor_comp_map, counit_comp_inr,
        ← lTensor_comp_rTensor, comp_assoc, rTensor_counit_comp_comul, lTensor_comp_mk]
  lTensor_counit_comp_comul := by
    ext : 1
    · rw [comp_assoc, comul_comp_inl, ← comp_assoc, lTensor_comp_map, counit_comp_inl,
        ← rTensor_comp_lTensor, comp_assoc, lTensor_counit_comp_comul, rTensor_comp_flip_mk]
    · rw [comp_assoc, comul_comp_inr, ← comp_assoc, lTensor_comp_map, counit_comp_inr,
        ← rTensor_comp_lTensor, comp_assoc, lTensor_counit_comp_comul, rTensor_comp_flip_mk]
  coassoc := by
    dsimp only [instCoalgebraStruct, ←comul'_def R (A × B), ← counit'_def]
    ext x : 2 <;> dsimp only [comp_apply, LinearEquiv.coe_coe, coe_inl, coe_inr, coprod_apply]
    · simp only [map_zero, add_zero]
      simp_rw [← comp_apply, ← comp_assoc, rTensor_comp_map, lTensor_comp_map, coprod_inl,
        ← map_comp_rTensor, ← map_comp_lTensor, comp_assoc, ← coassoc, ← comp_assoc,
        TensorProduct.map_map_comp_assoc_eq, comp_apply, LinearEquiv.coe_coe]
    · simp only [map_zero, zero_add]
      simp_rw [← comp_apply, ← comp_assoc, rTensor_comp_map, lTensor_comp_map, coprod_inr,
        ← map_comp_rTensor, ← map_comp_lTensor, comp_assoc, ← coassoc, ← comp_assoc,
        TensorProduct.map_map_comp_assoc_eq, comp_apply, LinearEquiv.coe_coe]

end Prod

namespace Finsupp
variable (R : Type u) (ι : Type v) (A : Type w)
variable [CommSemiring R] [AddCommMonoid A] [Module R A] [Coalgebra R A]

open LinearMap

instance instCoalgebraStruct : CoalgebraStruct R (ι →₀ A) where
  comul' := Finsupp.lsum R fun i =>
    TensorProduct.map (Finsupp.lsingle i) (Finsupp.lsingle i) ∘ₗ comul R _
  counit' := Finsupp.lsum R fun _ => counit R _

@[simp]
theorem comul_single (i : ι) (a : A) :
    comul R _ (Finsupp.single i a) =
      (TensorProduct.map (Finsupp.lsingle i) (Finsupp.lsingle i) : _ →ₗ[R] _) (comul R _ a) :=
  lsum_single _ _ _ _

@[simp]
theorem counit_single (i : ι) (a : A) : counit R _ (Finsupp.single i a) = counit R _ a :=
  lsum_single _ _ _ _

theorem comul_comp_lsingle (i : ι) :
    comul R _ ∘ₗ (lsingle i : A →ₗ[R] _) =
    TensorProduct.map (lsingle i) (lsingle i) ∘ₗ comul R _ := by
  ext; simp

theorem comul_comp_lapply (i : ι) :
    comul R _ ∘ₗ (lapply i : _ →ₗ[R] A) = TensorProduct.map (lapply i) (lapply i) ∘ₗ comul R _ := by
  ext j : 1
  conv_rhs => rw [comp_assoc, comul_comp_lsingle, ← comp_assoc, ← TensorProduct.map_comp]
  obtain rfl | hij := eq_or_ne i j
  · rw [comp_assoc, lapply_comp_lsingle_same, comp_id,  TensorProduct.map_id, id_comp]
  · rw [comp_assoc, lapply_comp_lsingle_of_ne _ _ hij, comp_zero, TensorProduct.map_zero_left,
      zero_comp]

@[simp] theorem counit_comp_lsingle (i : ι) :
    counit R _ ∘ₗ (lsingle i : A →ₗ[R] _) = counit R _ := by
  ext; simp

/-- The `R`-module whose elements are functions `ι → A` which are zero on all but finitely many
elements of `ι` has a coalgebra structure. The coproduct `Δ` is given by `Δ(fᵢ a) = fᵢ a₁ ⊗ fᵢ a₂`
where `Δ(a) = a₁ ⊗ a₂` and the counit `ε` by `ε(fᵢ a) = ε(a)`, where `fᵢ a` is the function sending
`i` to `a` and all other elements of `ι` to zero. -/
instance instCoalgebra : Coalgebra R (ι →₀ A) where
  rTensor_counit_comp_comul := by
    ext : 1
    rw [comp_assoc, comul_comp_lsingle, ← comp_assoc, rTensor_comp_map, counit_comp_lsingle,
      ← lTensor_comp_rTensor, comp_assoc, rTensor_counit_comp_comul, lTensor_comp_mk]
  lTensor_counit_comp_comul := by
    ext : 1
    rw [comp_assoc, comul_comp_lsingle, ← comp_assoc, lTensor_comp_map, counit_comp_lsingle,
      ← rTensor_comp_lTensor, comp_assoc, lTensor_counit_comp_comul, rTensor_comp_flip_mk]
  coassoc := by
    ext i : 1
    simp_rw [comp_assoc, comul_comp_lsingle, ← comp_assoc, lTensor_comp_map, comul_comp_lsingle,
      comp_assoc, ← comp_assoc $ comul _ _, rTensor_comp_map, comul_comp_lsingle, ← map_comp_rTensor,
      ← map_comp_lTensor, comp_assoc, ← coassoc, ← comp_assoc $ comul _ _, ← comp_assoc,
        TensorProduct.map_map_comp_assoc_eq]

end Finsupp

end CommSemiring
