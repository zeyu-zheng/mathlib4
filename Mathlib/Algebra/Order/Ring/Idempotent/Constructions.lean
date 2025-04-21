/-
Copyright (c) 2025 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
import Mathlib.Algebra.Order.Ring.Idempotent.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Algebra.Ring.Pi
import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.RingTheory.SimpleRing.Basic

#trans_imports "Mathlib."

/-!
# Constructions related to `CentralCompleteOrthogonalPair`
-/

namespace CentralCompleteOrthogonalPair

section map

variable {R S F : Type*} [NonAssocSemiring R] [NonAssocSemiring S]

/-- The image of a `CentralCompleteOrthogonalPair` under a surjective ring homomorphism
is a `CentralCompleteOrthogonalPair`. -/
@[simps]
def mapOfSurjective [FunLike F R S] [RingHomClass F R S] (f : F) (hf : Function.Surjective f) :
    CentralCompleteOrthogonalPair R →o CentralCompleteOrthogonalPair S where
  toFun p :=
  { left := f p.left
    right := f p.right
    central_left := p.central_left.map_of_surjective f hf
    central_right := p.central_right.map_of_surjective f hf
    ortho := by rw [← map_mul, p.ortho, map_zero]
    complete := by rw [← map_add, p.complete, map_one] }
  monotone' p q h := by simp_rw [(· ≤ ·)] at h ⊢; rw [← map_mul, h]

/-- The image of a `CentralCompleteOrthogonalPair` under a ring isomorphism is a
`CentralCompleteOrthogonalPair`. -/
@[simps!] def mapEquiv [EquivLike F R S] [RingEquivClass F R S] (f : F) :
    CentralCompleteOrthogonalPair R ≃o CentralCompleteOrthogonalPair S :=
  .ofHomInv (mapOfSurjective f (EquivLike.surjective f))
    (mapOfSurjective _ (EquivLike.surjective (f : R ≃+* S).symm))
    (DFunLike.ext _ _ fun _ ↦ ext_left <| EquivLike.right_inv ..)
    (DFunLike.ext _ _ fun _ ↦ ext_right <| EquivLike.left_inv ..)

end map

section RingCon

variable {R : Type*} [NonAssocSemiring R]

/-- The order embedding from `CentralCompleteOrthogonalPair R` to `RingCon R`. -/
def toRingCon : CentralCompleteOrthogonalPair R ↪o RingCon R :=
  .ofMapLEIff (fun p ↦
  { __ := Setoid.ker (· * p.right)
    mul' h h' := have hp := p.central_right; by
      simp_rw [Setoid.ker_def] at h h' ⊢
      simp_rw [hp.right_assoc, h', ← (hp.comm _).eq, ← hp.mid_assoc, h]
    add' h h' := by simp_rw [Setoid.ker_def] at h h' ⊢; simp_rw [add_mul, h, h'] })
  fun p q ↦ .symm <| le_iff_right.trans <|
  { mpr le := have : _ = _ := le (p.isIdempotentElem_right.trans (one_mul _).symm)
      by simpa only [one_mul]
    mp le _ _ (eq : _ * _ = _ * _) := show _ = _ by
      rw [← le]; simp_rw [← q.central_right.right_assoc, eq] }

@[simp] theorem toRingCon_bot : toRingCon (R := R) ⊥ = ⊥ :=
  bot_unique fun x y h ↦ (mul_one x).symm.trans (h.trans (mul_one y))

@[simp] theorem toRingCon_top : toRingCon (R := R) ⊤ = ⊤ :=
  top_unique fun x y _ ↦ (mul_zero x).trans (mul_zero y).symm

end RingCon

/-- A semiring is indecomposable if it does not admit a nontrivial `CentralCompleteOrthogonalPair`.
Equivalently, it is not the direct product of two nontrivial semirings. -/
abbrev IsIndecomposableRing (R) [NonAssocSemiring R]: Prop :=
  IsSimpleOrder (CentralCompleteOrthogonalPair R)

instance (R) [NonAssocRing R] [IsSimpleRing R] : IsIndecomposableRing R where
  exists_pair_ne := ⟨⊥, ⊤, fun h ↦ zero_ne_one congr(($h).left)⟩
  eq_bot_or_eq_top p := by
    have := TwoSidedIdeal.orderIsoRingCon (R := R).symm.isSimpleOrder
    refine (eq_bot_or_eq_top p.toRingCon).imp ?_ ?_ <;>
      exact fun h ↦ toRingCon.injective <| by simp [h]

/-- The complete pairs of central orthogonal idempotents in a product of rings correspond to
tuples consisting of complete pairs of central orthogonal idempotents in the individual rings. -/
protected def piOrderIso {ι} {R : ι → Type*} [∀ i, NonAssocSemiring (R i)] :
    CentralCompleteOrthogonalPair (Π i, R i) ≃o Π i, CentralCompleteOrthogonalPair (R i) where
  toFun p i :=
  { left := p.left i
    right := p.right i
    central_left := Pi.isMulCentral_iff.mp p.central_left i
    central_right := Pi.isMulCentral_iff.mp p.central_right i
    ortho := congr_fun p.ortho i
    complete := congr_fun p.complete i }
  invFun p :=
  { left i := (p i).left
    right i := (p i).right
    central_left := Pi.isMulCentral_iff.mpr fun i ↦ (p i).central_left
    central_right := Pi.isMulCentral_iff.mpr fun i ↦ (p i).central_right
    ortho := funext fun i ↦ (p i).ortho
    complete := funext fun i ↦ (p i).complete }
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := by simp [(· ≤ ·), funext_iff]

end CentralCompleteOrthogonalPair
