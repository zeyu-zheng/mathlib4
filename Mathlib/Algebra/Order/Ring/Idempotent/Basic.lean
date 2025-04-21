/-
Copyright (c) 2025 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
import Mathlib.Algebra.GroupWithZero.Center
import Mathlib.Algebra.Ring.Idempotent
import Mathlib.Algebra.Ring.Center
import Mathlib.Order.BooleanAlgebra
import Mathlib.Order.Hom.Basic

/-!
# Boolean algebra structure on idempotents in a commutative (semi)ring

We show that the idempotent in a commutative ring form a Boolean algebra, with complement given
by `a ↦ 1 - a` and infimum given by multiplication. In a commutative semiring where subtraction
is not available, it is still true that pairs of elements `(a, b)` satisfying `a * b = 0` and
`a + b = 1` form a Boolean algebra (such elements are automatically idempotents, and such a pair
is uniquely determined by either `a` or `b`).
-/

variable (R : Type*)

/-- A complete pair of central orthogonal idempotents in a unital, not necessarily associative
semiring is a pair of central elements whose product is 0 and whose sum is 1. -/
@[ext] structure CentralCompleteOrthogonalPair [Mul R] [Add R] [One R] [Zero R] where
  left : R
  right : R
  central_left : IsMulCentral left
  central_right : IsMulCentral right
  ortho : left * right = 0
  complete : left + right = 1

variable {R}

instance [Mul R] [AddCommMagma R] [One R] [Zero R] :
    HasCompl (CentralCompleteOrthogonalPair R) where
  compl a :=
  { left := a.right
    right := a.left
    central_left := a.central_right
    central_right := a.central_left
    ortho := (a.central_right.comm _).trans a.ortho
    complete := (add_comm ..).trans a.complete }

lemma eq_of_mul_eq_add_eq_one [MulOneClass R] [Add R] [LeftDistribClass R] [RightDistribClass R]
    (a : R) {b c : R} (mul : a * b = c * a) (add_ab : a + b = 1) (add_ac : a + c = 1) :
    b = c :=
  calc b = (a + c) * b := by rw [add_ac, one_mul]
       _ = c * (a + b) := by rw [add_mul, mul, mul_add]
       _ = c := by rw [add_ab, mul_one]

namespace CentralCompleteOrthogonalPair

section NonAssocSemiring

variable [NonAssocSemiring R]

/-- To construct a `CentralCompleteOrthogonalPair`, one only needs to prove that
the first element needs to be central. -/
abbrev mkOfCentralLeft (a b : R) (ha : IsMulCentral a) (ortho : a * b = 0) (complete : a + b = 1) :
    CentralCompleteOrthogonalPair R where
  left := a
  right := b
  central_left := ha
  central_right := by
    refine ⟨fun c ↦ (commute_iff_eq ..).mpr ?_, fun c d ↦ ?_, fun c d ↦ ?_⟩
    · conv_lhs => rw [← mul_one (b * c), ← complete, mul_add,
        ← (ha.comm _).eq, ha.left_assoc, ortho, zero_mul, zero_add]
      conv_rhs => rw [← one_mul c, ← complete, add_mul, add_mul,
        (ha.comm _).eq, ha.mid_assoc, ortho, mul_zero, zero_add]
    · conv_lhs => rw [← one_mul c, ← complete, add_mul, add_mul, mul_add,
        ← ha.left_assoc, ← ha.left_comm, ha.left_assoc, ortho, zero_mul, zero_add]
      conv_rhs => rw [← one_mul (b * c * d), ← complete, add_mul, ha.left_assoc,
        ha.left_assoc, ortho, zero_mul, zero_mul, zero_add]
    · conv_lhs => rw [← mul_one d, ← complete, mul_add, mul_add, add_mul,
        ← ha.right_assoc, ha.mid_assoc, ortho, mul_zero, zero_add]
      conv_rhs => rw [← mul_one (c * (d * b)), ← complete, mul_add, ha.right_assoc,
        ha.right_assoc, ← (ha.comm _).eq, ortho, mul_zero, mul_zero, zero_add]
  ortho := ortho
  complete := complete

/-- To construct a `CentralCompleteOrthogonalPair`, one could alternatively prove that
the second element is central. -/
abbrev mkOfCentralRight (a b : R) (hb : IsMulCentral b) (ortho : a * b = 0) (complete : a + b = 1) :
    CentralCompleteOrthogonalPair R :=
  (mkOfCentralLeft b a hb ((hb.comm _).trans ortho) ((add_comm ..).trans complete))ᶜ

variable {a b : CentralCompleteOrthogonalPair R}

lemma ext_left (eq : a.left = b.left) : a = b := by
  refine CentralCompleteOrthogonalPair.ext eq (eq_of_mul_eq_add_eq_one a.left ?_ a.complete ?_)
  · rw [a.ortho, ← a.central_left.comm, eq, b.ortho]
  · rw [eq, b.complete]

lemma ext_right (eq : a.right = b.right) : a = b := by
  refine CentralCompleteOrthogonalPair.ext (eq_of_mul_eq_add_eq_one a.right ?_ ?_ ?_) eq
  · rw [a.central_right.comm, a.ortho, eq, b.ortho]
  · rw [add_comm, a.complete]
  · rw [add_comm, eq, b.complete]

@[deprecated (since := "2025-04-20")] alias _root_.mul_eq_zero_add_eq_one_ext_left := ext_left
@[deprecated (since := "2025-04-20")] alias _root_.mul_eq_zero_add_eq_one_ext_right := ext_right

lemma isIdempotentElem_left (a : CentralCompleteOrthogonalPair R) : IsIdempotentElem a.left :=
  (IsIdempotentElem.of_mul_add a.ortho a.complete).1

lemma isIdempotentElem_right (a : CentralCompleteOrthogonalPair R) : IsIdempotentElem a.right :=
  (IsIdempotentElem.of_mul_add a.ortho a.complete).2

-- Note: the above four lemmas only need the commutativity condition in `IsMulCentral`

instance : PartialOrder (CentralCompleteOrthogonalPair R) where
  le a b := a.left * b.left = a.left
  le_refl a := a.isIdempotentElem_left
  le_trans a b c hab hbc := show _ = _ by rw [← hab, ← a.central_left.left_assoc, hbc]
  le_antisymm a b hab hba := ext_left <| by rw [← hab, a.central_left.comm, hba]

theorem le_iff_mul_eq_zero : a ≤ b ↔ a.left * b.right = 0 where
  mp h := by rw [← h, ← a.central_left.left_assoc, b.ortho, mul_zero]
  mpr h := by
    simp_rw [(· ≤ ·)]; conv_rhs => rw [← mul_one a.left, ← b.complete, mul_add, h, add_zero]

theorem le_iff_right : a ≤ b ↔ a.right * b.right = b.right := le_iff_mul_eq_zero.trans
  { mp h := by conv_rhs => rw [← one_mul b.right, ← a.complete, add_mul, h, zero_add]
    mpr h := by rw [← h, a.central_left.left_assoc, a.ortho, zero_mul] }

instance : SemilatticeSup (CentralCompleteOrthogonalPair R) where
  sup a b :=
  { left := a.left + a.right * b.left
    right := a.right * b.right
    central_left := Set.add_mem_center a.central_left
      (Set.mul_mem_center a.central_right b.central_left)
    central_right := Set.mul_mem_center a.central_right b.central_right
    ortho := by simp_rw [add_mul, ← a.central_right.left_assoc, b.central_left.left_comm,
      b.ortho, mul_zero, a.central_left.left_assoc, a.ortho, zero_mul, add_zero]
    complete := by simp_rw [add_assoc, ← mul_add, b.complete, mul_one, a.complete] }
  le_sup_left a b := by simp_rw [(· ≤ ·), mul_add, a.central_left.left_assoc,
    a.ortho, zero_mul, add_zero, a.isIdempotentElem_left.eq]
  le_sup_right a b := by
    simp_rw [(· ≤ ·), mul_add, (a.central_right.comm _).eq, b.central_left.left_assoc,
      b.isIdempotentElem_left.eq, ← mul_add, a.complete, mul_one]
  sup_le a b c hac hbc := by simp_rw [(· ≤ ·), add_mul, ← a.central_right.left_assoc]; rw [hac, hbc]

instance : BooleanAlgebra (CentralCompleteOrthogonalPair R) where
  inf a b := (aᶜ ⊔ bᶜ)ᶜ
  inf_le_left a b := by simp_rw [(· ≤ ·), (· ⊔ ·), (·ᶜ), SemilatticeSup.sup,
    a.central_left.right_comm, a.isIdempotentElem_left.eq]
  inf_le_right a b := by simp_rw [(· ≤ ·), (· ⊔ ·), (·ᶜ), SemilatticeSup.sup,
    ← a.central_left.left_assoc, b.isIdempotentElem_left.eq]
  le_inf a b c hab hac := by
    simp_rw [(· ≤ ·), (· ⊔ ·), (·ᶜ), SemilatticeSup.sup, a.central_left.left_assoc]; rw [hab, hac]
  le_sup_inf a b c := Eq.le <| ext_right <| by simp_rw [(· ⊔ ·), (· ⊓ ·),
    (·ᶜ), SemilatticeSup.sup, add_mul, mul_add, ← a.central_right.left_assoc,
    b.central_left.left_comm, a.central_right.left_assoc, a.isIdempotentElem_right.eq,
    a.central_left.left_assoc, a.ortho, zero_mul, zero_add]
  top := ⟨1, 0, Set.one_mem_center, Set.zero_mem_center, mul_zero _, add_zero _⟩
  bot := ⟨0, 1, Set.zero_mem_center, Set.one_mem_center, zero_mul _, zero_add _⟩
  inf_compl_le_bot a := Eq.le <| ext_right <| by
    simp_rw [(· ⊔ ·), (· ⊓ ·), (·ᶜ), SemilatticeSup.sup,
      (IsIdempotentElem.of_mul_add a.ortho a.complete).1.eq, add_comm, a.complete]
  top_le_sup_compl a := Eq.le <| ext_left <| by simp_rw [(· ⊔ ·), (·ᶜ),
    SemilatticeSup.sup, a.isIdempotentElem_right.eq, a.complete]
  le_top _ := mul_one _
  bot_le _ := zero_mul _
  sdiff_eq _ _ := rfl
  himp_eq _ _ := rfl

end NonAssocSemiring

section CommSemiring

variable (R) [CommSemiring R]

/-- In a commutative semiring, we do not need to supply the `IsMulCentral` conditions to
construct a `CentralCompleteOrthogonalPair`. -/
abbrev equivMulZeroAddOne :
    CentralCompleteOrthogonalPair R ≃ {a : R × R // a.1 * a.2 = 0 ∧ a.1 + a.2 = 1} where
  toFun a := ⟨(a.left, a.right), a.ortho, a.complete⟩
  invFun a := ⟨a.1.1, a.1.2, Semigroup.mem_center_iff.mpr fun _ ↦ mul_comm ..,
    Semigroup.mem_center_iff.mpr fun _ ↦ mul_comm .., a.2.1, a.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : BooleanAlgebra {a : R × R // a.1 * a.2 = 0 ∧ a.1 + a.2 = 1} :=
  (equivMulZeroAddOne R).symm.booleanAlgebra

/-- `equivMulZeroAddOne` as an `OrderIso`. -/
abbrev orderIsoMulZeroAddOne :
    CentralCompleteOrthogonalPair R ≃o {a : R × R // a.1 * a.2 = 0 ∧ a.1 + a.2 = 1} where
  __ := equivMulZeroAddOne R
  map_rel_iff' := Iff.rfl

end CommSemiring

end CentralCompleteOrthogonalPair

instance {S : Type*} [CommSemigroup S] : SemilatticeInf {a : S // IsIdempotentElem a} where
  le a b := a.1 * b = a
  le_refl a := a.2
  le_trans a b c hab hbc := show _ = _ by rw [← hab, mul_assoc, hbc]
  le_antisymm a b hab hba := Subtype.ext <| by rw [← hab, mul_comm, hba]
  inf a b := ⟨_, a.2.mul b.2⟩
  inf_le_left a b := show _ = _ by simp_rw [mul_right_comm]; rw [a.2]
  inf_le_right a b := show _ = _ by simp_rw [mul_assoc]; rw [b.2]
  le_inf a b c hab hac := by simp_rw [← mul_assoc]; rw [hab, hac]

instance {M : Type*} [CommMonoid M] : OrderTop {a : M // IsIdempotentElem a} where
  top := ⟨1, .one⟩
  le_top _ := mul_one _

instance {M₀ : Type*} [CommMonoidWithZero M₀] : OrderBot {a : M₀ // IsIdempotentElem a} where
  bot := ⟨0, .zero⟩
  bot_le _ := zero_mul _

section CommRing

variable [CommRing R]

instance : Lattice {a : R // IsIdempotentElem a} where
  __ : SemilatticeInf _ := inferInstance
  sup a b := ⟨_, a.2.add_sub_mul b.2⟩
  le_sup_left a b := show _ = _ by
    simp_rw [mul_sub, mul_add]; rw [← mul_assoc, a.2, add_sub_cancel_right]
  le_sup_right a b := show _ = _ by
    simp_rw [mul_sub, mul_add]; rw [← mul_assoc, mul_right_comm, b.2, add_sub_cancel_left]
  sup_le a b c hac hbc := show _ = _ by simp_rw [sub_mul, add_mul, mul_assoc]; rw [hbc, hac]

instance : BooleanAlgebra {a : R // IsIdempotentElem a} where
  __ : DistribLattice _ := .ofInfSupLe fun a b c ↦ Eq.le <| Subtype.ext <| by
    simp_rw [(· ⊔ ·), (· ⊓ ·), SemilatticeSup.sup, SemilatticeInf.inf, Lattice.inf,
      SemilatticeInf.inf, mul_sub, mul_add, mul_mul_mul_comm]
    rw [a.2]
  __ : OrderTop _ := inferInstance
  __ : OrderBot _ := inferInstance
  compl a := ⟨_, a.2.one_sub⟩
  inf_compl_le_bot a := (mul_zero _).trans ((mul_one_sub ..).trans <| by rw [a.2, sub_self]).symm
  top_le_sup_compl a := (one_mul _).trans <| by
    simp_rw [(· ⊔ ·), SemilatticeSup.sup, add_sub_cancel, mul_sub, mul_one]
    rw [a.2, sub_self, sub_zero]; rfl
  sdiff_eq _ _ := rfl
  himp a b := ⟨_, (a.2.mul b.2.one_sub).one_sub⟩
  himp_eq a b := Subtype.ext <| by simp_rw [(· ⊔ ·), SemilatticeSup.sup,
    add_comm b.1, add_sub_assoc, mul_sub, mul_one, sub_sub_cancel, sub_add, mul_comm]

/-- In a commutative ring, the idempotents are in 1-1 correspondence with pairs of elements
whose product is 0 and whose sum is 1. The correspondence is given by `a ↔ (a, 1 - a)`. -/
def OrderIso.isIdempotentElemMulZeroAddOne :
    {a : R // IsIdempotentElem a} ≃o {a : R × R // a.1 * a.2 = 0 ∧ a.1 + a.2 = 1} where
  toFun a := ⟨(a, 1 - a), by simp_rw [mul_sub, mul_one, a.2.eq, sub_self], by rw [add_sub_cancel]⟩
  invFun a := ⟨a.1.1, (IsIdempotentElem.of_mul_add a.2.1 a.2.2).1⟩
  left_inv _ := rfl
  right_inv a := Subtype.ext <| Prod.ext rfl <| sub_eq_of_eq_add <| a.2.2.symm.trans (add_comm ..)
  map_rel_iff' := Iff.rfl

end CommRing
