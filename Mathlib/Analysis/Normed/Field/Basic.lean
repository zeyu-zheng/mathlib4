import Mathlib.Tactic.Have
/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Johannes Hölzl
-/
import Mathlib.Algebra.Algebra.NonUnitalSubalgebra
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Algebra.Order.Ring.Finset
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Analysis.Normed.Group.Rat
import Mathlib.Analysis.Normed.Group.Submodule
import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Topology.Instances.NNReal
import Mathlib.Topology.MetricSpace.DilationEquiv

/-!
# Normed fields

In this file we define (semi)normed rings and fields. We also prove some theorems about these
definitions.
-/

variable {α : Type*} {β : Type*} {γ : Type*} {ι : Type*}

open Filter Metric Bornology
open scoped Topology NNReal ENNReal uniformity Pointwise

/-- A non-unital seminormed ring is a not-necessarily-unital ring
endowed with a seminorm which satisfies the inequality `‖x y‖ ≤ ‖x‖ ‖y‖`. -/
class NonUnitalSeminormedRing (α : Type*) extends Norm α, NonUnitalRing α,
  PseudoMetricSpace α where
  /-- The distance is induced by the norm. -/
  dist_eq : ∀ x y, dist x y = norm (x - y)
  /-- The norm is submultiplicative. -/
  norm_mul : ∀ a b, norm (a * b) ≤ norm a * norm b

/-- A seminormed ring is a ring endowed with a seminorm which satisfies the inequality
`‖x y‖ ≤ ‖x‖ ‖y‖`. -/
class SeminormedRing (α : Type*) extends Norm α, Ring α, PseudoMetricSpace α where
  /-- The distance is induced by the norm. -/
  dist_eq : ∀ x y, dist x y = norm (x - y)
  /-- The norm is submultiplicative. -/
  norm_mul : ∀ a b, norm (a * b) ≤ norm a * norm b

-- see Note [lower instance priority]
/-- A seminormed ring is a non-unital seminormed ring. -/
instance (priority := 100) SeminormedRing.toNonUnitalSeminormedRing [β : SeminormedRing α] :
    NonUnitalSeminormedRing α :=
  { β with }

/-- A non-unital normed ring is a not-necessarily-unital ring
endowed with a norm which satisfies the inequality `‖x y‖ ≤ ‖x‖ ‖y‖`. -/
class NonUnitalNormedRing (α : Type*) extends Norm α, NonUnitalRing α, MetricSpace α where
  /-- The distance is induced by the norm. -/
  dist_eq : ∀ x y, dist x y = norm (x - y)
  /-- The norm is submultiplicative. -/
  norm_mul : ∀ a b, norm (a * b) ≤ norm a * norm b

-- see Note [lower instance priority]
/-- A non-unital normed ring is a non-unital seminormed ring. -/
instance (priority := 100) NonUnitalNormedRing.toNonUnitalSeminormedRing
    [β : NonUnitalNormedRing α] : NonUnitalSeminormedRing α :=
  { β with }

/-- A normed ring is a ring endowed with a norm which satisfies the inequality `‖x y‖ ≤ ‖x‖ ‖y‖`. -/
class NormedRing (α : Type*) extends Norm α, Ring α, MetricSpace α where
  /-- The distance is induced by the norm. -/
  dist_eq : ∀ x y, dist x y = norm (x - y)
  /-- The norm is submultiplicative. -/
  norm_mul : ∀ a b, norm (a * b) ≤ norm a * norm b

/-- A normed division ring is a division ring endowed with a seminorm which satisfies the equality
`‖x y‖ = ‖x‖ ‖y‖`. -/
class NormedDivisionRing (α : Type*) extends Norm α, DivisionRing α, MetricSpace α where
  /-- The distance is induced by the norm. -/
  dist_eq : ∀ x y, dist x y = norm (x - y)
  /-- The norm is multiplicative. -/
  norm_mul' : ∀ a b, norm (a * b) = norm a * norm b

-- see Note [lower instance priority]
/-- A normed division ring is a normed ring. -/
instance (priority := 100) NormedDivisionRing.toNormedRing [β : NormedDivisionRing α] :
    NormedRing α :=
  { β with norm_mul := fun a b => (NormedDivisionRing.norm_mul' a b).le }

-- see Note [lower instance priority]
/-- A normed ring is a seminormed ring. -/
instance (priority := 100) NormedRing.toSeminormedRing [β : NormedRing α] : SeminormedRing α :=
  { β with }

-- see Note [lower instance priority]
/-- A normed ring is a non-unital normed ring. -/
instance (priority := 100) NormedRing.toNonUnitalNormedRing [β : NormedRing α] :
    NonUnitalNormedRing α :=
  { β with }

/-- A non-unital seminormed commutative ring is a non-unital commutative ring endowed with a
seminorm which satisfies the inequality `‖x y‖ ≤ ‖x‖ ‖y‖`. -/
class NonUnitalSeminormedCommRing (α : Type*) extends NonUnitalSeminormedRing α where
  /-- Multiplication is commutative. -/
  mul_comm : ∀ x y : α, x * y = y * x

/-- A non-unital normed commutative ring is a non-unital commutative ring endowed with a
norm which satisfies the inequality `‖x y‖ ≤ ‖x‖ ‖y‖`. -/
class NonUnitalNormedCommRing (α : Type*) extends NonUnitalNormedRing α where
  /-- Multiplication is commutative. -/
  mul_comm : ∀ x y : α, x * y = y * x

-- see Note [lower instance priority]
/-- A non-unital normed commutative ring is a non-unital seminormed commutative ring. -/
instance (priority := 100) NonUnitalNormedCommRing.toNonUnitalSeminormedCommRing
    [β : NonUnitalNormedCommRing α] : NonUnitalSeminormedCommRing α :=
  { β with }

/-- A seminormed commutative ring is a commutative ring endowed with a seminorm which satisfies
the inequality `‖x y‖ ≤ ‖x‖ ‖y‖`. -/
class SeminormedCommRing (α : Type*) extends SeminormedRing α where
  /-- Multiplication is commutative. -/
  mul_comm : ∀ x y : α, x * y = y * x

/-- A normed commutative ring is a commutative ring endowed with a norm which satisfies
the inequality `‖x y‖ ≤ ‖x‖ ‖y‖`. -/
class NormedCommRing (α : Type*) extends NormedRing α where
  /-- Multiplication is commutative. -/
  mul_comm : ∀ x y : α, x * y = y * x

-- see Note [lower instance priority]
/-- A seminormed commutative ring is a non-unital seminormed commutative ring. -/
instance (priority := 100) SeminormedCommRing.toNonUnitalSeminormedCommRing
    [β : SeminormedCommRing α] : NonUnitalSeminormedCommRing α :=
  { β with }

-- see Note [lower instance priority]
/-- A normed commutative ring is a non-unital normed commutative ring. -/
instance (priority := 100) NormedCommRing.toNonUnitalNormedCommRing
    [β : NormedCommRing α] : NonUnitalNormedCommRing α :=
  { β with }

-- see Note [lower instance priority]
/-- A normed commutative ring is a seminormed commutative ring. -/
instance (priority := 100) NormedCommRing.toSeminormedCommRing [β : NormedCommRing α] :
    SeminormedCommRing α :=
  { β with }

instance PUnit.normedCommRing : NormedCommRing PUnit :=
  { PUnit.normedAddCommGroup, PUnit.commRing with
    norm_mul := fun _ _ => by simp }

/-- A mixin class with the axiom `‖1‖ = 1`. Many `NormedRing`s and all `NormedField`s satisfy this
axiom. -/
class NormOneClass (α : Type*) [Norm α] [One α] : Prop where
  /-- The norm of the multiplicative identity is 1. -/
  norm_one : ‖(1 : α)‖ = 1

export NormOneClass (norm_one)

attribute [simp] norm_one

@[simp]
theorem nnnorm_one [SeminormedAddCommGroup α] [One α] [NormOneClass α] : ‖(1 : α)‖₊ = 1 :=
  NNReal.eq norm_one

theorem NormOneClass.nontrivial (α : Type*) [SeminormedAddCommGroup α] [One α] [NormOneClass α] :
    Nontrivial α :=
  nontrivial_of_ne 0 1 <| ne_of_apply_ne norm <| by simp

-- see Note [lower instance priority]
instance (priority := 100) NonUnitalSeminormedCommRing.toNonUnitalCommRing
    [β : NonUnitalSeminormedCommRing α] : NonUnitalCommRing α :=
  { β with }

-- see Note [lower instance priority]
instance (priority := 100) SeminormedCommRing.toCommRing [β : SeminormedCommRing α] : CommRing α :=
  { β with }

-- see Note [lower instance priority]
instance (priority := 100) NonUnitalNormedRing.toNormedAddCommGroup [β : NonUnitalNormedRing α] :
    NormedAddCommGroup α :=
  { β with }

-- see Note [lower instance priority]
instance (priority := 100) NonUnitalSeminormedRing.toSeminormedAddCommGroup
    [NonUnitalSeminormedRing α] : SeminormedAddCommGroup α :=
  { ‹NonUnitalSeminormedRing α› with }

instance ULift.normOneClass [SeminormedAddCommGroup α] [One α] [NormOneClass α] :
    NormOneClass (ULift α) :=
  ⟨by simp [ULift.norm_def]⟩

instance Prod.normOneClass [SeminormedAddCommGroup α] [One α] [NormOneClass α]
    [SeminormedAddCommGroup β] [One β] [NormOneClass β] : NormOneClass (α × β) :=
  ⟨by simp [Prod.norm_def]⟩

instance Pi.normOneClass {ι : Type*} {α : ι → Type*} [Nonempty ι] [Fintype ι]
    [∀ i, SeminormedAddCommGroup (α i)] [∀ i, One (α i)] [∀ i, NormOneClass (α i)] :
    NormOneClass (∀ i, α i) :=
  ⟨by simpa [Pi.norm_def] using Finset.sup_const Finset.univ_nonempty 1⟩

instance MulOpposite.normOneClass [SeminormedAddCommGroup α] [One α] [NormOneClass α] :
    NormOneClass αᵐᵒᵖ :=
  ⟨@norm_one α _ _ _⟩

section NonUnitalSeminormedRing

variable [NonUnitalSeminormedRing α]

theorem norm_mul_le (a b : α) : ‖a * b‖ ≤ ‖a‖ * ‖b‖ :=
  NonUnitalSeminormedRing.norm_mul _ _

theorem nnnorm_mul_le (a b : α) : ‖a * b‖₊ ≤ ‖a‖₊ * ‖b‖₊ := by
  simpa only [← norm_toNNReal, ← Real.toNNReal_mul (norm_nonneg _)] using
    Real.toNNReal_mono (norm_mul_le _ _)

theorem one_le_norm_one (β) [NormedRing β] [Nontrivial β] : 1 ≤ ‖(1 : β)‖ :=
  (le_mul_iff_one_le_left <| norm_pos_iff.mpr (one_ne_zero : (1 : β) ≠ 0)).mp
    (by simpa only [mul_one] using norm_mul_le (1 : β) 1)

theorem one_le_nnnorm_one (β) [NormedRing β] [Nontrivial β] : 1 ≤ ‖(1 : β)‖₊ :=
  one_le_norm_one β

theorem Filter.Tendsto.zero_mul_isBoundedUnder_le {f g : ι → α} {l : Filter ι}
    (hf : Tendsto f l (𝓝 0)) (hg : IsBoundedUnder (· ≤ ·) l ((‖·‖) ∘ g)) :
    Tendsto (fun x => f x * g x) l (𝓝 0) :=
  hf.op_zero_isBoundedUnder_le hg (· * ·) norm_mul_le

theorem Filter.isBoundedUnder_le_mul_tendsto_zero {f g : ι → α} {l : Filter ι}
    (hf : IsBoundedUnder (· ≤ ·) l (norm ∘ f)) (hg : Tendsto g l (𝓝 0)) :
    Tendsto (fun x => f x * g x) l (𝓝 0) :=
  hg.op_zero_isBoundedUnder_le hf (flip (· * ·)) fun x y =>
    (norm_mul_le y x).trans_eq (mul_comm _ _)

/-- In a seminormed ring, the left-multiplication `AddMonoidHom` is bounded. -/
theorem mulLeft_bound (x : α) : ∀ y : α, ‖AddMonoidHom.mulLeft x y‖ ≤ ‖x‖ * ‖y‖ :=
  norm_mul_le x

/-- In a seminormed ring, the right-multiplication `AddMonoidHom` is bounded. -/
theorem mulRight_bound (x : α) : ∀ y : α, ‖AddMonoidHom.mulRight x y‖ ≤ ‖x‖ * ‖y‖ := fun y => by
  rw [mul_comm]
  exact norm_mul_le y x

/-- A non-unital subalgebra of a non-unital seminormed ring is also a non-unital seminormed ring,
with the restriction of the norm.  -/
instance NonUnitalSubalgebra.nonUnitalSeminormedRing {𝕜 : Type*} [CommRing 𝕜] {E : Type*}
    [NonUnitalSeminormedRing E] [Module 𝕜 E] (s : NonUnitalSubalgebra 𝕜 E) :
    NonUnitalSeminormedRing s :=
  { s.toSubmodule.seminormedAddCommGroup, s.toNonUnitalRing with
    norm_mul := fun a b => norm_mul_le a.1 b.1 }

/-- A non-unital subalgebra of a non-unital seminormed ring is also a non-unital seminormed ring,
with the restriction of the norm.  -/
-- necessary to require `SMulMemClass S 𝕜 E` so that `𝕜` can be determined as an `outParam`
@[nolint unusedArguments]
instance (priority := 75) NonUnitalSubalgebraClass.nonUnitalSeminormedRing {S 𝕜 E : Type*}
    [CommRing 𝕜] [NonUnitalSeminormedRing E] [Module 𝕜 E] [SetLike S E] [NonUnitalSubringClass S E]
    [SMulMemClass S 𝕜 E] (s : S) :
    NonUnitalSeminormedRing s :=
  { AddSubgroupClass.seminormedAddCommGroup s, NonUnitalSubringClass.toNonUnitalRing s with
    norm_mul := fun a b => norm_mul_le a.1 b.1 }

/-- A non-unital subalgebra of a non-unital normed ring is also a non-unital normed ring, with the
restriction of the norm.  -/
instance NonUnitalSubalgebra.nonUnitalNormedRing {𝕜 : Type*} [CommRing 𝕜] {E : Type*}
    [NonUnitalNormedRing E] [Module 𝕜 E] (s : NonUnitalSubalgebra 𝕜 E) : NonUnitalNormedRing s :=
  { s.nonUnitalSeminormedRing with
    eq_of_dist_eq_zero := eq_of_dist_eq_zero }

/-- A non-unital subalgebra of a non-unital normed ring is also a non-unital normed ring,
with the restriction of the norm.  -/
instance (priority := 75) NonUnitalSubalgebraClass.nonUnitalNormedRing {S 𝕜 E : Type*}
    [CommRing 𝕜] [NonUnitalNormedRing E] [Module 𝕜 E] [SetLike S E] [NonUnitalSubringClass S E]
    [SMulMemClass S 𝕜 E] (s : S) :
    NonUnitalNormedRing s :=
  { nonUnitalSeminormedRing s with
    eq_of_dist_eq_zero := eq_of_dist_eq_zero }

instance ULift.nonUnitalSeminormedRing : NonUnitalSeminormedRing (ULift α) :=
  { ULift.seminormedAddCommGroup, ULift.nonUnitalRing with
    norm_mul := fun x y => (norm_mul_le x.down y.down : _) }

/-- Non-unital seminormed ring structure on the product of two non-unital seminormed rings,
  using the sup norm. -/
instance Prod.nonUnitalSeminormedRing [NonUnitalSeminormedRing β] :
    NonUnitalSeminormedRing (α × β) :=
  { seminormedAddCommGroup, instNonUnitalRing with
    norm_mul := fun x y =>
      calc
        ‖x * y‖ = ‖(x.1 * y.1, x.2 * y.2)‖ := rfl
        _ = max ‖x.1 * y.1‖ ‖x.2 * y.2‖ := rfl
        _ ≤ max (‖x.1‖ * ‖y.1‖) (‖x.2‖ * ‖y.2‖) :=
          (max_le_max (norm_mul_le x.1 y.1) (norm_mul_le x.2 y.2))
        _ = max (‖x.1‖ * ‖y.1‖) (‖y.2‖ * ‖x.2‖) := by simp [mul_comm]
        _ ≤ max ‖x.1‖ ‖x.2‖ * max ‖y.2‖ ‖y.1‖ := by
          apply max_mul_mul_le_max_mul_max <;> simp [norm_nonneg]
        _ = max ‖x.1‖ ‖x.2‖ * max ‖y.1‖ ‖y.2‖ := by simp [max_comm]
        _ = ‖x‖ * ‖y‖ := rfl
         }

/-- Non-unital seminormed ring structure on the product of finitely many non-unital seminormed
rings, using the sup norm. -/
instance Pi.nonUnitalSeminormedRing {π : ι → Type*} [Fintype ι]
    [∀ i, NonUnitalSeminormedRing (π i)] : NonUnitalSeminormedRing (∀ i, π i) :=
  { Pi.seminormedAddCommGroup, Pi.nonUnitalRing with
    norm_mul := fun x y =>
      NNReal.coe_mono <|
        calc
          (Finset.univ.sup fun i => ‖x i * y i‖₊) ≤
              Finset.univ.sup ((fun i => ‖x i‖₊) * fun i => ‖y i‖₊) :=
            Finset.sup_mono_fun fun _ _ => norm_mul_le _ _
          _ ≤ (Finset.univ.sup fun i => ‖x i‖₊) * Finset.univ.sup fun i => ‖y i‖₊ :=
            Finset.sup_mul_le_mul_sup_of_nonneg _ (fun _ _ => zero_le _) fun _ _ => zero_le _
           }

instance MulOpposite.instNonUnitalSeminormedRing : NonUnitalSeminormedRing αᵐᵒᵖ where
  __ := instNonUnitalRing
  __ := instSeminormedAddCommGroup
  norm_mul := MulOpposite.rec' fun x ↦ MulOpposite.rec' fun y ↦
    (norm_mul_le y x).trans_eq (mul_comm _ _)

end NonUnitalSeminormedRing

section SeminormedRing

variable [SeminormedRing α]

/-- A subalgebra of a seminormed ring is also a seminormed ring, with the restriction of the
norm. -/
instance Subalgebra.seminormedRing {𝕜 : Type*} [CommRing 𝕜] {E : Type*} [SeminormedRing E]
    [Algebra 𝕜 E] (s : Subalgebra 𝕜 E) : SeminormedRing s :=
  { s.toSubmodule.seminormedAddCommGroup, s.toRing with
    norm_mul := fun a b => norm_mul_le a.1 b.1 }

/-- A subalgebra of a seminormed ring is also a seminormed ring, with the restriction of the
norm. -/
-- necessary to require `SMulMemClass S 𝕜 E` so that `𝕜` can be determined as an `outParam`
@[nolint unusedArguments]
instance (priority := 75) SubalgebraClass.seminormedRing {S 𝕜 E : Type*} [CommRing 𝕜]
    [SeminormedRing E] [Algebra 𝕜 E] [SetLike S E] [SubringClass S E] [SMulMemClass S 𝕜 E]
    (s : S) : SeminormedRing s :=
  { AddSubgroupClass.seminormedAddCommGroup s, SubringClass.toRing s with
    norm_mul := fun a b => norm_mul_le a.1 b.1 }

/-- A subalgebra of a normed ring is also a normed ring, with the restriction of the norm. -/
instance Subalgebra.normedRing {𝕜 : Type*} [CommRing 𝕜] {E : Type*} [NormedRing E]
    [Algebra 𝕜 E] (s : Subalgebra 𝕜 E) : NormedRing s :=
  { s.seminormedRing with
    eq_of_dist_eq_zero := eq_of_dist_eq_zero }

/-- A subalgebra of a normed ring is also a normed ring, with the restriction of the
norm. -/
instance (priority := 75) SubalgebraClass.normedRing {S 𝕜 E : Type*} [CommRing 𝕜]
    [NormedRing E] [Algebra 𝕜 E] [SetLike S E] [SubringClass S E] [SMulMemClass S 𝕜 E]
    (s : S) : NormedRing s :=
  { seminormedRing s with
    eq_of_dist_eq_zero := eq_of_dist_eq_zero }

theorem Nat.norm_cast_le : ∀ n : ℕ, ‖(n : α)‖ ≤ n * ‖(1 : α)‖
  | 0 => by simp
  | n + 1 => by
    rw [n.cast_succ, n.cast_succ, add_mul, one_mul]
    exact norm_add_le_of_le (Nat.norm_cast_le n) le_rfl

theorem List.norm_prod_le' : ∀ {l : List α}, l ≠ [] → ‖l.prod‖ ≤ (l.map norm).prod
  | [], h => (h rfl).elim
  | [a], _ => by simp
  | a::b::l, _ => by
    rw [List.map_cons, List.prod_cons, @List.prod_cons _ _ _ ‖a‖]
    refine le_trans (norm_mul_le _ _) (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
    exact List.norm_prod_le' (List.cons_ne_nil b l)

theorem List.nnnorm_prod_le' {l : List α} (hl : l ≠ []) : ‖l.prod‖₊ ≤ (l.map nnnorm).prod :=
  (List.norm_prod_le' hl).trans_eq <| by simp [NNReal.coe_list_prod, List.map_map]

theorem List.norm_prod_le [NormOneClass α] : ∀ l : List α, ‖l.prod‖ ≤ (l.map norm).prod
  | [] => by simp
  | a::l => List.norm_prod_le' (List.cons_ne_nil a l)

theorem List.nnnorm_prod_le [NormOneClass α] (l : List α) : ‖l.prod‖₊ ≤ (l.map nnnorm).prod :=
  l.norm_prod_le.trans_eq <| by simp [NNReal.coe_list_prod, List.map_map]

theorem Finset.norm_prod_le' {α : Type*} [NormedCommRing α] (s : Finset ι) (hs : s.Nonempty)
    (f : ι → α) : ‖∏ i ∈ s, f i‖ ≤ ∏ i ∈ s, ‖f i‖ := by
  rcases s with ⟨⟨l⟩, hl⟩
  have : l.map f ≠ []
  simpa using hs
  simpa using List.norm_prod_le' this

theorem Finset.nnnorm_prod_le' {α : Type*} [NormedCommRing α] (s : Finset ι) (hs : s.Nonempty)
    (f : ι → α) : ‖∏ i ∈ s, f i‖₊ ≤ ∏ i ∈ s, ‖f i‖₊ :=
  (s.norm_prod_le' hs f).trans_eq <| by simp [NNReal.coe_prod]

theorem Finset.norm_prod_le {α : Type*} [NormedCommRing α] [NormOneClass α] (s : Finset ι)
    (f : ι → α) : ‖∏ i ∈ s, f i‖ ≤ ∏ i ∈ s, ‖f i‖ := by
  rcases s with ⟨⟨l⟩, hl⟩
  simpa using (l.map f).norm_prod_le

theorem Finset.nnnorm_prod_le {α : Type*} [NormedCommRing α] [NormOneClass α] (s : Finset ι)
    (f : ι → α) : ‖∏ i ∈ s, f i‖₊ ≤ ∏ i ∈ s, ‖f i‖₊ :=
  (s.norm_prod_le f).trans_eq <| by simp [NNReal.coe_prod]

/-- If `α` is a seminormed ring, then `‖a ^ n‖₊ ≤ ‖a‖₊ ^ n` for `n > 0`.
See also `nnnorm_pow_le`. -/
theorem nnnorm_pow_le' (a : α) : ∀ {n : ℕ}, 0 < n → ‖a ^ n‖₊ ≤ ‖a‖₊ ^ n
  | 1, _ => by simp only [pow_one, le_rfl]
  | n + 2, _ => by
    simpa only [pow_succ' _ (n + 1)] using
      le_trans (nnnorm_mul_le _ _) (mul_le_mul_left' (nnnorm_pow_le' a n.succ_pos) _)

/-- If `α` is a seminormed ring with `‖1‖₊ = 1`, then `‖a ^ n‖₊ ≤ ‖a‖₊ ^ n`.
See also `nnnorm_pow_le'`. -/
theorem nnnorm_pow_le [NormOneClass α] (a : α) (n : ℕ) : ‖a ^ n‖₊ ≤ ‖a‖₊ ^ n :=
  Nat.recOn n (by simp only [Nat.zero_eq, pow_zero, nnnorm_one, le_rfl])
    fun k _hk => nnnorm_pow_le' a k.succ_pos

/-- If `α` is a seminormed ring, then `‖a ^ n‖ ≤ ‖a‖ ^ n` for `n > 0`. See also `norm_pow_le`. -/
theorem norm_pow_le' (a : α) {n : ℕ} (h : 0 < n) : ‖a ^ n‖ ≤ ‖a‖ ^ n := by
  simpa only [NNReal.coe_pow, coe_nnnorm] using NNReal.coe_mono (nnnorm_pow_le' a h)

/-- If `α` is a seminormed ring with `‖1‖ = 1`, then `‖a ^ n‖ ≤ ‖a‖ ^ n`.
See also `norm_pow_le'`. -/
theorem norm_pow_le [NormOneClass α] (a : α) (n : ℕ) : ‖a ^ n‖ ≤ ‖a‖ ^ n :=
  Nat.recOn n (by simp only [Nat.zero_eq, pow_zero, norm_one, le_rfl])
    fun n _hn => norm_pow_le' a n.succ_pos

theorem eventually_norm_pow_le (a : α) : ∀ᶠ n : ℕ in atTop, ‖a ^ n‖ ≤ ‖a‖ ^ n :=
  eventually_atTop.mpr ⟨1, fun _b h => norm_pow_le' a (Nat.succ_le_iff.mp h)⟩

instance ULift.seminormedRing : SeminormedRing (ULift α) :=
  { ULift.nonUnitalSeminormedRing, ULift.ring with }

/-- Seminormed ring structure on the product of two seminormed rings,
  using the sup norm. -/
instance Prod.seminormedRing [SeminormedRing β] : SeminormedRing (α × β) :=
  { nonUnitalSeminormedRing, instRing with }

/-- Seminormed ring structure on the product of finitely many seminormed rings,
  using the sup norm. -/
instance Pi.seminormedRing {π : ι → Type*} [Fintype ι] [∀ i, SeminormedRing (π i)] :
    SeminormedRing (∀ i, π i) :=
  { Pi.nonUnitalSeminormedRing, Pi.ring with }

instance MulOpposite.instSeminormedRing : SeminormedRing αᵐᵒᵖ where
  __ := instRing
  __ := instNonUnitalSeminormedRing

end SeminormedRing

section NonUnitalNormedRing

variable [NonUnitalNormedRing α]

instance ULift.nonUnitalNormedRing : NonUnitalNormedRing (ULift α) :=
  { ULift.nonUnitalSeminormedRing, ULift.normedAddCommGroup with }

/-- Non-unital normed ring structure on the product of two non-unital normed rings,
using the sup norm. -/
instance Prod.nonUnitalNormedRing [NonUnitalNormedRing β] : NonUnitalNormedRing (α × β) :=
  { Prod.nonUnitalSeminormedRing, Prod.normedAddCommGroup with }

/-- Normed ring structure on the product of finitely many non-unital normed rings, using the sup
norm. -/
instance Pi.nonUnitalNormedRing {π : ι → Type*} [Fintype ι] [∀ i, NonUnitalNormedRing (π i)] :
    NonUnitalNormedRing (∀ i, π i) :=
  { Pi.nonUnitalSeminormedRing, Pi.normedAddCommGroup with }

instance MulOpposite.instNonUnitalNormedRing : NonUnitalNormedRing αᵐᵒᵖ where
  __ := instNonUnitalRing
  __ := instNonUnitalSeminormedRing
  __ := instNormedAddCommGroup

end NonUnitalNormedRing

section NormedRing

variable [NormedRing α]

theorem Units.norm_pos [Nontrivial α] (x : αˣ) : 0 < ‖(x : α)‖ :=
  norm_pos_iff.mpr (Units.ne_zero x)

theorem Units.nnnorm_pos [Nontrivial α] (x : αˣ) : 0 < ‖(x : α)‖₊ :=
  x.norm_pos

instance ULift.normedRing : NormedRing (ULift α) :=
  { ULift.seminormedRing, ULift.normedAddCommGroup with }

/-- Normed ring structure on the product of two normed rings, using the sup norm. -/
instance Prod.normedRing [NormedRing β] : NormedRing (α × β) :=
  { nonUnitalNormedRing, instRing with }

/-- Normed ring structure on the product of finitely many normed rings, using the sup norm. -/
instance Pi.normedRing {π : ι → Type*} [Fintype ι] [∀ i, NormedRing (π i)] :
    NormedRing (∀ i, π i) :=
  { Pi.seminormedRing, Pi.normedAddCommGroup with }

instance MulOpposite.instNormedRing : NormedRing αᵐᵒᵖ where
  __ := instRing
  __ := instSeminormedRing
  __ := instNormedAddCommGroup

end NormedRing

section NonUnitalSeminormedCommRing

variable [NonUnitalSeminormedCommRing α]

instance ULift.nonUnitalSeminormedCommRing : NonUnitalSeminormedCommRing (ULift α) :=
  { ULift.nonUnitalSeminormedRing, ULift.nonUnitalCommRing with }

/-- Non-unital seminormed commutative ring structure on the product of two non-unital seminormed
commutative rings, using the sup norm. -/
instance Prod.nonUnitalSeminormedCommRing [NonUnitalSeminormedCommRing β] :
    NonUnitalSeminormedCommRing (α × β) :=
  { nonUnitalSeminormedRing, instNonUnitalCommRing with }

/-- Non-unital seminormed commutative ring structure on the product of finitely many non-unital
seminormed commutative rings, using the sup norm. -/
instance Pi.nonUnitalSeminormedCommRing {π : ι → Type*} [Fintype ι]
    [∀ i, NonUnitalSeminormedCommRing (π i)] : NonUnitalSeminormedCommRing (∀ i, π i) :=
  { Pi.nonUnitalSeminormedRing, Pi.nonUnitalCommRing with }

instance MulOpposite.instNonUnitalSeminormedCommRing : NonUnitalSeminormedCommRing αᵐᵒᵖ where
  __ := instNonUnitalSeminormedRing
  __ := instNonUnitalCommRing

end NonUnitalSeminormedCommRing

section NonUnitalNormedCommRing

variable [NonUnitalNormedCommRing α]

/-- A non-unital subalgebra of a non-unital seminormed commutative ring is also a non-unital
seminormed commutative ring, with the restriction of the norm.  -/
instance NonUnitalSubalgebra.nonUnitalSeminormedCommRing {𝕜 : Type*} [CommRing 𝕜] {E : Type*}
    [NonUnitalSeminormedCommRing E] [Module 𝕜 E] (s : NonUnitalSubalgebra 𝕜 E) :
    NonUnitalSeminormedCommRing s :=
  { s.nonUnitalSeminormedRing, s.toNonUnitalCommRing with }

/-- A non-unital subalgebra of a non-unital normed commutative ring is also a non-unital normed
commutative ring, with the restriction of the norm.  -/
instance NonUnitalSubalgebra.nonUnitalNormedCommRing {𝕜 : Type*} [CommRing 𝕜] {E : Type*}
    [NonUnitalNormedCommRing E] [Module 𝕜 E] (s : NonUnitalSubalgebra 𝕜 E) :
    NonUnitalNormedCommRing s :=
  { s.nonUnitalSeminormedCommRing, s.nonUnitalNormedRing with }

instance ULift.nonUnitalNormedCommRing : NonUnitalNormedCommRing (ULift α) :=
  { ULift.nonUnitalSeminormedCommRing, ULift.normedAddCommGroup with }

/-- Non-unital normed commutative ring structure on the product of two non-unital normed
commutative rings, using the sup norm. -/
instance Prod.nonUnitalNormedCommRing [NonUnitalNormedCommRing β] :
    NonUnitalNormedCommRing (α × β) :=
  { Prod.nonUnitalSeminormedCommRing, Prod.normedAddCommGroup with }

/-- Normed commutative ring structure on the product of finitely many non-unital normed
commutative rings, using the sup norm. -/
instance Pi.nonUnitalNormedCommRing {π : ι → Type*} [Fintype ι]
    [∀ i, NonUnitalNormedCommRing (π i)] : NonUnitalNormedCommRing (∀ i, π i) :=
  { Pi.nonUnitalSeminormedCommRing, Pi.normedAddCommGroup with }

instance MulOpposite.instNonUnitalNormedCommRing : NonUnitalNormedCommRing αᵐᵒᵖ where
  __ := instNonUnitalNormedRing
  __ := instNonUnitalSeminormedCommRing

end NonUnitalNormedCommRing

section SeminormedCommRing

variable [SeminormedCommRing α]

instance ULift.seminormedCommRing : SeminormedCommRing (ULift α) :=
  { ULift.nonUnitalSeminormedRing, ULift.commRing with }

/-- Seminormed commutative ring structure on the product of two seminormed commutative rings,
  using the sup norm. -/
instance Prod.seminormedCommRing [SeminormedCommRing β] : SeminormedCommRing (α × β) :=
  { Prod.nonUnitalSeminormedCommRing, instCommRing with }

/-- Seminormed commutative ring structure on the product of finitely many seminormed commutative
rings, using the sup norm. -/
instance Pi.seminormedCommRing {π : ι → Type*} [Fintype ι] [∀ i, SeminormedCommRing (π i)] :
    SeminormedCommRing (∀ i, π i) :=
  { Pi.nonUnitalSeminormedCommRing, Pi.ring with }

instance MulOpposite.instSeminormedCommRing : SeminormedCommRing αᵐᵒᵖ where
  __ := instSeminormedRing
  __ := instNonUnitalSeminormedCommRing

end SeminormedCommRing

section NormedCommRing

/-- A subalgebra of a seminormed commutative ring is also a seminormed commutative ring, with the
restriction of the norm.  -/
instance Subalgebra.seminormedCommRing {𝕜 : Type*} [CommRing 𝕜] {E : Type*} [SeminormedCommRing E]
    [Algebra 𝕜 E] (s : Subalgebra 𝕜 E) : SeminormedCommRing s :=
  { s.seminormedRing, s.toCommRing with }

/-- A subalgebra of a normed commutative ring is also a normed commutative ring, with the
restriction of the norm.  -/
instance Subalgebra.normedCommRing {𝕜 : Type*} [CommRing 𝕜] {E : Type*} [NormedCommRing E]
    [Algebra 𝕜 E] (s : Subalgebra 𝕜 E) : NormedCommRing s :=
  { s.seminormedCommRing, s.normedRing with }

variable [NormedCommRing α]

instance ULift.normedCommRing : NormedCommRing (ULift α) :=
  { ULift.normedRing (α := α), ULift.seminormedCommRing with }

/-- Normed commutative ring structure on the product of two normed commutative rings, using the sup
norm. -/
instance Prod.normedCommRing [NormedCommRing β] : NormedCommRing (α × β) :=
  { nonUnitalNormedRing, instCommRing with }

/-- Normed commutative ring structure on the product of finitely many normed commutative rings,
using the sup norm. -/
instance Pi.normedCommutativeRing {π : ι → Type*} [Fintype ι] [∀ i, NormedCommRing (π i)] :
    NormedCommRing (∀ i, π i) :=
  { Pi.seminormedCommRing, Pi.normedAddCommGroup with }

instance MulOpposite.instNormedCommRing : NormedCommRing αᵐᵒᵖ where
  __ := instNormedRing
  __ := instSeminormedCommRing

end NormedCommRing

-- see Note [lower instance priority]
instance (priority := 100) semi_normed_ring_top_monoid [NonUnitalSeminormedRing α] :
    ContinuousMul α :=
  ⟨continuous_iff_continuousAt.2 fun x =>
      tendsto_iff_norm_sub_tendsto_zero.2 <| by
        have : ∀ e : α × α,
            ‖e.1 * e.2 - x.1 * x.2‖ ≤ ‖e.1‖ * ‖e.2 - x.2‖ + ‖e.1 - x.1‖ * ‖x.2‖ := by
          intro e
          calc
            ‖e.1 * e.2 - x.1 * x.2‖ ≤ ‖e.1 * (e.2 - x.2) + (e.1 - x.1) * x.2‖ := by
              rw [_root_.mul_sub, _root_.sub_mul, sub_add_sub_cancel]
            -- Porting note: `ENNReal.{mul_sub, sub_mul}` should be protected
            _ ≤ ‖e.1‖ * ‖e.2 - x.2‖ + ‖e.1 - x.1‖ * ‖x.2‖ :=
              norm_add_le_of_le (norm_mul_le _ _) (norm_mul_le _ _)
        refine squeeze_zero (fun e => norm_nonneg _) this ?_
        convert
          ((continuous_fst.tendsto x).norm.mul
                ((continuous_snd.tendsto x).sub tendsto_const_nhds).norm).add
            (((continuous_fst.tendsto x).sub tendsto_const_nhds).norm.mul _)
        -- Porting note: `show` used to select a goal to work on
        rotate_right
        show Tendsto _ _ _
        exact tendsto_const_nhds
        simp⟩

-- see Note [lower instance priority]
/-- A seminormed ring is a topological ring. -/
instance (priority := 100) semi_normed_top_ring [NonUnitalSeminormedRing α] :
    TopologicalRing α where

section NormedDivisionRing

variable [NormedDivisionRing α] {a : α}

@[simp]
theorem norm_mul (a b : α) : ‖a * b‖ = ‖a‖ * ‖b‖ :=
  NormedDivisionRing.norm_mul' a b

instance (priority := 900) NormedDivisionRing.to_normOneClass : NormOneClass α :=
  ⟨mul_left_cancel₀ (mt norm_eq_zero.1 (one_ne_zero' α)) <| by rw [← norm_mul, mul_one, mul_one]⟩

instance isAbsoluteValue_norm : IsAbsoluteValue (norm : α → ℝ) where
  abv_nonneg' := norm_nonneg
  abv_eq_zero' := norm_eq_zero
  abv_add' := norm_add_le
  abv_mul' := norm_mul

@[simp]
theorem nnnorm_mul (a b : α) : ‖a * b‖₊ = ‖a‖₊ * ‖b‖₊ :=
  NNReal.eq <| norm_mul a b

/-- `norm` as a `MonoidWithZeroHom`. -/
@[simps]
def normHom : α →*₀ ℝ where
  toFun := (‖·‖)
  map_zero' := norm_zero
  map_one' := norm_one
  map_mul' := norm_mul

/-- `nnnorm` as a `MonoidWithZeroHom`. -/
@[simps]
def nnnormHom : α →*₀ ℝ≥0 where
  toFun := (‖·‖₊)
  map_zero' := nnnorm_zero
  map_one' := nnnorm_one
  map_mul' := nnnorm_mul

@[simp]
theorem norm_pow (a : α) : ∀ n : ℕ, ‖a ^ n‖ = ‖a‖ ^ n :=
  (normHom.toMonoidHom : α →* ℝ).map_pow a

@[simp]
theorem nnnorm_pow (a : α) (n : ℕ) : ‖a ^ n‖₊ = ‖a‖₊ ^ n :=
  (nnnormHom.toMonoidHom : α →* ℝ≥0).map_pow a n

protected theorem List.norm_prod (l : List α) : ‖l.prod‖ = (l.map norm).prod :=
  map_list_prod (normHom.toMonoidHom : α →* ℝ) _

protected theorem List.nnnorm_prod (l : List α) : ‖l.prod‖₊ = (l.map nnnorm).prod :=
  map_list_prod (nnnormHom.toMonoidHom : α →* ℝ≥0) _

@[simp]
theorem norm_div (a b : α) : ‖a / b‖ = ‖a‖ / ‖b‖ :=
  map_div₀ (normHom : α →*₀ ℝ) a b

@[simp]
theorem nnnorm_div (a b : α) : ‖a / b‖₊ = ‖a‖₊ / ‖b‖₊ :=
  map_div₀ (nnnormHom : α →*₀ ℝ≥0) a b

@[simp]
theorem norm_inv (a : α) : ‖a⁻¹‖ = ‖a‖⁻¹ :=
  map_inv₀ (normHom : α →*₀ ℝ) a

@[simp]
theorem nnnorm_inv (a : α) : ‖a⁻¹‖₊ = ‖a‖₊⁻¹ :=
  NNReal.eq <| by simp

@[simp]
theorem norm_zpow : ∀ (a : α) (n : ℤ), ‖a ^ n‖ = ‖a‖ ^ n :=
  map_zpow₀ (normHom : α →*₀ ℝ)

@[simp]
theorem nnnorm_zpow : ∀ (a : α) (n : ℤ), ‖a ^ n‖₊ = ‖a‖₊ ^ n :=
  map_zpow₀ (nnnormHom : α →*₀ ℝ≥0)

theorem dist_inv_inv₀ {z w : α} (hz : z ≠ 0) (hw : w ≠ 0) :
    dist z⁻¹ w⁻¹ = dist z w / (‖z‖ * ‖w‖) := by
  rw [dist_eq_norm, inv_sub_inv' hz hw, norm_mul, norm_mul, norm_inv, norm_inv, mul_comm ‖z‖⁻¹,
    mul_assoc, dist_eq_norm', div_eq_mul_inv, mul_inv]

theorem nndist_inv_inv₀ {z w : α} (hz : z ≠ 0) (hw : w ≠ 0) :
    nndist z⁻¹ w⁻¹ = nndist z w / (‖z‖₊ * ‖w‖₊) :=
  NNReal.eq <| dist_inv_inv₀ hz hw

lemma antilipschitzWith_mul_left {a : α} (ha : a ≠ 0) : AntilipschitzWith (‖a‖₊⁻¹) (a * ·) :=
  AntilipschitzWith.of_le_mul_dist fun _ _ ↦ by simp [dist_eq_norm, ← _root_.mul_sub, ha]

lemma antilipschitzWith_mul_right {a : α} (ha : a ≠ 0) : AntilipschitzWith (‖a‖₊⁻¹) (· * a) :=
  AntilipschitzWith.of_le_mul_dist fun _ _ ↦ by
    simp [dist_eq_norm, ← _root_.sub_mul, ← mul_comm (‖a‖), ha]

/-- Multiplication by a nonzero element `a` on the left
as a `DilationEquiv` of a normed division ring. -/
@[simps!]
def DilationEquiv.mulLeft (a : α) (ha : a ≠ 0) : α ≃ᵈ α where
  toEquiv := Equiv.mulLeft₀ a ha
  edist_eq' := ⟨‖a‖₊, nnnorm_ne_zero_iff.2 ha, fun x y ↦ by
    simp [edist_nndist, nndist_eq_nnnorm, ← mul_sub]⟩

/-- Multiplication by a nonzero element `a` on the right
as a `DilationEquiv` of a normed division ring. -/
@[simps!]
def DilationEquiv.mulRight (a : α) (ha : a ≠ 0) : α ≃ᵈ α where
  toEquiv := Equiv.mulRight₀ a ha
  edist_eq' := ⟨‖a‖₊, nnnorm_ne_zero_iff.2 ha, fun x y ↦ by
    simp [edist_nndist, nndist_eq_nnnorm, ← sub_mul, ← mul_comm (‖a‖₊)]⟩

namespace Filter

@[simp]
lemma comap_mul_left_cobounded {a : α} (ha : a ≠ 0) :
    comap (a * ·) (cobounded α) = cobounded α :=
  Dilation.comap_cobounded (DilationEquiv.mulLeft a ha)

@[simp]
lemma map_mul_left_cobounded {a : α} (ha : a ≠ 0) :
    map (a * ·) (cobounded α) = cobounded α :=
  DilationEquiv.map_cobounded (DilationEquiv.mulLeft a ha)

@[simp]
lemma comap_mul_right_cobounded {a : α} (ha : a ≠ 0) :
    comap (· * a) (cobounded α) = cobounded α :=
  Dilation.comap_cobounded (DilationEquiv.mulRight a ha)

@[simp]
lemma map_mul_right_cobounded {a : α} (ha : a ≠ 0) :
    map (· * a) (cobounded α) = cobounded α :=
  DilationEquiv.map_cobounded (DilationEquiv.mulRight a ha)

/-- Multiplication on the left by a nonzero element of a normed division ring tends to infinity at
infinity. -/
theorem tendsto_mul_left_cobounded {a : α} (ha : a ≠ 0) :
    Tendsto (a * ·) (cobounded α) (cobounded α) :=
  (map_mul_left_cobounded ha).le

/-- Multiplication on the right by a nonzero element of a normed division ring tends to infinity at
infinity. -/
theorem tendsto_mul_right_cobounded {a : α} (ha : a ≠ 0) :
    Tendsto (· * a) (cobounded α) (cobounded α) :=
  (map_mul_right_cobounded ha).le

@[simp]
lemma inv_cobounded₀ : (cobounded α)⁻¹ = 𝓝[≠] 0 := by
  rw [← comap_norm_atTop, ← Filter.comap_inv, ← comap_norm_nhdsWithin_Ioi_zero,
    ← inv_atTop₀, ← Filter.comap_inv]
  simp only [comap_comap, (· ∘ ·), norm_inv]

@[simp]
lemma inv_nhdsWithin_ne_zero : (𝓝[≠] (0 : α))⁻¹ = cobounded α := by
  rw [← inv_cobounded₀, inv_inv]

lemma tendsto_inv₀_cobounded' : Tendsto Inv.inv (cobounded α) (𝓝[≠] 0) :=
  inv_cobounded₀.le

theorem tendsto_inv₀_cobounded : Tendsto Inv.inv (cobounded α) (𝓝 0) :=
  tendsto_inv₀_cobounded'.mono_right inf_le_left

lemma tendsto_inv₀_nhdsWithin_ne_zero : Tendsto Inv.inv (𝓝[≠] 0) (cobounded α) :=
  inv_nhdsWithin_ne_zero.le

end Filter

-- see Note [lower instance priority]
instance (priority := 100) NormedDivisionRing.to_hasContinuousInv₀ : HasContinuousInv₀ α := by
  refine ⟨fun r r0 => tendsto_iff_norm_sub_tendsto_zero.2 ?_⟩
  have r0' : 0 < ‖r‖ := norm_pos_iff.2 r0
  rcases exists_between r0' with ⟨ε, ε0, εr⟩
  have : ∀ᶠ e in 𝓝 r, ‖e⁻¹ - r⁻¹‖ ≤ ‖r - e‖ / ‖r‖ / ε
  filter_upwards [(isOpen_lt continuous_const continuous_norm).eventually_mem εr] with e he
  have e0 : e ≠ 0 := norm_pos_iff.1 (ε0.trans he)
  calc
    ‖e⁻¹ - r⁻¹‖ = ‖r‖⁻¹ * ‖r - e‖ * ‖e‖⁻¹ := by
      rw [← norm_inv, ← norm_inv, ← norm_mul, ← norm_mul, _root_.mul_sub, _root_.sub_mul,
        mul_assoc _ e, inv_mul_cancel r0, mul_inv_cancel e0, one_mul, mul_one]
    -- Porting note: `ENNReal.{mul_sub, sub_mul}` should be `protected`
    _ = ‖r - e‖ / ‖r‖ / ‖e‖ := by field_simp [mul_comm]
    _ ≤ ‖r - e‖ / ‖r‖ / ε := by gcongr
  refine squeeze_zero' (eventually_of_forall fun _ => norm_nonneg _) this ?_
  refine (((continuous_const.sub continuous_id).norm.div_const _).div_const _).tendsto' _ _ ?_
  simp

-- see Note [lower instance priority]
/-- A normed division ring is a topological division ring. -/
instance (priority := 100) NormedDivisionRing.to_topologicalDivisionRing :
    TopologicalDivisionRing α where

protected lemma IsOfFinOrder.norm_eq_one (ha : IsOfFinOrder a) : ‖a‖ = 1 :=
  ((normHom : α →*₀ ℝ).toMonoidHom.isOfFinOrder ha).eq_one $ norm_nonneg _

example [Monoid β] (φ : β →* α) {x : β} {k : ℕ+} (h : x ^ (k : ℕ) = 1) :
    ‖φ x‖ = 1 := (φ.isOfFinOrder <| isOfFinOrder_iff_pow_eq_one.2 ⟨_, k.2, h⟩).norm_eq_one

end NormedDivisionRing

/-- A normed field is a field with a norm satisfying ‖x y‖ = ‖x‖ ‖y‖. -/
class NormedField (α : Type*) extends Norm α, Field α, MetricSpace α where
  /-- The distance is induced by the norm. -/
  dist_eq : ∀ x y, dist x y = norm (x - y)
  /-- The norm is multiplicative. -/
  norm_mul' : ∀ a b, norm (a * b) = norm a * norm b

/-- A nontrivially normed field is a normed field in which there is an element of norm different
from `0` and `1`. This makes it possible to bring any element arbitrarily close to `0` by
multiplication by the powers of any element, and thus to relate algebra and topology. -/
class NontriviallyNormedField (α : Type*) extends NormedField α where
  /-- The norm attains a value exceeding 1. -/
  non_trivial : ∃ x : α, 1 < ‖x‖

/-- A densely normed field is a normed field for which the image of the norm is dense in `ℝ≥0`,
which means it is also nontrivially normed. However, not all nontrivally normed fields are densely
normed; in particular, the `Padic`s exhibit this fact. -/
class DenselyNormedField (α : Type*) extends NormedField α where
  /-- The range of the norm is dense in the collection of nonnegative real numbers. -/
  lt_norm_lt : ∀ x y : ℝ, 0 ≤ x → x < y → ∃ a : α, x < ‖a‖ ∧ ‖a‖ < y

section NormedField

/-- A densely normed field is always a nontrivially normed field.
See note [lower instance priority]. -/
instance (priority := 100) DenselyNormedField.toNontriviallyNormedField [DenselyNormedField α] :
    NontriviallyNormedField α where
  non_trivial :=
    let ⟨a, h, _⟩ := DenselyNormedField.lt_norm_lt 1 2 zero_le_one one_lt_two
    ⟨a, h⟩

variable [NormedField α]

-- see Note [lower instance priority]
instance (priority := 100) NormedField.toNormedDivisionRing : NormedDivisionRing α :=
  { ‹NormedField α› with }

-- see Note [lower instance priority]
instance (priority := 100) NormedField.toNormedCommRing : NormedCommRing α :=
  { ‹NormedField α› with norm_mul := fun a b => (norm_mul a b).le }

@[simp]
theorem norm_prod (s : Finset β) (f : β → α) : ‖∏ b ∈ s, f b‖ = ∏ b ∈ s, ‖f b‖ :=
  map_prod normHom.toMonoidHom f s

@[simp]
theorem nnnorm_prod (s : Finset β) (f : β → α) : ‖∏ b ∈ s, f b‖₊ = ∏ b ∈ s, ‖f b‖₊ :=
  map_prod nnnormHom.toMonoidHom f s

end NormedField

namespace NormedField

section Nontrivially

variable (α) [NontriviallyNormedField α]

theorem exists_one_lt_norm : ∃ x : α, 1 < ‖x‖ :=
  ‹NontriviallyNormedField α›.non_trivial

theorem exists_lt_norm (r : ℝ) : ∃ x : α, r < ‖x‖ :=
  let ⟨w, hw⟩ := exists_one_lt_norm α
  let ⟨n, hn⟩ := pow_unbounded_of_one_lt r hw
  ⟨w ^ n, by rwa [norm_pow]⟩

theorem exists_norm_lt {r : ℝ} (hr : 0 < r) : ∃ x : α, 0 < ‖x‖ ∧ ‖x‖ < r :=
  let ⟨w, hw⟩ := exists_lt_norm α r⁻¹
  ⟨w⁻¹, by rwa [← Set.mem_Ioo, norm_inv, ← Set.mem_inv, Set.inv_Ioo_0_left hr]⟩

theorem exists_norm_lt_one : ∃ x : α, 0 < ‖x‖ ∧ ‖x‖ < 1 :=
  exists_norm_lt α one_pos

variable {α}

@[instance]
theorem punctured_nhds_neBot (x : α) : NeBot (𝓝[≠] x) := by
  rw [← mem_closure_iff_nhdsWithin_neBot, Metric.mem_closure_iff]
  rintro ε ε0
  rcases exists_norm_lt α ε0 with ⟨b, hb0, hbε⟩
  refine ⟨x + b, mt (Set.mem_singleton_iff.trans add_right_eq_self).1 <| norm_pos_iff.1 hb0, ?_⟩
  rwa [dist_comm, dist_eq_norm, add_sub_cancel_left]

@[instance]
theorem nhdsWithin_isUnit_neBot : NeBot (𝓝[{ x : α | IsUnit x }] 0) := by
  simpa only [isUnit_iff_ne_zero] using punctured_nhds_neBot (0 : α)

end Nontrivially

section Densely

variable (α) [DenselyNormedField α]

theorem exists_lt_norm_lt {r₁ r₂ : ℝ} (h₀ : 0 ≤ r₁) (h : r₁ < r₂) : ∃ x : α, r₁ < ‖x‖ ∧ ‖x‖ < r₂ :=
  DenselyNormedField.lt_norm_lt r₁ r₂ h₀ h

theorem exists_lt_nnnorm_lt {r₁ r₂ : ℝ≥0} (h : r₁ < r₂) : ∃ x : α, r₁ < ‖x‖₊ ∧ ‖x‖₊ < r₂ :=
  mod_cast exists_lt_norm_lt α r₁.prop h

instance denselyOrdered_range_norm : DenselyOrdered (Set.range (norm : α → ℝ)) where
  dense := by
    rintro ⟨-, x, rfl⟩ ⟨-, y, rfl⟩ hxy
    let ⟨z, h⟩ := exists_lt_norm_lt α (norm_nonneg _) hxy
    exact ⟨⟨‖z‖, z, rfl⟩, h⟩

instance denselyOrdered_range_nnnorm : DenselyOrdered (Set.range (nnnorm : α → ℝ≥0)) where
  dense := by
    rintro ⟨-, x, rfl⟩ ⟨-, y, rfl⟩ hxy
    let ⟨z, h⟩ := exists_lt_nnnorm_lt α hxy
    exact ⟨⟨‖z‖₊, z, rfl⟩, h⟩

theorem denseRange_nnnorm : DenseRange (nnnorm : α → ℝ≥0) :=
  dense_of_exists_between fun _ _ hr =>
    let ⟨x, h⟩ := exists_lt_nnnorm_lt α hr
    ⟨‖x‖₊, ⟨x, rfl⟩, h⟩

end Densely

end NormedField

/-- A normed field is nontrivially normed
provided that the norm of some nonzero element is not one. -/
def NontriviallyNormedField.ofNormNeOne {𝕜 : Type*} [h' : NormedField 𝕜]
    (h : ∃ x : 𝕜, x ≠ 0 ∧ ‖x‖ ≠ 1) : NontriviallyNormedField 𝕜 where
  toNormedField := h'
  non_trivial := by
    rcases h with ⟨x, hx, hx1⟩
    rcases hx1.lt_or_lt with hlt | hlt
    · use x⁻¹
      rw [norm_inv]
      exact one_lt_inv (norm_pos_iff.2 hx) hlt
    · exact ⟨x, hlt⟩

instance Real.normedCommRing : NormedCommRing ℝ :=
  { Real.normedAddCommGroup, Real.commRing with norm_mul := fun x y => (abs_mul x y).le }

noncomputable instance Real.normedField : NormedField ℝ :=
  { Real.normedAddCommGroup, Real.field with
    norm_mul' := abs_mul }

noncomputable instance Real.denselyNormedField : DenselyNormedField ℝ where
  lt_norm_lt _ _ h₀ hr :=
    let ⟨x, h⟩ := exists_between hr
    ⟨x, by rwa [Real.norm_eq_abs, abs_of_nonneg (h₀.trans h.1.le)]⟩

namespace Real

theorem toNNReal_mul_nnnorm {x : ℝ} (y : ℝ) (hx : 0 ≤ x) : x.toNNReal * ‖y‖₊ = ‖x * y‖₊ := by
  ext
  simp only [NNReal.coe_mul, nnnorm_mul, coe_nnnorm, Real.toNNReal_of_nonneg, norm_of_nonneg, hx,
    NNReal.coe_mk]

theorem nnnorm_mul_toNNReal (x : ℝ) {y : ℝ} (hy : 0 ≤ y) : ‖x‖₊ * y.toNNReal = ‖x * y‖₊ := by
  rw [mul_comm, mul_comm x, toNNReal_mul_nnnorm x hy]

end Real

namespace NNReal

open NNReal

-- porting note (#10618): removed `@[simp]` because `simp` can prove this
theorem norm_eq (x : ℝ≥0) : ‖(x : ℝ)‖ = x := by rw [Real.norm_eq_abs, x.abs_eq]

@[simp]
theorem nnnorm_eq (x : ℝ≥0) : ‖(x : ℝ)‖₊ = x :=
  NNReal.eq <| Real.norm_of_nonneg x.2

lemma lipschitzWith_sub : LipschitzWith 2 (fun (p : ℝ≥0 × ℝ≥0) ↦ p.1 - p.2) := by
  rw [← isometry_subtype_coe.lipschitzWith_iff]
  have : Isometry (Prod.map ((↑) : ℝ≥0 → ℝ) ((↑) : ℝ≥0 → ℝ)) :=
    isometry_subtype_coe.prod_map isometry_subtype_coe
  convert (((LipschitzWith.prod_fst.comp this.lipschitz).sub
    (LipschitzWith.prod_snd.comp this.lipschitz)).max_const 0)
  norm_num

end NNReal

@[simp 1001] -- Porting note: increase priority so that the LHS doesn't simplify
theorem norm_norm [SeminormedAddCommGroup α] (x : α) : ‖‖x‖‖ = ‖x‖ :=
  Real.norm_of_nonneg (norm_nonneg _)

@[simp]
theorem nnnorm_norm [SeminormedAddCommGroup α] (a : α) : ‖‖a‖‖₊ = ‖a‖₊ := by
  rw [Real.nnnorm_of_nonneg (norm_nonneg a)]; rfl

/-- A restatement of `MetricSpace.tendsto_atTop` in terms of the norm. -/
theorem NormedAddCommGroup.tendsto_atTop [Nonempty α] [SemilatticeSup α] {β : Type*}
    [SeminormedAddCommGroup β] {f : α → β} {b : β} :
    Tendsto f atTop (𝓝 b) ↔ ∀ ε, 0 < ε → ∃ N, ∀ n, N ≤ n → ‖f n - b‖ < ε :=
  (atTop_basis.tendsto_iff Metric.nhds_basis_ball).trans (by simp [dist_eq_norm])

/-- A variant of `NormedAddCommGroup.tendsto_atTop` that
uses `∃ N, ∀ n > N, ...` rather than `∃ N, ∀ n ≥ N, ...`
-/
theorem NormedAddCommGroup.tendsto_atTop' [Nonempty α] [SemilatticeSup α] [NoMaxOrder α]
    {β : Type*} [SeminormedAddCommGroup β] {f : α → β} {b : β} :
    Tendsto f atTop (𝓝 b) ↔ ∀ ε, 0 < ε → ∃ N, ∀ n, N < n → ‖f n - b‖ < ε :=
  (atTop_basis_Ioi.tendsto_iff Metric.nhds_basis_ball).trans (by simp [dist_eq_norm])

instance Int.instNormedCommRing : NormedCommRing ℤ where
  __ := instCommRing
  __ := instNormedAddCommGroup
  norm_mul m n := by simp only [norm, Int.cast_mul, abs_mul, le_rfl]

instance Int.instNormOneClass : NormOneClass ℤ :=
  ⟨by simp [← Int.norm_cast_real]⟩

instance Rat.instNormedField : NormedField ℚ where
  __ := instField
  __ := instNormedAddCommGroup
  norm_mul' a b := by simp only [norm, Rat.cast_mul, abs_mul]

instance Rat.instDenselyNormedField : DenselyNormedField ℚ where
  lt_norm_lt r₁ r₂ h₀ hr :=
    let ⟨q, h⟩ := exists_rat_btwn hr
    ⟨q, by rwa [← Rat.norm_cast_real, Real.norm_eq_abs, abs_of_pos (h₀.trans_lt h.1)]⟩

section RingHomIsometric

variable {R₁ : Type*} {R₂ : Type*} {R₃ : Type*}

/-- This class states that a ring homomorphism is isometric. This is a sufficient assumption
for a continuous semilinear map to be bounded and this is the main use for this typeclass. -/
class RingHomIsometric [Semiring R₁] [Semiring R₂] [Norm R₁] [Norm R₂] (σ : R₁ →+* R₂) : Prop where
  /-- The ring homomorphism is an isometry. -/
  is_iso : ∀ {x : R₁}, ‖σ x‖ = ‖x‖

attribute [simp] RingHomIsometric.is_iso

variable [SeminormedRing R₁] [SeminormedRing R₂] [SeminormedRing R₃]

instance RingHomIsometric.ids : RingHomIsometric (RingHom.id R₁) :=
  ⟨rfl⟩

end RingHomIsometric

/-! ### Induced normed structures -/


section Induced

variable {F : Type*} (R S : Type*)
variable [FunLike F R S]

/-- A non-unital ring homomorphism from a `NonUnitalRing` to a `NonUnitalSeminormedRing`
induces a `NonUnitalSeminormedRing` structure on the domain.

See note [reducible non-instances] -/
abbrev NonUnitalSeminormedRing.induced [NonUnitalRing R] [NonUnitalSeminormedRing S]
    [NonUnitalRingHomClass F R S] (f : F) : NonUnitalSeminormedRing R :=
  { SeminormedAddCommGroup.induced R S f, ‹NonUnitalRing R› with
    norm_mul := fun x y => by
      show ‖f (x * y)‖ ≤ ‖f x‖ * ‖f y‖
      exact (map_mul f x y).symm ▸ norm_mul_le (f x) (f y) }

/-- An injective non-unital ring homomorphism from a `NonUnitalRing` to a
`NonUnitalNormedRing` induces a `NonUnitalNormedRing` structure on the domain.

See note [reducible non-instances] -/
abbrev NonUnitalNormedRing.induced [NonUnitalRing R] [NonUnitalNormedRing S]
    [NonUnitalRingHomClass F R S] (f : F) (hf : Function.Injective f) : NonUnitalNormedRing R :=
  { NonUnitalSeminormedRing.induced R S f, NormedAddCommGroup.induced R S f hf with }

/-- A non-unital ring homomorphism from a `Ring` to a `SeminormedRing` induces a
`SeminormedRing` structure on the domain.

See note [reducible non-instances] -/
abbrev SeminormedRing.induced [Ring R] [SeminormedRing S] [NonUnitalRingHomClass F R S] (f : F) :
    SeminormedRing R :=
  { NonUnitalSeminormedRing.induced R S f, SeminormedAddCommGroup.induced R S f, ‹Ring R› with }

/-- An injective non-unital ring homomorphism from a `Ring` to a `NormedRing` induces a
`NormedRing` structure on the domain.

See note [reducible non-instances] -/
abbrev NormedRing.induced [Ring R] [NormedRing S] [NonUnitalRingHomClass F R S] (f : F)
    (hf : Function.Injective f) : NormedRing R :=
  { NonUnitalSeminormedRing.induced R S f, NormedAddCommGroup.induced R S f hf, ‹Ring R› with }

/-- A non-unital ring homomorphism from a `NonUnitalCommRing` to a `NonUnitalSeminormedCommRing`
induces a `NonUnitalSeminormedCommRing` structure on the domain.

See note [reducible non-instances] -/
abbrev NonUnitalSeminormedCommRing.induced [NonUnitalCommRing R] [NonUnitalSeminormedCommRing S]
    [NonUnitalRingHomClass F R S] (f : F) : NonUnitalSeminormedCommRing R :=
  { NonUnitalSeminormedRing.induced R S f, ‹NonUnitalCommRing R› with }

/-- An injective non-unital ring homomorphism from a `NonUnitalCommRing` to a
`NonUnitalNormedCommRing` induces a `NonUnitalNormedCommRing` structure on the domain.

See note [reducible non-instances] -/
abbrev NonUnitalNormedCommRing.induced [NonUnitalCommRing R] [NonUnitalNormedCommRing S]
    [NonUnitalRingHomClass F R S] (f : F) (hf : Function.Injective f) : NonUnitalNormedCommRing R :=
  { NonUnitalNormedRing.induced R S f hf, ‹NonUnitalCommRing R› with }
/-- A non-unital ring homomorphism from a `CommRing` to a `SeminormedRing` induces a
`SeminormedCommRing` structure on the domain.

See note [reducible non-instances] -/
abbrev SeminormedCommRing.induced [CommRing R] [SeminormedRing S] [NonUnitalRingHomClass F R S]
    (f : F) : SeminormedCommRing R :=
  { NonUnitalSeminormedRing.induced R S f, SeminormedAddCommGroup.induced R S f, ‹CommRing R› with }

/-- An injective non-unital ring homomorphism from a `CommRing` to a `NormedRing` induces a
`NormedCommRing` structure on the domain.

See note [reducible non-instances] -/
abbrev NormedCommRing.induced [CommRing R] [NormedRing S] [NonUnitalRingHomClass F R S] (f : F)
    (hf : Function.Injective f) : NormedCommRing R :=
  { SeminormedCommRing.induced R S f, NormedAddCommGroup.induced R S f hf with }

/-- An injective non-unital ring homomorphism from a `DivisionRing` to a `NormedRing` induces a
`NormedDivisionRing` structure on the domain.

See note [reducible non-instances] -/
abbrev NormedDivisionRing.induced [DivisionRing R] [NormedDivisionRing S]
    [NonUnitalRingHomClass F R S] (f : F) (hf : Function.Injective f) : NormedDivisionRing R :=
  { NormedAddCommGroup.induced R S f hf, ‹DivisionRing R› with
    norm_mul' := fun x y => by
      show ‖f (x * y)‖ = ‖f x‖ * ‖f y‖
      exact (map_mul f x y).symm ▸ norm_mul (f x) (f y) }

/-- An injective non-unital ring homomorphism from a `Field` to a `NormedRing` induces a
`NormedField` structure on the domain.

See note [reducible non-instances] -/
abbrev NormedField.induced [Field R] [NormedField S] [NonUnitalRingHomClass F R S] (f : F)
    (hf : Function.Injective f) : NormedField R :=
  { NormedDivisionRing.induced R S f hf with
    mul_comm := mul_comm }

/-- A ring homomorphism from a `Ring R` to a `SeminormedRing S` which induces the norm structure
`SeminormedRing.induced` makes `R` satisfy `‖(1 : R)‖ = 1` whenever `‖(1 : S)‖ = 1`. -/
theorem NormOneClass.induced {F : Type*} (R S : Type*) [Ring R] [SeminormedRing S]
    [NormOneClass S] [FunLike F R S] [RingHomClass F R S] (f : F) :
    @NormOneClass R (SeminormedRing.induced R S f).toNorm _ :=
  -- Porting note: is this `let` a bad idea somehow?
  let _ : SeminormedRing R := SeminormedRing.induced R S f
  { norm_one := (congr_arg norm (map_one f)).trans norm_one }

end Induced

namespace SubringClass

variable {S R : Type*} [SetLike S R]

instance toSeminormedRing [SeminormedRing R] [SubringClass S R] (s : S) : SeminormedRing s :=
  SeminormedRing.induced s R (SubringClass.subtype s)

instance toNormedRing [NormedRing R] [SubringClass S R] (s : S) : NormedRing s :=
  NormedRing.induced s R (SubringClass.subtype s) Subtype.val_injective

instance toSeminormedCommRing [SeminormedCommRing R] [_h : SubringClass S R] (s : S) :
    SeminormedCommRing s :=
  { SubringClass.toSeminormedRing s with mul_comm := mul_comm }

instance toNormedCommRing [NormedCommRing R] [SubringClass S R] (s : S) : NormedCommRing s :=
  { SubringClass.toNormedRing s with mul_comm := mul_comm }

end SubringClass

-- Guard against import creep.
assert_not_exists RestrictScalars
