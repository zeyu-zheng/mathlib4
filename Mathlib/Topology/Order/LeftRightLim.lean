import Mathlib.Tactic.Have
/-
Copyright (c) 2022 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.Topology.Order.LeftRight
import Mathlib.Topology.Order.Monotone

/-!
# Left and right limits

We define the (strict) left and right limits of a function.

* `leftLim f x` is the strict left limit of `f` at `x` (using `f x` as a garbage value if `x`
  is isolated to its left).
* `rightLim f x` is the strict right limit of `f` at `x` (using `f x` as a garbage value if `x`
  is isolated to its right).

We develop a comprehensive API for monotone functions. Notably,

* `Monotone.continuousAt_iff_leftLim_eq_rightLim` states that a monotone function is continuous
  at a point if and only if its left and right limits coincide.
* `Monotone.countable_not_continuousAt` asserts that a monotone function taking values in a
  second-countable space has at most countably many discontinuity points.

We also port the API to antitone functions.

## TODO

Prove corresponding stronger results for `StrictMono` and `StrictAnti` functions.
-/


open Set Filter

open Topology

section

variable {α β : Type*} [LinearOrder α] [TopologicalSpace β]

open Classical in
/-- Let `f : α → β` be a function from a linear order `α` to a topological space `β`, and
let `a : α`. The limit strictly to the left of `f` at `a`, denoted with `leftLim f a`, is defined
by using the order topology on `α`. If `a` is isolated to its left or the function has no left
limit, we use `f a` instead to guarantee a good behavior in most cases. -/
noncomputable def Function.leftLim (f : α → β) (a : α) : β := by
  haveI : Nonempty β := ⟨f a⟩
  letI : TopologicalSpace α := Preorder.topology α
  exact if 𝓝[<] a = ⊥ ∨ ¬∃ y, Tendsto f (𝓝[<] a) (𝓝 y) then f a else limUnder (𝓝[<] a) f

/-- Let `f : α → β` be a function from a linear order `α` to a topological space `β`, and
let `a : α`. The limit strictly to the right of `f` at `a`, denoted with `rightLim f a`, is defined
by using the order topology on `α`. If `a` is isolated to its right or the function has no right
limit, , we use `f a` instead to guarantee a good behavior in most cases. -/
noncomputable def Function.rightLim (f : α → β) (a : α) : β :=
  @Function.leftLim αᵒᵈ β _ _ f a

open Function

theorem leftLim_eq_of_tendsto [hα : TopologicalSpace α] [h'α : OrderTopology α] [T2Space β]
    {f : α → β} {a : α} {y : β} (h : 𝓝[<] a ≠ ⊥) (h' : Tendsto f (𝓝[<] a) (𝓝 y)) :
    leftLim f a = y := by
  have h'' : ∃ y, Tendsto f (𝓝[<] a) (𝓝 y) := ⟨y, h'⟩
  rw [h'α.topology_eq_generate_intervals] at h h' h''
  simp only [leftLim, h, h'', not_true, or_self_iff, if_false]
  haveI := neBot_iff.2 h
  exact lim_eq h'

theorem leftLim_eq_of_eq_bot [hα : TopologicalSpace α] [h'α : OrderTopology α] (f : α → β) {a : α}
    (h : 𝓝[<] a = ⊥) : leftLim f a = f a := by
  rw [h'α.topology_eq_generate_intervals] at h
  simp [leftLim, ite_eq_left_iff, h]

theorem rightLim_eq_of_tendsto [TopologicalSpace α] [OrderTopology α] [T2Space β]
    {f : α → β} {a : α} {y : β} (h : 𝓝[>] a ≠ ⊥) (h' : Tendsto f (𝓝[>] a) (𝓝 y)) :
    Function.rightLim f a = y :=
  @leftLim_eq_of_tendsto αᵒᵈ _ _ _ _ _ _ f a y h h'

theorem rightLim_eq_of_eq_bot [TopologicalSpace α] [OrderTopology α] (f : α → β) {a : α}
    (h : 𝓝[>] a = ⊥) : rightLim f a = f a :=
  @leftLim_eq_of_eq_bot αᵒᵈ _ _ _ _ _  f a h

end

open Function

namespace Monotone

variable {α β : Type*} [LinearOrder α] [ConditionallyCompleteLinearOrder β] [TopologicalSpace β]
  [OrderTopology β] {f : α → β} (hf : Monotone f) {x y : α}

theorem leftLim_eq_sSup [TopologicalSpace α] [OrderTopology α] (h : 𝓝[<] x ≠ ⊥) :
    leftLim f x = sSup (f '' Iio x) :=
  leftLim_eq_of_tendsto h (hf.tendsto_nhdsWithin_Iio x)

theorem rightLim_eq_sInf [TopologicalSpace α] [OrderTopology α] (h : 𝓝[>] x ≠ ⊥) :
    rightLim f x = sInf (f '' Ioi x) :=
  rightLim_eq_of_tendsto h (hf.tendsto_nhdsWithin_Ioi x)

theorem leftLim_le (h : x ≤ y) : leftLim f x ≤ f y := by
  letI : TopologicalSpace α := Preorder.topology α
  haveI : OrderTopology α := ⟨rfl⟩
  rcases eq_or_ne (𝓝[<] x) ⊥ with (h' | h')
  simpa [leftLim, h'] using hf h
  haveI A : NeBot (𝓝[<] x) := neBot_iff.2 h'
  rw [leftLim_eq_sSup hf h']
  refine csSup_le ?_ ?_
  simp only [image_nonempty]
  exact (forall_mem_nonempty_iff_neBot.2 A) _ self_mem_nhdsWithin
  simp only [mem_image, mem_Iio, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  intro z hz
  exact hf (hz.le.trans h)

theorem le_leftLim (h : x < y) : f x ≤ leftLim f y := by
  letI : TopologicalSpace α := Preorder.topology α
  haveI : OrderTopology α := ⟨rfl⟩
  rcases eq_or_ne (𝓝[<] y) ⊥ with (h' | h')
  rw [leftLim_eq_of_eq_bot _ h']
  exact hf h.le
  rw [leftLim_eq_sSup hf h']
  refine le_csSup ⟨f y, ?_⟩ (mem_image_of_mem _ h)
  simp only [upperBounds, mem_image, mem_Iio, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂, mem_setOf_eq]
  intro z hz
  exact hf hz.le

@[mono]
protected theorem leftLim : Monotone (leftLim f) := by
  intro x y h
  rcases eq_or_lt_of_le h with (rfl | hxy)
  exact le_rfl
  exact (hf.leftLim_le le_rfl).trans (hf.le_leftLim hxy)

theorem le_rightLim (h : x ≤ y) : f x ≤ rightLim f y :=
  hf.dual.leftLim_le h

theorem rightLim_le (h : x < y) : rightLim f x ≤ f y :=
  hf.dual.le_leftLim h

@[mono]
protected theorem rightLim : Monotone (rightLim f) := fun _ _ h => hf.dual.leftLim h

theorem leftLim_le_rightLim (h : x ≤ y) : leftLim f x ≤ rightLim f y :=
  (hf.leftLim_le le_rfl).trans (hf.le_rightLim h)

theorem rightLim_le_leftLim (h : x < y) : rightLim f x ≤ leftLim f y := by
  letI : TopologicalSpace α := Preorder.topology α
  haveI : OrderTopology α := ⟨rfl⟩
  rcases eq_or_ne (𝓝[<] y) ⊥ with (h' | h')
  simp [leftLim, h']
  exact rightLim_le hf h
  obtain ⟨a, ⟨xa, ay⟩⟩ : (Ioo x y).Nonempty :=
    forall_mem_nonempty_iff_neBot.2 (neBot_iff.2 h') (Ioo x y)
      (Ioo_mem_nhdsWithin_Iio ⟨h, le_refl _⟩)
  calc
    rightLim f x ≤ f a := hf.rightLim_le xa
    _ ≤ leftLim f y := hf.le_leftLim ay

variable [TopologicalSpace α] [OrderTopology α]

theorem tendsto_leftLim (x : α) : Tendsto f (𝓝[<] x) (𝓝 (leftLim f x)) := by
  rcases eq_or_ne (𝓝[<] x) ⊥ with (h' | h')
  simp [h']
  rw [leftLim_eq_sSup hf h']
  exact hf.tendsto_nhdsWithin_Iio x

theorem tendsto_leftLim_within (x : α) : Tendsto f (𝓝[<] x) (𝓝[≤] leftLim f x) := by
  apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within f (hf.tendsto_leftLim x)
  filter_upwards [@self_mem_nhdsWithin _ _ x (Iio x)] with y hy using hf.le_leftLim hy

theorem tendsto_rightLim (x : α) : Tendsto f (𝓝[>] x) (𝓝 (rightLim f x)) :=
  hf.dual.tendsto_leftLim x

theorem tendsto_rightLim_within (x : α) : Tendsto f (𝓝[>] x) (𝓝[≥] rightLim f x) :=
  hf.dual.tendsto_leftLim_within x

/-- A monotone function is continuous to the left at a point if and only if its left limit
coincides with the value of the function. -/
theorem continuousWithinAt_Iio_iff_leftLim_eq :
    ContinuousWithinAt f (Iio x) x ↔ leftLim f x = f x := by
  rcases eq_or_ne (𝓝[<] x) ⊥ with (h' | h')
  simp [leftLim_eq_of_eq_bot f h', ContinuousWithinAt, h']
  haveI : (𝓝[Iio x] x).NeBot := neBot_iff.2 h'
  refine ⟨fun h => tendsto_nhds_unique (hf.tendsto_leftLim x) h.tendsto, fun h => ?_⟩
  have := hf.tendsto_leftLim x
  rwa [h] at this

/-- A monotone function is continuous to the right at a point if and only if its right limit
coincides with the value of the function. -/
theorem continuousWithinAt_Ioi_iff_rightLim_eq :
    ContinuousWithinAt f (Ioi x) x ↔ rightLim f x = f x :=
  hf.dual.continuousWithinAt_Iio_iff_leftLim_eq

/-- A monotone function is continuous at a point if and only if its left and right limits
coincide. -/
theorem continuousAt_iff_leftLim_eq_rightLim : ContinuousAt f x ↔ leftLim f x = rightLim f x := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  have A : leftLim f x = f x :=
    hf.continuousWithinAt_Iio_iff_leftLim_eq.1 h.continuousWithinAt
  have B : rightLim f x = f x :=
    hf.continuousWithinAt_Ioi_iff_rightLim_eq.1 h.continuousWithinAt
  exact A.trans B.symm
  have h' : leftLim f x = f x := by
    apply le_antisymm (leftLim_le hf (le_refl _))
    rw [h]
    exact le_rightLim hf (le_refl _)
  refine continuousAt_iff_continuous_left'_right'.2 ⟨?_, ?_⟩
  exact hf.continuousWithinAt_Iio_iff_leftLim_eq.2 h'
  rw [h] at h'
  exact hf.continuousWithinAt_Ioi_iff_rightLim_eq.2 h'

/-- In a second countable space, the set of points where a monotone function is not right-continuous
is at most countable. Superseded by `countable_not_continuousAt` which gives the two-sided
version. -/
theorem countable_not_continuousWithinAt_Ioi [SecondCountableTopology β] :
    Set.Countable { x | ¬ContinuousWithinAt f (Ioi x) x } := by
  apply (countable_image_lt_image_Ioi f).mono
  rintro x (hx : ¬ContinuousWithinAt f (Ioi x) x)
  dsimp
  contrapose! hx
  refine tendsto_order.2 ⟨fun m hm => ?_, fun u hu => ?_⟩
  filter_upwards [@self_mem_nhdsWithin _ _ x (Ioi x)] with y hy using hm.trans_le
    (hf (le_of_lt hy))
  rcases hx u hu with ⟨v, xv, fvu⟩
  have : Ioo x v ∈ 𝓝[>] x := Ioo_mem_nhdsWithin_Ioi ⟨le_refl _, xv⟩
  filter_upwards [this] with y hy
  apply (hf hy.2.le).trans_lt fvu

/-- In a second countable space, the set of points where a monotone function is not left-continuous
is at most countable. Superseded by `countable_not_continuousAt` which gives the two-sided
version. -/
theorem countable_not_continuousWithinAt_Iio [SecondCountableTopology β] :
    Set.Countable { x | ¬ContinuousWithinAt f (Iio x) x } :=
  hf.dual.countable_not_continuousWithinAt_Ioi

/-- In a second countable space, the set of points where a monotone function is not continuous
is at most countable. -/
theorem countable_not_continuousAt [SecondCountableTopology β] :
    Set.Countable { x | ¬ContinuousAt f x } := by
  apply
    (hf.countable_not_continuousWithinAt_Ioi.union hf.countable_not_continuousWithinAt_Iio).mono
      _
  refine compl_subset_compl.1 ?_
  simp only [compl_union]
  rintro x ⟨hx, h'x⟩
  simp only [mem_setOf_eq, Classical.not_not, mem_compl_iff] at hx h'x ⊢
  exact continuousAt_iff_continuous_left'_right'.2 ⟨h'x, hx⟩

end Monotone

namespace Antitone

variable {α β : Type*} [LinearOrder α] [ConditionallyCompleteLinearOrder β] [TopologicalSpace β]
  [OrderTopology β] {f : α → β} (hf : Antitone f) {x y : α}

theorem le_leftLim (h : x ≤ y) : f y ≤ leftLim f x :=
  hf.dual_right.leftLim_le h

theorem leftLim_le (h : x < y) : leftLim f y ≤ f x :=
  hf.dual_right.le_leftLim h

@[mono]
protected theorem leftLim : Antitone (leftLim f) :=
  hf.dual_right.leftLim

theorem rightLim_le (h : x ≤ y) : rightLim f y ≤ f x :=
  hf.dual_right.le_rightLim h

theorem le_rightLim (h : x < y) : f y ≤ rightLim f x :=
  hf.dual_right.rightLim_le h

@[mono]
protected theorem rightLim : Antitone (rightLim f) :=
  hf.dual_right.rightLim

theorem rightLim_le_leftLim (h : x ≤ y) : rightLim f y ≤ leftLim f x :=
  hf.dual_right.leftLim_le_rightLim h

theorem leftLim_le_rightLim (h : x < y) : leftLim f y ≤ rightLim f x :=
  hf.dual_right.rightLim_le_leftLim h

variable [TopologicalSpace α] [OrderTopology α]

theorem tendsto_leftLim (x : α) : Tendsto f (𝓝[<] x) (𝓝 (leftLim f x)) :=
  hf.dual_right.tendsto_leftLim x

theorem tendsto_leftLim_within (x : α) : Tendsto f (𝓝[<] x) (𝓝[≥] leftLim f x) :=
  hf.dual_right.tendsto_leftLim_within x

theorem tendsto_rightLim (x : α) : Tendsto f (𝓝[>] x) (𝓝 (rightLim f x)) :=
  hf.dual_right.tendsto_rightLim x

theorem tendsto_rightLim_within (x : α) : Tendsto f (𝓝[>] x) (𝓝[≤] rightLim f x) :=
  hf.dual_right.tendsto_rightLim_within x

/-- An antitone function is continuous to the left at a point if and only if its left limit
coincides with the value of the function. -/
theorem continuousWithinAt_Iio_iff_leftLim_eq :
    ContinuousWithinAt f (Iio x) x ↔ leftLim f x = f x :=
  hf.dual_right.continuousWithinAt_Iio_iff_leftLim_eq

/-- An antitone function is continuous to the right at a point if and only if its right limit
coincides with the value of the function. -/
theorem continuousWithinAt_Ioi_iff_rightLim_eq :
    ContinuousWithinAt f (Ioi x) x ↔ rightLim f x = f x :=
  hf.dual_right.continuousWithinAt_Ioi_iff_rightLim_eq

/-- An antitone function is continuous at a point if and only if its left and right limits
coincide. -/
theorem continuousAt_iff_leftLim_eq_rightLim : ContinuousAt f x ↔ leftLim f x = rightLim f x :=
  hf.dual_right.continuousAt_iff_leftLim_eq_rightLim

/-- In a second countable space, the set of points where an antitone function is not continuous
is at most countable. -/
theorem countable_not_continuousAt [SecondCountableTopology β] :
    Set.Countable { x | ¬ContinuousAt f x } :=
  hf.dual_right.countable_not_continuousAt

end Antitone
