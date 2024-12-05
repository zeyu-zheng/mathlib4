import Mathlib.SetTheory.Game.PGame
import Mathlib.Data.Fintype.Card

open SetTheory

/-- Interprets a type as a combinatorial game, by specifying the relations which determine whether
a given player can change the game state in a given manner. -/
class ConcreteGame (α : Type*) where
  /-- `x ≺ₗ y` when Left can move from `y` to `x`. -/
  leftSubsequent : α → α → Prop
  /-- `x ≺ᵣ y` when Right can move from `y` to `x`. -/
  rightSubsequent : α → α → Prop
  /-- The game must terminate in a finite amount of moves. -/
  wf : WellFounded fun x y ↦ leftSubsequent x y ∨ rightSubsequent x y

namespace ConcreteGame

variable {α : Type*} [ConcreteGame α]

@[inherit_doc]
scoped infixl:50 " ≺ₗ " => leftSubsequent

@[inherit_doc]
scoped infixl:50 " ≺ᵣ " => rightSubsequent

/-- `x ≺ y` when either `x ≺ₗ y` or `x ≺ᵣ y`. -/
def subsequent (x y : α) : Prop :=
  x ≺ₗ y ∨ x ≺ᵣ y

@[inherit_doc]
scoped infixl:50 " ≺ " => subsequent

theorem leftSubsequent.subsequent : @Subrelation α (· ≺ₗ ·) (· ≺ ·) :=
  Or.inl

theorem rightSubsequent.subsequent : @Subrelation α (· ≺ᵣ ·) (· ≺ ·) :=
  Or.inr

instance : IsWellFounded α (· ≺ ·) :=
  ⟨ConcreteGame.wf⟩

instance : IsWellFounded α (· ≺ₗ ·) :=
  leftSubsequent.subsequent.isWellFounded

instance : IsWellFounded α (· ≺ᵣ ·) :=
  rightSubsequent.subsequent.isWellFounded

instance : WellFoundedRelation α :=
  IsWellFounded.toWellFoundedRelation (· ≺ ·)

/-- Turns a state of a concrete game into a `PGame`. -/
def toPGame (x : α) : PGame :=
  .mk {y // y ≺ₗ x} {y // y ≺ᵣ x} (fun y ↦ toPGame y) (fun y ↦ toPGame y)
termination_by x
decreasing_by all_goals exact y.2.subsequent

end ConcreteGame

/-- Proof of concept: 10-stone nim. -/
def Nim : Type := Fin 10

instance : ConcreteGame Nim where
  leftSubsequent := (· < · : Fin _ → _ → _)
  rightSubsequent := (· < · : Fin _ → _ → _)
  wf := by
    simp_rw [or_self]
    exact wellFounded_lt (α := Fin _)

/-- The `PGame` corresponding to a given amount of stones. -/
def nim (x : Nim) := ConcreteGame.toPGame x
