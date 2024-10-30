import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.Functor.Const
import Mathlib.CategoryTheory.ChosenFiniteProducts
import Mathlib.CategoryTheory.Closed.Cartesian
import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts
import Mathlib.CategoryTheory.Limits.Shapes.Terminal

namespace Guardedlean

universe u v

def makeArrow : {n m : ℕ} → (p : n ≤ m) → (n ⟶ m) := λ p => ULift.up (PLift.up p)
def makeOpArrow : {n m : ℕ} → (n ≤ m) → (Opposite.op m ⟶ Opposite.op n) := λ p => Quiver.Hom.op (makeArrow p)
def unmakeArrow : {n m : ℕ} →  (p: n ⟶ m) → (n ≤ m):= λ p => PLift.down (ULift.down p)
def unmakeOpArrow : {n m : ℕ} → (p : Opposite.op m ⟶ Opposite.op n) → (n ≤ m) := λ p => unmakeArrow (Quiver.Hom.unop p)
-- TODO This lemma should exist somewhere, right ?
lemma comp_assoc {A B C D:Type} (a : A → B) (b : B → C) (c : C → D) :
  (c ∘ b) ∘ a = c ∘ (b ∘ a) := by {
    rw [Function.comp_def,Function.comp_def,Function.comp_def,Function.comp_def]
  }
lemma cast_replace {X : Sort} {Y : X → Sort} {a b : X} (eq eq': Y a = Y b) (x : Y a) : eq ▸ x = eq' ▸ x := by {cases eq; rfl}

lemma cast_symm {X Y : Sort} (e : X = Y) (x : X) (y : Y): e ▸ x = y → x = e ▸ y := by intro h;cases h;simp

@[simp]
lemma cast_poly {α β : Sort} {φ : Sort → Sort} (f : {ξ : Sort} → ξ → φ ξ) (e : α = β) (x : α)
  : f (cast e x) = cast (congrArg φ e) (f x) := by {
    cases e
    rfl
  }
@[simp]
lemma cast_poly2 {X : Sort u} {α β : X} {φ ψ : X → Sort v} (f : {ξ : X} → φ ξ → ψ ξ) (e : α = β) (x : φ α)
  : f (cast (congrArg φ e) x) = cast (congrArg ψ e) (f x) := by {
    cases e
    rfl
  }
lemma etaCast {α β γ: Sort u} {f : β → γ} {e : α = β} : (fun x:α => f (e ▸ x)) = e ▸ f := by {
  cases e
  rfl
}
@[simp]
lemma compCast {α α' β γ : Sort u} (f : α → β) (g : β → γ) {e : α = α'}: g ∘ (e ▸ f) = e ▸ (g ∘ f) := by {cases e;rfl}
@[simp]
lemma compCast2 {α β γ γ' : Sort u} (f : α → β) (g : β → γ) {e : γ = γ'}: (e ▸ g) ∘ f = e ▸ (g ∘ f) := by {cases e;rfl}

lemma compDefExt {α β γ : Sort u} (f : β → γ) (g : α → β) (x : α): f (g x) = (f ∘ g) x := by simp


-- We can do an induction on ℕ with (0,1,+)
lemma ℕsumInduction (P : ℕ → Prop) (zero : P 0) (one : P 1) (add : ∀ a b, P a → P b → P (a+b)):
  ∀ n, P n := by
  intro n
  induction n with
  | zero => apply zero
  | succ n₀ hr => cases n₀ with
  | zero => apply one
  | succ n₁ => apply add; apply hr; apply one
