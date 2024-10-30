import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.Functor.Const
import Mathlib.CategoryTheory.ChosenFiniteProducts
import Mathlib.CategoryTheory.Closed.Cartesian
import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Mathlib.Tests.ToT.Lemmas

open CategoryTheory

namespace Guardedlean

structure ToT where
  set : ℕ → Type
  restrict : ∀ n, set (n + 1) → set n

structure ToTMorphism (X Y : ToT) where
  setMorph : (n: ℕ) → (X.set n) → (Y.set n)
  restrictMorph: ∀ n,
    (Y.restrict n) ∘ (setMorph (n+1)) = (setMorph n) ∘ (X.restrict n)

instance : Category ToT where
  Hom := ToTMorphism
  id X := {
    setMorph := λ _n => id,
    restrictMorph := λ _n => by {rw [Function.id_comp, Function.comp_id]}
  }
  comp {X Y Z} u v := {
    setMorph := λ n => (v.setMorph n) ∘ (u.setMorph n),
    restrictMorph := by {
      intro n
      simp
      rw [← comp_assoc, v.restrictMorph n, comp_assoc, u.restrictMorph n, comp_assoc]
    }
  }

def ToT.iterRestrict (o : ToT) (n k m : ℕ) (e : n + k = m) (x : o.set m) : o.set n := match k with
  | 0 =>
    have e' : n = m := e
    e' ▸ x
  | k₀ + 1 =>
    have eq : n + 1 + k₀ = m := by omega
    o.restrict n (o.iterRestrict (n + 1) k₀ m eq x)

def ToT.iterRestrictZero (o : ToT) (n m : ℕ) (e : n = m) (x : o.set m) : o.iterRestrict n 0 m e x = e ▸ x := by
  unfold ToT.iterRestrict
  simp

def ToT.iterRestrictComp (o : ToT) (n m p k q : ℕ) (e₁ : n + k = m) (e₂ : p + q = n) (x : o.set m) :
    o.iterRestrict p q n e₂ (o.iterRestrict n k m e₁ x) = o.iterRestrict p (k + q) m (by omega) x := by
    induction q generalizing p with
    | zero =>
      rw [ToT.iterRestrictZero]
      subst e₂
      simp
    | succ q₀ hr =>
      unfold ToT.iterRestrict
      simp
      rw [hr]

theorem ToTMorphism.restrictMorphLift {X Y : ToT} (η : X ⟶ Y) : ∀ n k m, (eq : n + k = m) →
    (Y.iterRestrict n k m eq) ∘ (η.setMorph m) = (η.setMorph n) ∘ (X.iterRestrict n k m eq) := by {
      intro n
      intro k
      induction k generalizing n with
      | zero =>
        intro m eq
        funext x
        simp
        rw [ToT.iterRestrictZero,ToT.iterRestrictZero]
        subst eq
        rfl
      | succ k hk =>
          intro m eq
          funext x
          simp [ToT.iterRestrict]
          rw [compDefExt (η.setMorph n)]
          rw [<-η.restrictMorph]
          simp
          congr
          rw [compDefExt (Y.iterRestrict (n+1) k m _),compDefExt (η.setMorph (n+1))]
          rw [hk]
    }
