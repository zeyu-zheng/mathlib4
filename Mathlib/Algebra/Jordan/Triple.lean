/-
Copyright (c) 2022 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/
import Mathlib.Algebra.Lie.OfAssociative

/-!
# Jordan triples

Let `A` be a module over a ring `R`. A triple product on `A` is a trilinear map
$\{.\,.\,\}:A\times A\times A\mapsto A$ which is symmetric in the first and third variables. The
module `A` is said to be a Jordan triple if, for any `a`, `b`, `c`, `d` and `e` in `A` the following
Leibniz rule is satisfied:
$$
\{a\,b\,\{c\,d\,e\}\} = \{\{a\,b\,c\}\,d\,e\} - \{c\,\{b\,a\,d\}\,e\} + \{c\,d\,\{a\,b\,e\}\}
$$
A module `A` over a *-ring `R` is said to be a *-triple if it has a triple product linear and
symmetric in the first and thrid variable and conjugate linear in the second variable. A *-triple
satisfying the Leibniz rule is said to be a Jordan *-triple.

As well as being of algebraic interest, Jordan *-triples arise naturally in mathematical physics,
functional analysis and differential geometry. For more information about these connections the
interested reader is referred to [alfsenshultz2003], [chu2012], [friedmanscarr2005],
[iordanescu2003] and [upmeier1987].

## Main results

(None yet, we're just getting started.)

## References

* [Chu, Jordan Structures in Geometry and Analysis][chu2012]
-/

/-- An additive commutative monoid with a trilinear triple product -/
class has_trilinear_tp (A : Type*) [AddCommMonoid A] := (tp : A →+ A →+ A →+ A )

notation "⦃" a ", " b ", " c "⦄" => has_trilinear_tp.tp a b c

namespace has_trilinear_tp

lemma add_left {A : Type*} [AddCommMonoid A] [has_trilinear_tp A] (a₁ a₂ b c : A) :
  ⦃a₁ + a₂, b, c⦄ = ⦃a₁, b, c⦄ + ⦃a₂, b, c⦄ :=
by rw [map_add, AddMonoidHom.add_apply, AddMonoidHom.add_apply]

lemma add_middle {A : Type*} [AddCommMonoid A] [has_trilinear_tp A] (a b₁ b₂ c : A) :
  ⦃a, b₁ + b₂, c⦄ = ⦃a, b₁, c⦄ + ⦃a, b₂, c⦄ := by rw [map_add, AddMonoidHom.add_apply]

lemma add_right {A : Type*} [AddCommMonoid A] [has_trilinear_tp A] (a b c₁ c₂ : A) :
  ⦃a, b, c₁ + c₂⦄ = ⦃a, b, c₁⦄ + ⦃a, b, c₂⦄ := by rw [map_add]

end has_trilinear_tp

/-- A Jordan triple product satisfies a Leibniz law -/
class is_jordan_tp (A : Type*) [AddCommGroup A] extends has_trilinear_tp A :=
(comm : ∀ (a b c : A), ⦃a, b, c⦄ = ⦃c, b, a⦄)
(jordan : ∀ (a b c d e: A), ⦃a, b, ⦃c, d, e⦄⦄  =
  ⦃⦃a, b, c⦄, d, e⦄ - ⦃c, ⦃b, a, d⦄, e⦄ + ⦃c, d, ⦃a, b, e⦄⦄)

namespace is_jordan_tp

open has_trilinear_tp

/--
We say that a pair of operators $(T,T^′)$ are Leibniz if they satisfy a law reminiscent of
differentiation.
-/
def leibniz {A : Type*} [AddCommMonoid A] [has_trilinear_tp A] (T : A → A) (T'  : A → A) : Prop :=
  ∀ (a b c : A),  T ⦃ a, b, c ⦄  = ⦃ T a, b, c⦄ + ⦃a, T' b, c⦄ + ⦃a, b, T c⦄

variable {A : Type*} [AddCommGroup A] [is_jordan_tp A]

/-
lemma polar (a b c : A) : ⦃a + c, b, a + c⦄ = ⦃a, b, a⦄ + 2•⦃a, b, c⦄ + ⦃c, b, c⦄ :=
calc
  ⦃a + c, b, a + c⦄ = ⦃a, b, a + c⦄ + ⦃c, b, a + c⦄ := by rw [add_left]
  _ = ⦃a, b, a⦄ + ⦃a, b, c⦄ + (⦃c, b, a⦄  + ⦃c, b, c⦄) := by rw [add_right, add_right]
  _ = ⦃a, b, a⦄ + ⦃a, b, c⦄ + (⦃a, b, c⦄ + ⦃c, b, c⦄) := by rw [comm c b a]
  _ = ⦃a, b, a⦄ + (⦃a, b, c⦄ + ⦃a, b, c⦄)  + ⦃c, b, c⦄ := by abel
  _ = ⦃a, b, a⦄ + 2•⦃a, b, c⦄ + ⦃c, b, c⦄ := by rw [two_nsmul]
-/

/-- Define the multiplication operator `D` -/
def D : A →+ A →+ AddMonoid.End A := has_trilinear_tp.tp

/-- homotope a is the a-homotope -/
def homotope : A →+ A →+ AddMonoid.End A := AddMonoidHom.flipHom (D : A →+ A →+ AddMonoid.End A)

lemma homotope_def (a b c : A) : homotope b a c = ⦃a, b, c⦄ := rfl

/-- Define the quadratic operator `Q` -/
@[simps] def Q : A →+ A →+  AddMonoid.End A :=
{ toFun := fun a => (D a : A →+  AddMonoid.End A).flip,
  map_zero' := by
    ext
    simp
  map_add' := fun _ _ => by
    ext
    simp
    rfl }

lemma Q_def (a b c : A) : Q a c b = ⦃a, b, c⦄ := rfl

lemma lie_D_D (a b c d: A) : ⁅D a b, D c d⁆ = D ⦃a, b, c⦄ d - D c ⦃b, a, d⦄ := by
  --simp
  apply AddMonoidHom.ext
  intro e
  rw [Ring.lie_def]
  unfold D
  simp
  rw [sub_eq_iff_eq_add, jordan]

/--
For a and b in A, the pair D(a,b) and -D(b,a) are Leibniz
-/
lemma D_D_leibniz (a b : A) : leibniz (D a b) (-D b a) := by
  unfold leibniz
  intros c d e
  unfold D
  simp
  rw [jordan]
  simp
  ring_nf

end is_jordan_tp
