/-
Copyright (c) 2023 Christopher Hoskin. All rights reserved.
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

class TrilinearTp (A : Type _) [AddCommMonoid A] (Aₛ : AddSubmonoid A) where
  tp : A →+ Aₛ →+ A →+ A
  subtriple: ∀ (a b c : Aₛ), tp a b c ∈ Aₛ

notation "⦃" a "," b "," c "⦄" => TrilinearTp.tp  a b c

namespace TrilinearTp

variable {A : Type _}  [AddCommMonoid A] {Aₛ : AddSubmonoid A} [TrilinearTp A Aₛ]

lemma add_left (a₁ a₂ c : A) (b : Aₛ) : ⦃a₁ + a₂, b, c⦄ = ⦃a₁, b, c⦄ + ⦃a₂, b, c⦄ := by
rw [map_add, AddMonoidHom.add_apply, AddMonoidHom.add_apply]

lemma add_middle (a c : A) (b₁ b₂ : Aₛ) : ⦃a, b₁ + b₂, c⦄ = ⦃a, b₁, c⦄ + ⦃a, b₂, c⦄ := by
rw [map_add, AddMonoidHom.add_apply]

lemma add_right (a c₁ c₂ : A) (b : Aₛ) : ⦃a, b, c₁ + c₂⦄ = ⦃a, b, c₁⦄ + ⦃a, b, c₂⦄ := by
rw [map_add]

/--
We say that a pair of operators $(T,T^′)$ are Leibniz if they satisfy a law reminiscent of
differentiation.
-/
def leibniz (T : A → A) (T'  : Aₛ → Aₛ) : Prop :=
  ∀ (a c : A) (b : Aₛ), T ⦃ a, b, c ⦄ = ⦃ T a, b, c⦄ + ⦃a, T' b, c⦄ + ⦃a, b, T c⦄

/-- Define the multiplication operator `D` -/
def D : A →+ Aₛ →+ AddMonoid.End A := TrilinearTp.tp

/-- homotope a is the a-homotope -/
def homotope : Aₛ →+ A →+ AddMonoid.End A := AddMonoidHom.flipHom (D : A →+ Aₛ →+ AddMonoid.End A)

lemma homotope_def (a c : A) (b : Aₛ) : homotope b a c = ⦃a, b, c⦄ := rfl

-- /-- Define the quadratic operator `Q` -/
/-
@[simps] def Q : A →+ A →+  AddMonoid.End Aₛ :=
{ toFun := fun a => AddMonoidHom.flipHom (D a : Aₛ →+  AddMonoid.End A)
  map_zero' := by
    ext
    simp
  map_add' := fun _ _ => by
    ext
    simp }
-/


end TrilinearTp

class PartialTripleProduct (A : Type _) [AddCommMonoid A] {Aₛ : AddSubmonoid A}
    extends TrilinearTp A Aₛ where
  comm : ∀ (a c : A) (b : Aₛ), ⦃a, b, c⦄ = ⦃c, b, a⦄

namespace PartialTripleProduct

open TrilinearTp

variable {A : Type _}  [AddCommMonoid A] {Aₛ : AddSubmonoid A} [TrilinearTp A Aₛ]

/-
lemma polar (a c : A) (b : Aₛ): ⦃a + c, b, a + c⦄ = ⦃a, b, a⦄ + 2•⦃a, b, c⦄ + ⦃c, b, c⦄ :=
calc
  ⦃a + c, b, a + c⦄ = ⦃a, b, a + c⦄ + ⦃c, b, a + c⦄ := by rw [add_left]
  _ = ⦃a, b, a⦄ + ⦃a, b, c⦄ + (⦃c, b, a⦄ + ⦃c, b, c⦄) := by rw [add_right, add_right]
  _ = ⦃a, b, a⦄ + ⦃a, b, c⦄ + (⦃a, b, c⦄ + ⦃c, b, c⦄) := by rw [comm c b a]
  _ = ⦃a, b, a⦄ + (⦃a, b, c⦄ + ⦃a, b, c⦄) + ⦃c, b, c⦄ := by abel
  _ = ⦃a, b, a⦄ + 2•⦃a, b, c⦄ + ⦃c, b, c⦄ := by rw [two_nsmul]
-/

end PartialTripleProduct

class PartialStarTriple (R : Type _) [CommSemiring R] [StarRing R] (A : Type _)
[AddCommMonoid A] [Module R A] (Aₛ : Submodule R A) where
  tp : A →ₗ[R] Aₛ →ₛₗ[starRingEnd R] A →ₗ[R] A
  comm (a c : A) (b : Aₛ) : tp a b c = tp c b a
  subtriple (a b c : Aₛ) : tp a b c ∈ Aₛ

notation "⦃" a "," b "," c "⦄" => PartialStarTriple.tp a b c

namespace PartialStarTriple

variable (R : Type _) [CommSemiring R] [StarRing R] (A : Type _) [AddCommMonoid A] [Module R A]
  (Aₛ : Submodule R A)

variable (T : A →ₗ[R] A)

lemma test : Aₛ ≤ ⊤ := by
  exact Iff.mp Submodule.comap_subtype_eq_top rfl

#check Submodule.ofLe

#check submonoid.inclusion

#check AddMonoidHom.flipHom

#check Aₛ.subtype

#check (↑T ∘ Aₛ.subtype)

#check Function.invFun_eq_of_injective_of_rightInverse

variable [h: PartialStarTriple R A Aₛ]

#check h.tp (Aₛ.subtype _) _ (Aₛ.subtype _)

instance  : PartialStarTriple R Aₛ ⊤ where
  tp (a b c : Aₛ) := h.tp (Aₛ.subtype a) b (Aₛ.subtype c)
  comm := sorry
  subtriple := sorry


-- (Aₛ,Aₛ) is a (partial) *-triple
instance [h: PartialStarTriple R A Aₛ] : PartialStarTriple R Aₛ ⊤ where
  tp := h.tp
  comm := h.comm
  subtriple := h.subtriple



/-- The type of centroid homomorphisms from `A` to `A`. -/
structure CentroidHom extends A →ₗ[R] A where
  map_left (a c : A) (b : Aₛ) : toFun ⦃a, b, c⦄ = ⦃toFun a, b, c⦄
  map_mid: ∃ (S : Aₛ →ₗ[R] Aₛ), ∀ (a c : A) (b : Aₛ), toFun ⦃a, b, c⦄ = ⦃a, S.toFun b, c⦄

--structure

-- lemma CentroidHom.map_right (a c : A) (b : Aₛ) :

namespace CentroidHom

/-- `id` as a `CentroidHom`. -/
protected def id : CentroidHom R A Aₛ :=
{ (LinearMap.id :  A →ₗ[R] A) with
  map_left := fun _ _ _ ↦ rfl
  map_mid := by
    use (LinearMap.id :  Aₛ →ₗ[R] Aₛ)
    simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearMap.id_coe, id_eq,
      Subtype.forall, implies_true, forall_const] }

end CentroidHom

end PartialStarTriple
