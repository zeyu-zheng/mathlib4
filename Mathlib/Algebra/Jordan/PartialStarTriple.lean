import Mathlib.Algebra.Lie.OfAssociative

class TrilinearTp (A : Type _) [AddCommMonoid A] (Aₛ : AddSubmonoid A) where
  tp : A →+ Aₛ →+ A →+ A

notation "⦃" a "," b "," c "⦄" => TrilinearTp.tp  a b c

lemma add_left {A : Type _}  [AddCommMonoid A] {Aₛ : AddSubmonoid A} [TrilinearTp A Aₛ] (a₁ a₂ c : A) (b : Aₛ):
  ⦃a₁ + a₂, b, c⦄ = ⦃a₁, b, c⦄ + ⦃a₂, b, c⦄ :=
by rw [map_add, AddMonoidHom.add_apply, AddMonoidHom.add_apply]

class PartialTripleProduct (A : Type _) [AddCommMonoid A] {Aₛ : AddSubmonoid A}
    extends TrilinearTp A Aₛ where
  comm : ∀ (a c : A) (b : Aₛ), ⦃a, b, c⦄ = ⦃c, b, a⦄
