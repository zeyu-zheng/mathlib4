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

class PartialStarTriple (R : Type _) [CommSemiring R] [StarRing R] (A : Type*)
[AddCommMonoid A] [Module R A] (Aₛ : Submodule R A) where
  tp : A →ₗ[R] Aₛ →ₛₗ[starRingEnd R] A →ₗ[R] A
  comm (a c : A) (b : Aₛ) : tp a b c = tp c b a
  subtriple (a b c : Aₛ) : tp a b c ∈ Aₛ

-- def trivial_star_triple


class StarTriple (R : Type _) [CommSemiring R] [StarRing R] (A : Type*)
[AddCommMonoid A] [Module R A] where
  tp : A →ₗ[R] A →ₛₗ[starRingEnd R] A →ₗ[R] A
  comm (a b c : A) : tp a b c = tp c b a


/- Composing a linear map `P → Q` and a bilinear map `M → N → P` to
form a bilinear map `M → N → Q`.
def compr₂ (f : M →ₗ[R] Nₗ →ₗ[R] Pₗ) (g : Pₗ →ₗ[R] Qₗ) : M →ₗ[R] Nₗ →ₗ[R] Qₗ :=
  llcomp R Nₗ Pₗ Qₗ g ∘ₗ f
-/

/- Composing a linear map `Q → N` and a bilinear map `M → N → P` to
form a bilinear map `M → Q → P`.
def compl₂ (g : Q →ₛₗ[σ₄₂] N) : M →ₛₗ[σ₁₃] Q →ₛₗ[σ₄₃] P :=
  (lcompₛₗ _ _ g).comp f
-/

section StarTriple_is_PartialStarTriple

variable {R : Type _} [CommSemiring R] [StarRing R] {A : Type*} [AddCommMonoid A] [Module R A]
  [StarTriple R A]


/-
instance third (a : A) (b : (⊤ : Submodule R A)) : A →ₗ[R] A where
  toFun (c : A) := StarTriple.tp a b c
  map_add' _ _ := LinearMap.map_add ((StarTriple.tp a) ↑b) _ _
  map_smul' _ _ := LinearMap.map_smul ((StarTriple.tp a) ↑b) _ _

lemma apply_third (a : A) (b : (⊤ : Submodule R A)) : third a b = StarTriple.tp a b := rfl

instance second (a : A) : (⊤ : Submodule R A) →ₛₗ[starRingEnd R] A →ₗ[R] A where
  toFun (b : (⊤ : Submodule R A)) := third a b
  map_add' _ _ := by
    simp only [apply_third, Submodule.top_coe, AddSubmonoid.coe_add, Submodule.top_toAddSubmonoid,
      AddSubmonoid.coe_top, map_add]
  map_smul' _ _ := by
    simp only [apply_third, Submodule.top_coe, SetLike.val_smul, map_smulₛₗ, LinearMap.smul_apply]

lemma apply_second (a : A) (b : (⊤ : Submodule R A)) : second a b = StarTriple.tp a b := rfl

instance first : A →ₗ[R] (⊤ : Submodule R A) →ₛₗ[starRingEnd R] A →ₗ[R] A where
  toFun (a : A) := second a
  map_add' _ _ := by
    ext _
    simp only [apply_second, map_add, Submodule.top_coe, LinearMap.add_apply]
  map_smul' _ _ := by
    ext _
    simp only [apply_second, map_smul, Submodule.top_coe, LinearMap.smul_apply, RingHom.id_apply]

lemma apply_first (a : A) (b : (⊤ : Submodule R A)) : ((first a) b)  = StarTriple.tp a b := rfl

instance : PartialStarTriple R A ⊤ where
  tp := first
  comm _ _ _ := by
    rw [apply_first, StarTriple.comm, apply_first]
  subtriple _ _ _ := by
    simp only [Submodule.top_coe, Submodule.mem_top]
-/

/--
Every *-triple is a partial *-triple
-/
instance : PartialStarTriple R A ⊤ where
  tp := LinearMap.compl₂ StarTriple.tp (Submodule.subtype (⊤ : Submodule R A))
  comm _ _ _ := by
    simp only [LinearMap.compl₂_apply, Submodule.coeSubtype, StarTriple.comm]
  subtriple _ _ _ := trivial

end StarTriple_is_PartialStarTriple

section PartialStarTriple_symmetric_top_is_StarTriple

variable {R : Type _} [CommSemiring R] [StarRing R] {A : Type*} [AddCommMonoid A] [Module R A]
  [PartialStarTriple R A (⊤ : Submodule R A)]


/-
/--
If `A` is a partial *-triple with symmetric part `A` then `A` is a *-triple
-/
instance : StarTriple R A where
  tp  := PartialStarTriple.tp
  comm := sorry
-/

end PartialStarTriple_symmetric_top_is_StarTriple

notation "⦃" a "," b "," c "⦄" => PartialStarTriple.tp a b c

namespace PartialStarTriple

variable {R : Type _} [CommSemiring R] [StarRing R] {A : Type _} [AddCommMonoid A] [Module R A]
  {Aₛ : Submodule R A}

lemma smul_middle [PartialStarTriple R A Aₛ] (a c : A) (b : Aₛ) (r : R) :
    ⦃a, r•b, c⦄ = (star r) • ⦃a, b, c⦄ := by
  simp only [map_smulₛₗ, LinearMap.smul_apply]
  rfl

variable (T : A →ₗ[R] A)

lemma test : Aₛ ≤ ⊤ := by
  exact Iff.mp Submodule.comap_subtype_eq_top rfl

variable [h: PartialStarTriple R A Aₛ]

lemma test1 (b : Aₛ) : ∀ (a : A), a ∈ Aₛ → ∀ (c : A), c ∈ Aₛ → h.tp a b c ∈ Aₛ :=
  fun a ha c hc => (h.subtriple ⟨a,ha⟩ b ⟨c,hc⟩)

lemma test2 (b : (⊤ : Submodule R Aₛ)) : ∀ (a : A), a ∈ Aₛ → ∀ (c : A), c ∈ Aₛ → h.tp a b c ∈ Aₛ :=
  fun a ha c hc => (h.subtriple ⟨a,ha⟩ b ⟨c,hc⟩)

instance third (a : Aₛ) (b : (⊤ : Submodule R Aₛ)) : Aₛ →ₗ[R] Aₛ where
  toFun (c : Aₛ) := (h.tp a b).restrict (test2 b a a.prop) c
  map_add' d e := by
    simp only [Submodule.top_coe, map_add]
  map_smul' r d := by
    simp only [Submodule.top_coe, map_smul, RingHom.id_apply]

lemma apply_third (a : Aₛ) (b : (⊤ : Submodule R Aₛ)) (c : Aₛ) : third a b c = h.tp a b c := rfl

instance second (a : Aₛ) : (⊤ : Submodule R Aₛ) →ₛₗ[starRingEnd R] Aₛ →ₗ[R] Aₛ where
  toFun (b : (⊤ : Submodule R Aₛ)) := third a b
  map_add' _ _ := by
    ext _
    simp only [apply_third, Submodule.top_coe, AddSubmonoid.coe_add, Submodule.top_toAddSubmonoid,
      AddSubmonoid.coe_top, map_add, LinearMap.add_apply, Submodule.coe_toAddSubmonoid]
  map_smul' _ _ := by
    ext _
    simp only [apply_third, Submodule.top_coe, SetLike.val_smul, map_smulₛₗ, LinearMap.smul_apply]

lemma apply_second (a : Aₛ) (b : (⊤ : Submodule R Aₛ)) (c : Aₛ) : second a b c = h.tp a b c := rfl

instance first : Aₛ →ₗ[R] (⊤ : Submodule R Aₛ) →ₛₗ[starRingEnd R] Aₛ →ₗ[R] Aₛ where
  toFun (a : Aₛ) := second a
  map_add' _ _ := by
    ext _
    simp only [apply_second, Submodule.top_coe, AddSubmonoid.coe_add, Submodule.coe_toAddSubmonoid,
      map_add, LinearMap.add_apply]
  map_smul' _ _ := by
    ext _
    simp only [apply_second, Submodule.top_coe, SetLike.val_smul, map_smul, LinearMap.smul_apply,
      RingHom.id_apply]

lemma apply_first (a : Aₛ) (b : (⊤ : Submodule R Aₛ)) (c : Aₛ) : ((first a) b) c = h.tp a b c := rfl

-- (Aₛ,Aₛ) is a (partial) *-triple
instance  : PartialStarTriple R Aₛ ⊤ where
  tp  := first
  comm _ _ _ := by
    ext
    rw [apply_first, h.comm, apply_first]
  subtriple a b c := by
    simp only [Submodule.top_coe, Submodule.mem_top]

/-
instance : StarTriple R Aₛ where
  tp := sorry
  comm := sorry
-/

/-- The type of centroid homomorphisms from `A` to `A`. -/
structure CentroidHom extends A →ₗ[R] A where
  map_left (a c : A) (b : Aₛ) : toFun ⦃a, b, c⦄ = ⦃toFun a, b, c⦄
  map_mid: ∃ (S : Aₛ →ₗ[R] Aₛ), ∀ (a c : A) (b : Aₛ), toFun ⦃a, b, c⦄ = ⦃a, S.toFun b, c⦄

--structure

-- lemma CentroidHom.map_right (a c : A) (b : Aₛ) :

namespace CentroidHom
/-
/-- `id` as a `CentroidHom`. -/
protected def id : CentroidHom R A Aₛ :=
{ (LinearMap.id :  A →ₗ[R] A) with
  map_left := fun _ _ _ ↦ rfl
  map_mid := by
    use (LinearMap.id :  Aₛ →ₗ[R] Aₛ)
    simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearMap.id_coe, id_eq,
      Subtype.forall, implies_true, forall_const] }
-/
end CentroidHom

end PartialStarTriple
