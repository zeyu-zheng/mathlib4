import Mathlib.CategoryTheory.GradedObject.Braiding

namespace CategoryTheory

open Category Limits

variable {I : Type*} [AddCommMonoid I] {C : Type*} [Category C] [MonoidalCategory C]

namespace GradedObject

namespace Monoidal

variable (X Y Z : GradedObject I C)

set_option aesop.dev.statefulForward true in
example [SymmetricCategory C] [HasTensor X Y] [HasTensor Y X] :
    (braiding X Y).hom ≫ (braiding Y X).hom = 𝟙 _ := by
  dsimp [braiding]
  ext x i₁ i₂ hi' : 2
  dsimp [GradedObject] at X Y Z
  saturate [categoryOfGradedObjects_id]
  sorry

end CategoryTheory.GradedObject.Monoidal
