/-
Copyright (c) 2024 Calle Sönne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Lezeau, Calle Sönne
-/

import Mathlib.CategoryTheory.FiberedCategory.Pseudofunctor

/-!
# Fibered category associated to a presheaf

In this file we associate to any presheaf valued in types `F : 𝒮ᵒᵖ ⥤ Type _` a fibered
category `∫ F ⥤ 𝒮`. We obtain this as a special case of the Grothendieck construction, which
associates a fibered category to any pseudofunctor `F : 𝒮ᵒᵖ ⥤ Cat _`.

## References
[Vistoli2008] "Notes on Grothendieck Topologies, Fibered Categories and Descent Theory" by
Angelo Vistoli

-/

universe u₁ v₁ u₂ v₂ u₃ w

open CategoryTheory Functor Category Opposite Discrete

namespace Presheaf

variable {𝒮 : Type u₁} [Category 𝒮] {F : 𝒮ᵒᵖ ⥤ Type u₃}

/-
Plan:

need to get "toPseudofunctor" (making target valued in Cat)!

then get everything generally

but need new HasFibers instance!

-/

#check Functor.toPseudoFunctor F

end Presheaf
