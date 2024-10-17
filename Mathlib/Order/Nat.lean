/-
Copyright (c) 2014 Floris van Doorn (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Leonardo de Moura, Jeremy Avigad, Mario Carneiro
-/
import Mathlib.Order.BoundedOrder

/-!
# The natural numbers form a linear order

This file contains the linear order instance on the natural numbers.

See note [foundational algebra order theory].
-/

namespace Nat

instance instLinearOrder : LinearOrder ℕ where
  le := Nat.le
  le_refl := @Nat.le_refl
  le_trans := @Nat.le_trans
  le_antisymm := @Nat.le_antisymm
  le_total := @Nat.le_total
  lt := Nat.lt
  lt_iff_le_not_le := @Nat.lt_iff_le_not_le
  decidableLT := inferInstance
  decidableLE := inferInstance
  decidableEq := inferInstance

instance instOrderBot : OrderBot ℕ where
  bot := 0
  bot_le := zero_le

instance instNoMaxOrder : NoMaxOrder ℕ where
  exists_gt n := ⟨n + 1, n.lt_succ_self⟩

/-! ### Miscellaneous lemmas -/

-- We want to use this lemma earlier than the lemma simp can prove it with
@[simp, nolint simpNF] protected lemma bot_eq_zero : ⊥ = 0 := rfl

end Nat
