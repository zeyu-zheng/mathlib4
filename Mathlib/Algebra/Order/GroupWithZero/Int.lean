/-
Copyright (c) 2025 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
import Mathlib.Algebra.GroupWithZero.Int
import Mathlib.Algebra.Order.GroupWithZero.Canonical

/-!
# Lemmas about `ℤₘ₀`.
-/

namespace WithZero

open Multiplicative

theorem ofAdd_neg_one_lt : ofAdd (-1 : ℤ) < (1 : ℤₘ₀) := by
  rw [← coe_one, coe_lt_coe, ← ofAdd_zero, ofAdd_lt]; omega

theorem ofAdd_neg_one_pow_lt {n : ℕ} {u : ℤₘ₀ˣ} :
    ofAdd (-1 : ℤ) ^ n < u.val ↔ -n < unitsMultiplicativeEquiv u := by
  rw [← lt_unitsMultiplicativeEquiv, ← ofAdd_neg_one_pow]
  simp

end WithZero
