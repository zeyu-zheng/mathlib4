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

namespace WithZeroMulInt

open Multiplicative WithZero

theorem ofAdd_neg_one_lt : ofAdd (-1 : ℤ) < (unitsMultiplicativeEquiv.symm (0 : ℤ)).val := by
  simp only [unitsMultiplicativeEquiv_symm_zero, Units.val_one]
  rw [← coe_one, coe_lt_coe, ← ofAdd_zero, ofAdd_lt]; omega

theorem ofAdd_neg_one_pow_lt {n : ℕ} {u : ℤₘ₀ˣ} :
    ofAdd (-1 : ℤ) ^ n < u.val ↔ -n < unitsMultiplicativeEquiv u := by
  rw [← lt_unitsMultiplicativeEquiv, ← ofAdd_neg_one_pow]
  simp

end WithZeroMulInt
