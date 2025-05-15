/-
Copyright (c) 2025 María Inés de Frutos-Fernández, Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Filippo A. E. Nuccio
-/
import Mathlib.Algebra.Group.Int.TypeTags
import Mathlib.Algebra.Order.GroupWithZero.Canonical
import Mathlib.Tactic.ApplyFun

/-!
# Lemmas about `ℤₘ₀`.
-/

namespace WithZero

open Multiplicative

theorem ofAdd_zpow (a : ℤ) : (↑(ofAdd a) : ℤₘ₀) = ofAdd (1 : ℤ) ^ a := by
  rw [← WithZero.coe_zpow, WithZero.coe_inj, ← Int.ofAdd_mul, one_mul]

theorem ofAdd_neg_one_pow_comm (a : ℤ) (n : ℕ) :
    ((↑(ofAdd (-1 : ℤ)) : ℤₘ₀) ^ (-a)) ^ n = ofAdd (n : ℤ) ^ a := by
  rw [ofAdd_zpow (-1)]
  simp only [zpow_neg, zpow_one, inv_zpow', inv_inv, coe_zpow]
  rw [← zpow_natCast, zpow_comm, ← ofAdd_zpow]

theorem ofAdd_neg_one_lt : ofAdd (-1 : ℤ) < (1 : ℤₘ₀) := by
  rw [← coe_one, coe_lt_coe, ← ofAdd_zero, ofAdd_lt]; omega

theorem ofAdd_neg_one_pow (n : ℕ) : ofAdd (-1 : ℤ) ^ n = ofAdd (-n : ℤ) := by
  apply_fun toAdd
  simp

theorem ofAdd_neg_one_pow_lt {n : ℕ} {u : ℤₘ₀ˣ} :
    ofAdd (-1 : ℤ) ^ n < u.val ↔ -n < unitsMultiplicativeEquiv u := by
  rw [← lt_unitsMultiplicativeEquiv, ← ofAdd_neg_one_pow]
  simp

end WithZero
