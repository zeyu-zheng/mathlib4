/-
Copyright (c) 2025 Qi Wen Wei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qi Wen Wei
-/
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Digits
import Mathlib.Algebra.GeomSum
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.RingTheory.Multiplicity


/-!
# Natural number factorization

This file contains lemmas about the factorization function (the maximum prime power dividing a
number) when applied to naturals, in particular calculating it for factorials and binomial
coefficients.

This is a port of the lemmas from `Data/Nat/Multiplicity` to here,
re-written in terms of `factorization`


## Factorization calculations

* `Nat.Prime.factorization_factorial`: Legendre's Theorem. The factorization of `p` in `n!` is
  `n / p + ... + n / p ^ b` for any `b` such that `n / p ^ (b + 1) = 0`. See `padicValNat_factorial`
  for this result stated in the language of `p`-adic valuations and
  `sub_one_mul_padicValNat_factorial` for a factorization result.
* `Nat.Prime.factorization_factorial_mul`: The factorization of `p` in `(p * n)!` is `n` more than
  that of `n!`.
* `Nat.Prime.factorization_choose`: Kummer's Theorem. The factorization of `p` in `n.choose k`
   is the number of carries when `k` and `n - k` are added in base `p`.
   See `padicValNat_choose` for the same result but stated in the language of `p`-adic
   valuations and `sub_one_mul_padicValNat_choose_eq_sub_sum_digits` for a related result.

## Other declarations

* `Nat.factorization_eq_card_pow_dvd`: The factorization of `m` in `n` is the number of positive
  natural numbers `i` such that `m ^ i` divides `n`.

## Tags

Legendre, p-adic
-/

open Finset List Finsupp

namespace Nat

/-- The factorization of `m` in `n` is the number of positive natural numbers `i` such that `m ^ i`
divides `n`. Note `m` is prime. This set is expressed by filtering `Ico 1 b` where `b` is any bound
greater than `log m n`. -/
theorem factorization_eq_card_pow_dvd₀ {m n b : ℕ} (hm : m ≠ 1)
  (hm2: m.Prime) (hn : 0 < n) (hb : log m n < b) :
    n.factorization m = #{i ∈ Ico 1 b | m ^ i ∣ n} :=
  have fin := Nat.finiteMultiplicity_iff.2 ⟨hm, hn⟩
  calc
    n.factorization m = #(Ico 1 <| multiplicity m n + 1) := by {
      simp only [card_Ico, add_tsub_cancel_right]
      rw [← multiplicity_eq_factorization]
      · exact hm2
      exact not_eq_zero_of_lt hn
    }
    _ = #{i ∈ Ico 1 b | m ^ i ∣ n} := by {
      apply congr_arg _
      apply Finset.ext fun i => by {
        simp only [mem_Ico, Nat.lt_succ_iff,
          fin.pow_dvd_iff_le_multiplicity, Finset.mem_filter,
          and_assoc, and_congr_right_iff, iff_and_self]
        intro hi h
        rw [← fin.pow_dvd_iff_le_multiplicity] at h
        rcases m with - | m
        · rw [zero_pow, zero_dvd_iff] at h
          exacts [(hn.ne' h).elim, one_le_iff_ne_zero.1 hi]
        refine LE.le.trans_lt ?_ hb
        exact le_log_of_pow_le (one_lt_iff_ne_zero_and_ne_one.2 ⟨m.succ_ne_zero, hm⟩)
          (le_of_dvd hn h)
      }
    }

theorem factorization_mul₀ {p m n : ℕ} (hm: m ≠ 0) (hn: n ≠ 0):
    (m * n).factorization p = m.factorization p + n.factorization p := by {
  rw [factorization_mul hm hn]
  rfl
}

theorem factorization_pow₀ {p m n : ℕ} :
    (m ^ n).factorization p = n * m.factorization p := by {
  rw [factorization_pow]
  simp
}

theorem factorization_pow_self {p n : ℕ} (hp : p.Prime) : (p ^ n).factorization p = n := by {
  simp only [factorization_pow, coe_smul, Pi.smul_apply, smul_eq_mul]
  have h1: p.factorization p = 1 := by {
    exact Prime.factorization_self hp
  }
  rw [h1]
  simp
}

/-- **Legendre's Theorem**

The multiplicity of a prime in `n!` is the sum of the quotients `n / p ^ i`. This sum is expressed
over the finset `Ico 1 b` where `b` is any bound greater than `log p n`. -/
theorem factorization_factorial {p : ℕ} (hp : p.Prime) :
  ∀ {n b : ℕ}, log p n < b → (n !).factorization p = (∑ i ∈ Ico 1 b, n / p ^ i : ℕ)
  | 0, b, _ => by simp only [factorial_zero, factorization_one, coe_zero, Pi.zero_apply,
    Nat.zero_div, sum_const_zero]
  | n + 1, b, hb =>
    calc
      ((n + 1)!).factorization p = ( (n + 1) * (n !)).factorization p := by
        rw [← factorial_succ]
      _ = (n + 1).factorization p + (n !).factorization p := by
        have p1: n + 1 ≠ 0 := by exact Ne.symm (zero_ne_add_one n)
        apply factorization_mul₀ p1 (factorial_ne_zero n)
      _ = #{i ∈ Ico 1 b | p ^ i ∣ n + 1} + (∑ i ∈ Ico 1 b, n / p ^ i : ℕ) := by
        rw [factorization_factorial hp ((log_mono_right <| le_succ _).trans_lt hb)]
        simp only [add_left_inj]
        apply factorization_eq_card_pow_dvd₀ (Prime.ne_one hp) hp (zero_lt_succ n)
        exact hb
      _ = (∑ i ∈ Ico 1 b, n / p ^ i : ℕ) + #{i ∈ Ico 1 b | p ^ i ∣ n + 1} := by
        exact
          Nat.add_comm (#(Finset.filter (fun i ↦ p ^ i ∣ n + 1) (Ico 1 b)))
            (∑ i ∈ Ico 1 b, n / p ^ i)
      _ = (∑ i ∈ Ico 1 b, (n / p ^ i + if p ^ i ∣ n + 1 then 1 else 0) : ℕ) := by
        rw [sum_add_distrib, sum_boole]
        simp
      _ = (∑ i ∈ Ico 1 b, (n + 1) / p ^ i : ℕ) :=
        Finset.sum_congr rfl fun _ _ => (succ_div _ _).symm

/-- For a prime number `p`, taking `(p - 1)` times the factorization of `p` in `n!` equals `n` minus
the sum of base `p` digits of `n`. -/
theorem sub_one_mul_factorization_factorial {n p : ℕ} (hp : p.Prime) :
    (p - 1) * (n !).factorization p = n - (p.digits n).sum := by {
  simp only [factorization_factorial hp <| lt_succ_of_lt <| lt.base (log p n),
    ← Finset.sum_Ico_add' _ 0 _ 1, Ico_zero_eq_range, ←
    sub_one_mul_sum_log_div_pow_eq_sub_sum_digits]
}

/-- Modified version of `factorization_prod` that accounts for inputs. -/
theorem factorization_prod₀ {α : Type*} {p : ℕ}
{S : Finset α} {g : α → ℕ} (hS : ∀ x ∈ S, g x ≠ 0) :
    (S.prod g).factorization p = S.sum fun x => (g x).factorization p := by {
  rw [factorization_prod (fun x a ↦ hS x a)]
  exact finset_sum_apply S (fun i ↦ (g i).factorization) p
}

/-- The factorization of `p` in `(p * (n + 1))!` is one more than the sum
  of the factorizations of `p` in `(p * n)!` and `n + 1`. -/
theorem factorization_factorial_mul_succ {n p : ℕ} (hp : p.Prime) :
    ((p * (n + 1))!).factorization p =
    ((p * n)!).factorization p + (n + 1).factorization p + 1 := by {
  have h0 : 2 ≤ p := hp.two_le
  have h1 : 1 ≤ p * n + 1 := Nat.le_add_left _ _
  have h2 : p * n + 1 ≤ p * (n + 1) := by linarith
  have h3 : p * n + 1 ≤ p * (n + 1) + 1 := by omega
  have h4 : ∀ m ∈ Ico (p * n + 1) (p * (n + 1)), m.factorization p = 0 := by {
    intro m hm
    apply factorization_eq_zero_of_not_dvd
    have a1: m ≥ p * n + 1 ∧ m < p * (n + 1) := by {
      exact mem_Ico.mp hm
    }
    have a2: m > p * n := by {
      have a3: m ≥ p * n + 1 := a1.left
      exact a3
    }
    have a3: m < p * (n + 1) := a1.right
    exact not_dvd_of_between_consec_multiples a2 a3
  }
  have hS : ∀ x ∈ (Ico 1 (p * (n + 1) + 1)), x ≠ 0 := by {
    intro a1 a2 contra1
    have contra2: a1 ≥ 1 := by {
      exact (Finset.mem_Ico.mp a2).left
    }
    rw [contra1] at contra2
    contradiction
  }
  have hS2 : ∀ x ∈ (Ico 1 (p * n + 1)), x ≠ 0 := by {
    intro a1 a2 contra1
    have contra2: a1 ≥ 1 := by {
      exact (Finset.mem_Ico.mp a2).left
    }
    rw [contra1] at contra2
    contradiction
  }
  simp_rw [← prod_Ico_id_eq_factorial, factorization_prod₀ hS, ← sum_Ico_consecutive _ h1 h3,
    add_assoc]
  rw [sum_Ico_succ_top h2]
  have h6: p ≠ 0 := by exact not_eq_zero_of_lt h0
  have h7: n + 1 ≠ 0 := by exact Ne.symm (zero_ne_add_one n)
  rw [factorization_prod₀ hS2]
  rw [factorization_mul₀ h6 h7, Prime.factorization_self hp,
    sum_congr rfl h4, sum_const_zero, zero_add, add_comm 1]
}

/-- The factorization of `p` in `(p * n)!` is `n` more than that of `n!`. -/
theorem factorization_factorial_mul {n p : ℕ} (hp : p.Prime) :
    ((p * n)!).factorization p = (n !).factorization p + n := by
  induction' n with n ih
  · simp
  · simp only [hp, factorization_factorial_mul_succ, ih, factorial_succ,
    cast_add, cast_one, ← add_assoc]
    congr 1
    rw [factorization_mul₀ (Ne.symm (zero_ne_add_one n)) (factorial_ne_zero n)]
    ring


theorem factorization_factorial_le_div_pred {p : ℕ} (hp : p.Prime) (n : ℕ) :
    (n !).factorization p ≤ (n / (p - 1) : ℕ) := by
  have h1 : log p n < (log p n).succ := by exact Nat.lt_add_one (log p n)
  rw [factorization_factorial hp (h1)]
  exact Nat.geom_sum_Ico_le hp.two_le _ _

theorem multiplicity_choose_aux {p n b k : ℕ} (hp : p.Prime) (hkn : k ≤ n) :
    ∑ i ∈ Finset.Ico 1 b, n / p ^ i =
      ((∑ i ∈ Finset.Ico 1 b, k / p ^ i) + ∑ i ∈ Finset.Ico 1 b, (n - k) / p ^ i) +
        #{i ∈ Ico 1 b | p ^ i ≤ k % p ^ i + (n - k) % p ^ i} :=
  calc
    ∑ i ∈ Finset.Ico 1 b, n / p ^ i = ∑ i ∈ Finset.Ico 1 b, (k + (n - k)) / p ^ i := by
      simp only [add_tsub_cancel_of_le hkn]
    _ = ∑ i ∈ Finset.Ico 1 b,
          (k / p ^ i + (n - k) / p ^ i + if p ^ i ≤ k % p ^ i + (n - k) % p ^ i then 1 else 0) := by
      simp only [Nat.add_div (pow_pos hp.pos _)]
    _ = _ := by simp [sum_add_distrib, sum_boole]


/-- The factorization of `p` in `choose (n + k) k` is the number of carries when `k` and `n`
  are added in base `p`. The set is expressed by filtering `Ico 1 b` where `b`
  is any bound greater than `log p (n + k)`. -/
theorem factorization_choose' {p n k b : ℕ} (hp : p.Prime) (hnb : log p (n + k) < b) :
    (choose (n + k) k).factorization p = #{i ∈ Ico 1 b | p ^ i ≤ k % p ^ i + n % p ^ i} := by
  have h₁ :
      (choose (n + k) k).factorization p +  (k ! * n !).factorization p =
        #{i ∈ Ico 1 b | p ^ i ≤ k % p ^ i + n % p ^ i} + (k ! * n !).factorization p := by
    rw [← factorization_mul₀, ← mul_assoc]
    have h2:= (add_tsub_cancel_right n k) ▸ choose_mul_factorial_mul_factorial (le_add_left k n)
    rw [h2, factorization_factorial hp hnb, factorization_mul₀,
      factorization_factorial hp ((log_mono_right (le_add_left k n)).trans_lt hnb),
      factorization_factorial hp ((log_mono_right (le_add_left n k)).trans_lt
      (add_comm n k ▸ hnb)), multiplicity_choose_aux hp (le_add_left k n)]
    simp [add_comm]
    exact factorial_ne_zero k
    exact factorial_ne_zero n
    · intro h
      rw [Nat.choose_eq_zero_iff] at h
      omega
    · have h1 : n ! ≠ 0 := by exact factorial_ne_zero n
      have h2 : k ! ≠ 0 := by exact factorial_ne_zero k
      exact Nat.mul_ne_zero h2 h1
  exact Nat.add_right_cancel h₁

/-- The factorization of `p` in `choose n k` is the number of carries when `k` and `n - k`
  are added in base `p`. The set is expressed by filtering `Ico 1 b` where `b`
  is any bound greater than `log p n`. -/
theorem factorization_choose {p n k b : ℕ} (hp : p.Prime) (hkn : k ≤ n) (hnb : log p n < b) :
    (choose n k).factorization p = #{i ∈ Ico 1 b | p ^ i ≤ k % p ^ i + (n - k) % p ^ i} := by
  have := Nat.sub_add_cancel hkn
  convert @factorization_choose' p (n - k) k b hp _
  · exact id (Eq.symm this)
  · rw [this]
    exact hnb


/-- Modified version of `emultiplicity_le_emultiplicity_of_dvd_right`
but for factorization.
-/
theorem factorization_le_factorization_of_dvd_right {a b c : ℕ} (h : b ∣ c)
(hb: b ≠ 0) (hc: c ≠ 0):
    b.factorization a ≤ c.factorization a := by {
  rcases h with ⟨k, hk⟩
  rw [hk]
  have h2 : k ≠ 0 := by {
    intro k1
    rw [k1, mul_zero] at hk
    tauto
  }
  rw [factorization_mul₀ hb h2]
  simp only [le_add_iff_nonneg_right, _root_.zero_le]
}

/-- A lower bound on the factorization of `p` in `choose n k`.
 -/
theorem factorization_le_factorization_choose_add {p : ℕ} :
    ∀ n k : ℕ, (k ≤ n) ∧ (k ≠ 0) →
    n.factorization p ≤ (choose n k).factorization p + k.factorization p
  | n, 0 => by {
    intro h
    tauto
  }
  | 0, x + 1 => by simp
  | n + 1, k + 1 => by
    intro h
    have h0: (n + 1).choose (k + 1) ≠ 0 := by {
      intro h2
      rw [choose_eq_zero_iff] at h2
      omega
    }
    rw [← factorization_mul₀ h0 (Ne.symm (zero_ne_add_one k))]
    have h1: (n + 1) ≠ 0 := by {
      exact Ne.symm (zero_ne_add_one n)
    }
    have h2: (n + 1).choose (k + 1) * (k + 1) ≠ 0 := by {
      have h3: (k + 1) ≠ 0 := by exact Ne.symm (zero_ne_add_one k)
      exact Nat.mul_ne_zero h0 h3
    }
    refine factorization_le_factorization_of_dvd_right ?_ h1 h2
    rw [← succ_mul_choose_eq]
    exact dvd_mul_right _ _

variable {p n k : ℕ}

theorem factorization_choose_prime_pow_add_factorization (hp : p.Prime) (hkn : k ≤ p ^ n)
    (hk0 : k ≠ 0) : (choose (p ^ n) k).factorization p + k.factorization p = n := by {
  apply le_antisymm
  · have hdisj :
      Disjoint {i ∈ Ico 1 n.succ | p ^ i ≤ k % p ^ i + (p ^ n - k) % p ^ i}
        {i ∈ Ico 1 n.succ | p ^ i ∣ k} := by
      simp +contextual [Finset.disjoint_right, *, dvd_iff_mod_eq_zero,
        Nat.mod_lt _ (pow_pos hp.pos _)]
    rw [factorization_choose hp hkn (lt_succ_self _),
        factorization_eq_card_pow_dvd₀ (ne_of_gt hp.one_lt) hp hk0.bot_lt
          (lt_succ_of_le (log_mono_right hkn))]
    rw [log_pow hp.one_lt, ← card_union_of_disjoint hdisj, filter_union_right]
    have filter_le_Ico := (Ico 1 n.succ).card_filter_le
      fun x => p ^ x ≤ k % p ^ x + (p ^ n - k) % p ^ x ∨ p ^ x ∣ k
    rwa [card_Ico 1 n.succ] at filter_le_Ico
  · have h1: (p ^ n).factorization p = n := by {
      exact factorization_pow_self hp
    }
    nth_rewrite 1 [← h1]
    have h3: k ≤ p ^ n ∧ k ≠ 0 := ⟨hkn, hk0⟩
    exact factorization_le_factorization_choose_add (p^n) k h3
}

theorem factorization_choose_prime_pow {p n k : ℕ} (hp : p.Prime) (hkn : k ≤ p ^ n) (hk0 : k ≠ 0) :
    (choose (p ^ n) k).factorization p = ↑(n - k.factorization p) := by {
  nth_rewrite 2 [← factorization_choose_prime_pow_add_factorization hp hkn hk0]
  rw [Nat.add_sub_cancel_right]
}

end Nat
