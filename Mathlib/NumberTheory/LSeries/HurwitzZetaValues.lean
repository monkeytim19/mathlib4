/-
Copyright (c) 2024 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/

import Mathlib.NumberTheory.ZetaValues
import Mathlib.NumberTheory.LSeries.HurwitzZeta

/-!
# Special values of Hurwitz zeta functions

This file gives the formulae for values of Hurwitz zeta functions at negative integers in terms
of Bernoulli polynomials.

(Note that most of the actual work for these formulae is done elsewhere, in
`Mathlib.NumberTheory.ZetaValues`. This file has only those results which really need the
definition of Hurwitz zeta and related functions, rather than working directly with the defining
sums in the convergence range.)

## Main results

- `hurwitzZeta_neg_nat`: for `k : ℕ` with `k ≠ 0`, and any `x ∈ ℝ / ℤ`, the special value
  `hurwitzZeta x (-k)` is equal to `-(Polynomial.bernoulli (k + 1) x) / (k + 1)`.

## TODO

* Derive the special case of the Riemann zeta function from these results (rather than proving it
  separately). This will come in a future PR which will re-implement Riemann zeta as a special
  case of Hurwitz zeta.
* Extend to cover Dirichlet L-functions.
* The formulae are correct for `s = 0` as well, but we do not prove this case, since this requires
  Fourier series which are only conditionally convergent, which is difficult to approach using the
  methods in the library at the present time (May 2024).
-/

open Complex Real Set

open scoped Nat

namespace HurwitzZeta

variable {k : ℕ} {x : ℝ}

/-- Express the value of `cosZeta` at a positive even integer as a value
of the Bernoulli polynomial. -/
theorem cosZeta_two_mul_nat (hk : k ≠ 0) (hx : x ∈ Icc 0 1) :
    cosZeta x (2 * k) = (-1) ^ (k + 1) * (2 * π) ^ (2 * k) / 2 / (2 * k)! *
      ((Polynomial.bernoulli (2 * k)).map (algebraMap ℚ ℂ)).eval (x : ℂ) := by
  rw [← (hasSum_nat_cosZeta x (?_ : 1 < re (2 * k))).tsum_eq]
  refine Eq.trans ?_ <| (congr_arg ofReal' (hasSum_one_div_nat_pow_mul_cos hk hx).tsum_eq).trans ?_
  · rw [ofReal_tsum]
    refine tsum_congr fun n ↦ ?_
    rw [mul_comm (1 / _), mul_one_div, ofReal_div, mul_assoc (2 * π), mul_comm x n, ← mul_assoc,
      ← Nat.cast_ofNat (R := ℂ), ← Nat.cast_mul, cpow_natCast, ofReal_pow, ofReal_natCast]
  · simp only [ofReal_mul, ofReal_div, ofReal_pow, ofReal_natCast, ofReal_ofNat,
      ofReal_neg, ofReal_one]
    congr 1
    have : (Polynomial.bernoulli (2 * k)).map (algebraMap ℚ ℂ) = _ :=
      (Polynomial.map_map (algebraMap ℚ ℝ) ofReal _).symm
    rw [this, ← ofReal_eq_coe, ← ofReal_eq_coe]
    apply Polynomial.map_aeval_eq_aeval_map
    simp only [Algebra.id.map_eq_id, RingHomCompTriple.comp_eq]
  · rw [← Nat.cast_ofNat, ← Nat.cast_one, ← Nat.cast_mul, natCast_re, Nat.cast_lt]
    omega

/--
Express the value of `sinZeta` at an odd integer `> 1` as a value of the Bernoulli polynomial.

Note that this formula is also correct for `k = 0` (i.e. for the value at `s = 1`), but we do not
prove it in this case, owing to the additional difficulty of working with series that are only
conditionally convergent.
-/
theorem sinZeta_two_mul_nat_add_one (hk : k ≠ 0) (hx : x ∈ Icc 0 1) :
    sinZeta x (2 * k + 1) = (-1) ^ (k + 1) * (2 * π) ^ (2 * k + 1) / 2 / (2 * k + 1)! *
      ((Polynomial.bernoulli (2 * k + 1)).map (algebraMap ℚ ℂ)).eval (x : ℂ) := by
  rw [← (hasSum_nat_sinZeta x (?_ : 1 < re (2 * k + 1))).tsum_eq]
  refine Eq.trans ?_ <| (congr_arg ofReal' (hasSum_one_div_nat_pow_mul_sin hk hx).tsum_eq).trans ?_
  · rw [ofReal_tsum]
    refine tsum_congr fun n ↦ ?_
    rw [mul_comm (1 / _), mul_one_div, ofReal_div, mul_assoc (2 * π), mul_comm x n, ← mul_assoc]
    congr 1
    rw [← Nat.cast_ofNat, ← Nat.cast_mul, ← Nat.cast_add_one, cpow_natCast, ofReal_pow,
      ofReal_natCast]
  · simp only [ofReal_mul, ofReal_div, ofReal_pow, ofReal_natCast, ofReal_ofNat,
      ofReal_neg, ofReal_one]
    congr 1
    have : (Polynomial.bernoulli (2 * k + 1)).map (algebraMap ℚ ℂ) = _ :=
      (Polynomial.map_map (algebraMap ℚ ℝ) ofReal _).symm
    rw [this, ← ofReal_eq_coe, ← ofReal_eq_coe]
    apply Polynomial.map_aeval_eq_aeval_map
    simp only [Algebra.id.map_eq_id, RingHomCompTriple.comp_eq]
  · rw [← Nat.cast_ofNat, ← Nat.cast_one, ← Nat.cast_mul, ← Nat.cast_add_one, natCast_re,
      Nat.cast_lt, lt_add_iff_pos_left]
    exact mul_pos two_pos (Nat.pos_of_ne_zero hk)

/-- Reformulation of `cosZeta_two_mul_nat` using `Gammaℂ`. -/
theorem cosZeta_two_mul_nat' (hk : k ≠ 0) (hx : x ∈ Icc (0 : ℝ) 1) :
    cosZeta x (2 * k) = (-1) ^ (k + 1) / (2 * k) / Gammaℂ (2 * k) *
      ((Polynomial.bernoulli (2 * k)).map (algebraMap ℚ ℂ)).eval (x : ℂ) := by
  rw [cosZeta_two_mul_nat hk hx]
  congr 1
  have : (2 * k)! = (2 * k) * Complex.Gamma (2 * k) := by
    rw [(by { norm_cast; omega } : 2 * (k : ℂ) = ↑(2 * k - 1) + 1), Complex.Gamma_nat_eq_factorial,
      ← Nat.cast_add_one, ← Nat.cast_mul, ← Nat.factorial_succ, Nat.sub_add_cancel (by omega)]
  simp_rw [this, Gammaℂ, cpow_neg, ← div_div, div_inv_eq_mul, div_mul_eq_mul_div, div_div]
  norm_cast
  ring_nf

/-- Reformulation of `sinZeta_two_mul_nat_add_one` using `Gammaℂ`. -/
theorem sinZeta_two_mul_nat_add_one' (hk : k ≠ 0) (hx : x ∈ Icc (0 : ℝ) 1) :
    sinZeta x (2 * k + 1) = (-1) ^ (k + 1) / (2 * k + 1) / Gammaℂ (2 * k + 1) *
      ((Polynomial.bernoulli (2 * k + 1)).map (algebraMap ℚ ℂ)).eval (x : ℂ) := by
  rw [sinZeta_two_mul_nat_add_one hk hx]
  congr 1
  have : (2 * k + 1)! = (2 * k + 1) * Complex.Gamma (2 * k + 1) := by
    rw [(by simp : Complex.Gamma (2 * k + 1) = Complex.Gamma (↑(2 * k) + 1)),
       Complex.Gamma_nat_eq_factorial, ← Nat.cast_ofNat (R := ℂ), ← Nat.cast_mul,
      ← Nat.cast_add_one, ← Nat.cast_mul, ← Nat.factorial_succ]
  simp_rw [this, Gammaℂ, cpow_neg, ← div_div, div_inv_eq_mul, div_mul_eq_mul_div, div_div]
  rw [(by simp : 2 * (k : ℂ) + 1 = ↑(2 * k + 1)), cpow_natCast]
  ring

theorem hurwitzZetaEven_one_sub_two_mul_nat (hk : k ≠ 0) (hx : x ∈ Icc (0 : ℝ) 1) :
    hurwitzZetaEven x (1 - 2 * k) =
      -1 / (2 * k) * ((Polynomial.bernoulli (2 * k)).map (algebraMap ℚ ℂ)).eval (x : ℂ) := by
  have h1 (n : ℕ) : (2 * k : ℂ) ≠ -n := by
    rw [← Int.cast_ofNat, ← Int.cast_natCast, ← Int.cast_mul, ← Int.cast_natCast n, ← Int.cast_neg,
      Ne, Int.cast_inj, ← Ne]
    refine ne_of_gt ((neg_nonpos_of_nonneg n.cast_nonneg).trans_lt (mul_pos two_pos ?_))
    exact Nat.cast_pos.mpr (Nat.pos_of_ne_zero hk)
  have h2 : (2 * k : ℂ) ≠ 1 := by norm_cast; simp only [mul_eq_one, OfNat.ofNat_ne_one,
    false_and, not_false_eq_true]
  have h3 : Gammaℂ (2 * k) ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero two_ne_zero ?_) (Gamma_ne_zero h1)
    simp only [ne_eq, cpow_eq_zero_iff, mul_eq_zero, OfNat.ofNat_ne_zero, ofReal_eq_zero,
      pi_ne_zero, Nat.cast_eq_zero, false_or, false_and, not_false_eq_true]
  rw [hurwitzZetaEven_one_sub _ h1 (Or.inr h2), ← Gammaℂ, cosZeta_two_mul_nat' hk hx, ← mul_assoc,
    ← mul_div_assoc, mul_assoc, mul_div_cancel_left₀ _ h3, ← mul_div_assoc]
  congr 2
  rw [mul_div_assoc, mul_div_cancel_left₀ _ two_ne_zero, ← ofReal_natCast, ← ofReal_mul,
    ← ofReal_cos, mul_comm π, ← sub_zero (k * π), cos_nat_mul_pi_sub, Real.cos_zero, mul_one,
    ofReal_pow, ofReal_neg, ofReal_one, pow_succ, mul_neg_one, mul_neg, ← mul_pow, neg_one_mul,
    neg_neg, one_pow]

theorem hurwitzZetaOdd_neg_two_mul_nat (hk : k ≠ 0) (hx : x ∈ Icc (0 : ℝ) 1) :
    hurwitzZetaOdd x (-(2 * k)) =
    -1 / (2 * k + 1) * ((Polynomial.bernoulli (2 * k + 1)).map (algebraMap ℚ ℂ)).eval (x : ℂ) := by
  have h1 (n : ℕ) : (2 * k + 1 : ℂ) ≠ -n := by
    rw [← Int.cast_ofNat, ← Int.cast_natCast, ← Int.cast_mul, ← Int.cast_natCast n, ← Int.cast_neg,
      ← Int.cast_one, ← Int.cast_add, Ne, Int.cast_inj, ← Ne]
    refine ne_of_gt ((neg_nonpos_of_nonneg n.cast_nonneg).trans_lt ?_)
    positivity
  have h3 : Gammaℂ (2 * k + 1) ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero two_ne_zero ?_) (Gamma_ne_zero h1)
    simp only [ne_eq, cpow_eq_zero_iff, mul_eq_zero, OfNat.ofNat_ne_zero, ofReal_eq_zero,
      pi_ne_zero, Nat.cast_eq_zero, false_or, false_and, not_false_eq_true]
  rw [(by simp : -(2 * k : ℂ) = 1 - (2 * k + 1)),
    hurwitzZetaOdd_one_sub _ h1, ← Gammaℂ, sinZeta_two_mul_nat_add_one' hk hx, ← mul_assoc,
    ← mul_div_assoc, mul_assoc, mul_div_cancel_left₀ _ h3, ← mul_div_assoc]
  congr 2
  rw [mul_div_assoc, add_div, mul_div_cancel_left₀ _ two_ne_zero, ← ofReal_natCast,
    ← ofReal_one, ← ofReal_ofNat, ← ofReal_div, ← ofReal_add, ← ofReal_mul,
    ← ofReal_sin, mul_comm π, add_mul, mul_comm (1 / 2), mul_one_div, Real.sin_add_pi_div_two,
    ← sub_zero (k * π), cos_nat_mul_pi_sub, Real.cos_zero, mul_one,
    ofReal_pow, ofReal_neg, ofReal_one, pow_succ, mul_neg_one, mul_neg, ← mul_pow, neg_one_mul,
    neg_neg, one_pow]

-- private because it is superseded by `hurwitzZeta_neg_nat` below
private lemma hurwitzZeta_one_sub_two_mul_nat (hk : k ≠ 0) (hx : x ∈ Icc (0 : ℝ) 1) :
    hurwitzZeta x (1 - 2 * k) =
      -1 / (2 * k) * ((Polynomial.bernoulli (2 * k)).map (algebraMap ℚ ℂ)).eval (x : ℂ) := by
  suffices hurwitzZetaOdd x (1 - 2 * k) = 0 by
    rw [hurwitzZeta, this, add_zero, hurwitzZetaEven_one_sub_two_mul_nat hk hx]
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
  rw [Nat.cast_succ, show (1 : ℂ) - 2 * (k + 1) = - 2 * k - 1 by ring,
    hurwitzZetaOdd_neg_two_mul_nat_sub_one]

-- private because it is superseded by `hurwitzZeta_neg_nat` below
private lemma hurwitzZeta_neg_two_mul_nat (hk : k ≠ 0) (hx : x ∈ Icc (0 : ℝ) 1) :
    hurwitzZeta x (-(2 * k)) = -1 / (2 * k + 1) *
      ((Polynomial.bernoulli (2 * k + 1)).map (algebraMap ℚ ℂ)).eval (x : ℂ) := by
  suffices hurwitzZetaEven x (-(2 * k)) = 0 by
    rw [hurwitzZeta, this, zero_add, hurwitzZetaOdd_neg_two_mul_nat hk hx]
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
  simpa only [Nat.cast_succ, ← neg_mul] using hurwitzZetaEven_neg_two_mul_nat_add_one x k

/-- Values of Hurwitz zeta functions at (strictly) negative integers.

TODO: This formula is also correct for `k = 0`; but our current proof does not work in this
case. -/
theorem hurwitzZeta_neg_nat (hk : k ≠ 0) (hx : x ∈ Icc (0 : ℝ) 1) :
    hurwitzZeta x (-k) =
    -1 / (k + 1) * ((Polynomial.bernoulli (k + 1)).map (algebraMap ℚ ℂ)).eval (x : ℂ) := by
  rcases Nat.even_or_odd' k with ⟨n, (rfl | rfl)⟩
  · exact_mod_cast hurwitzZeta_neg_two_mul_nat (by omega : n ≠ 0) hx
  · exact_mod_cast hurwitzZeta_one_sub_two_mul_nat (by omega : n + 1 ≠ 0) hx

end HurwitzZeta
