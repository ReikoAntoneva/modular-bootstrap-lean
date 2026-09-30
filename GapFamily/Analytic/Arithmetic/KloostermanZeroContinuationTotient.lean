import GapFamily.Analytic.Arithmetic.KloostermanDirichletZero
import Mathlib.NumberTheory.LSeries.Convolution
import Mathlib.NumberTheory.LSeries.Dirichlet

/-!
# The convergent zero-spin Kloosterman series as a zeta quotient

Euler's divisor identity for the actual totient coefficients gives their
Dirichlet convolution with the constant sequence one. Multiplication of
genuinely convergent Dirichlet series then identifies the zero-spin series
with the zeta quotient in the open half-plane of absolute convergence.
No continuation value is assigned in this module.
-/

noncomputable section

namespace GapFamily.Analytic

/-- Euler's divisor identity as an equality of the actual coefficient convolution. -/
theorem totient_convolution_one :
    LSeries.convolution (fun c : ℕ => (Nat.totient c : ℂ)) 1 =
      fun c : ℕ => (c : ℂ) := by
  rw [LSeries.convolution_def]
  funext c
  simp only [Pi.one_apply, mul_one]
  rw [Nat.sum_divisorsAntidiagonal (fun a _ => (Nat.totient a : ℂ))]
  exact_mod_cast Nat.sum_totient c

/-- Multiplication of a coefficient by its index shifts the exponent by one. -/
theorem lSeries_natCast_eq_shift (z : ℂ) :
    LSeries (fun c : ℕ => (c : ℂ)) z = LSeries 1 (z - 1) := by
  unfold LSeries
  apply tsum_congr
  intro c
  by_cases hc : c = 0
  · simp [hc]
  · simp only [LSeries.term_of_ne_zero hc, Pi.one_apply]
    rw [Complex.cpow_sub _ _ (Nat.cast_ne_zero.mpr hc), Complex.cpow_one]
    simp

/-- Absolute convergence of the actual totient series for real part above two. -/
theorem totient_LSeriesSummable {z : ℂ} (hz : 2 < z.re) :
    LSeriesSummable (fun c : ℕ => (Nat.totient c : ℂ)) z :=
  (LSeriesSummable_congr z (fun {_} _ => kloostermanCoefficient_zero_zero _)).mp
    (kloostermanCoefficient_LSeriesSummable 0 0 hz)

/-- The exact Euler product relation, proved by absolutely convergent convolution. -/
theorem totient_LSeries_mul_zeta {z : ℂ} (hz : 2 < z.re) :
    LSeries (fun c : ℕ => (Nat.totient c : ℂ)) z * riemannZeta z =
      riemannZeta (z - 1) := by
  have hz₁ : 1 < z.re := by linarith
  have hzsub : 1 < (z - 1).re := by simp; linarith
  have h := LSeries_convolution' (totient_LSeriesSummable hz)
    (LSeriesSummable_one_iff.mpr hz₁)
  rw [totient_convolution_one, lSeries_natCast_eq_shift,
    LSeries_one_eq_riemannZeta hzsub, LSeries_one_eq_riemannZeta hz₁] at h
  exact h.symm

/-- The totient Dirichlet series equals the ratio of actual Riemann zeta functions. -/
theorem totient_LSeries_eq_zeta_div {z : ℂ} (hz : 2 < z.re) :
    LSeries (fun c : ℕ => (Nat.totient c : ℂ)) z =
      riemannZeta (z - 1) / riemannZeta z := by
  apply (eq_div_iff (riemannZeta_ne_zero_of_one_lt_re (by linarith))).mpr
  exact totient_LSeries_mul_zeta hz

/-- The all-zero Kloosterman Dirichlet series has the exact source normalization. -/
theorem kloostermanDirichlet_zero_zero_eq_zeta_div {s : ℂ} (hs : 1 < s.re) :
    kloostermanDirichlet 0 0 s = riemannZeta (2 * s - 1) / riemannZeta (2 * s) := by
  rw [kloostermanDirichlet_zero_zero_eq_totient_LSeries]
  apply totient_LSeries_eq_zeta_div
  simp only [Complex.mul_re]
  norm_num
  linarith

/-- The zeta quotient is the actual sum of the positive-denominator totient series. -/
theorem kloostermanDirichlet_zero_zero_zeta_hasSum {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun k : ℕ => (Nat.totient (k + 1) : ℂ) / (k + 1 : ℂ) ^ (2 * s))
      (riemannZeta (2 * s - 1) / riemannZeta (2 * s)) := by
  rw [← kloostermanDirichlet_zero_zero_eq_zeta_div hs]
  exact kloostermanDirichlet_zero_zero_hasSum hs

end GapFamily.Analytic
