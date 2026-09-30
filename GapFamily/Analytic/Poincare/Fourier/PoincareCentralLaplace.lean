import GapFamily.Analytic.Bessel.Bessel
import GapFamily.Analytic.Foundation.ReferenceMeasure
import GapFamily.Analytic.Poincare.Arithmetic.PoincareCentralQuotient
import GapFamily.Analytic.Poincare.PoincareScalarIdentification
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# The central physical Laplace integral

The nonzero-spin reference measure is exactly the measure appearing in the
order-zero Bessel integral after the change of variable `E = |j| v`.
-/

noncomputable section

namespace GapFamily.Analytic

open Real Set MeasureTheory

private theorem referenceDensity_scale {j : ℤ} (hj : j ≠ 0) (v : ℝ) :
    referenceDensity j (|(j : ℝ)| * v) =
      |(j : ℝ)|⁻¹ / Real.sqrt (v ^ 2 - 1) := by
  have ha : 0 < |(j : ℝ)| := abs_pos.mpr (Int.cast_ne_zero.mpr hj)
  unfold referenceDensity
  rw [show (|(j : ℝ)| * v) ^ 2 - (j : ℝ) ^ 2 =
      |(j : ℝ)| ^ 2 * (v ^ 2 - 1) by rw [mul_pow]; simp only [sq_abs]; ring,
    Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq ha.le]
  simp [div_eq_mul_inv, mul_inv_rev, mul_comm]

private theorem referenceLaplace_scale {j : ℤ} (hj : j ≠ 0) (t v : ℝ) :
    Real.exp (-t * (|(j : ℝ)| * v)) * referenceDensity j (|(j : ℝ)| * v) =
      |(j : ℝ)|⁻¹ * besselK0Integrand (t * |(j : ℝ)|) v := by
  rw [referenceDensity_scale hj]
  unfold besselK0Integrand
  rw [show -t * (|(j : ℝ)| * v) = -(t * |(j : ℝ)|) * v by ring]
  ring

/-- A positive exponential is ordinarily integrable against the physical
reference measure in every nonzero spin. -/
theorem integrable_exp_neg_referenceMeasure {j : ℤ} (hj : j ≠ 0)
    {t : ℝ} (ht : 0 < t) :
    Integrable (fun E : ℝ => Real.exp (-t * E)) (referenceMeasure j) := by
  have ha : 0 < |(j : ℝ)| := abs_pos.mpr (Int.cast_ne_zero.mpr hj)
  have hi := (besselK0_integrable (mul_pos ht ha)).const_mul |(j : ℝ)|⁻¹
  have hs : IntegrableOn
      (fun v : ℝ => Real.exp (-t * (|(j : ℝ)| * v)) *
        referenceDensity j (|(j : ℝ)| * v)) (Ioi 1) := by
    simpa only [referenceLaplace_scale hj, IntegrableOn] using hi
  have he := (integrableOn_Ioi_comp_mul_left_iff
    (fun E : ℝ => Real.exp (-t * E) * referenceDensity j E) 1 ha).mp hs
  rw [referenceMeasure, integrable_withDensity_iff_integrable_smul'
    (measurable_referenceDensity j).ennreal_ofReal
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simpa only [ENNReal.toReal_ofReal (referenceDensity_nonneg j _), smul_eq_mul,
    mul_comm, mul_one, IntegrableOn] using he

/-- Exact Laplace transform of the nonzero-spin reference measure. -/
theorem integral_exp_neg_referenceMeasure {j : ℤ} (hj : j ≠ 0) (t : ℝ) :
    (∫ E : ℝ, Real.exp (-t * E) ∂referenceMeasure j) =
      besselK0 (t * |(j : ℝ)|) := by
  have ha : 0 < |(j : ℝ)| := abs_pos.mpr (Int.cast_ne_zero.mpr hj)
  rw [referenceMeasure, integral_withDensity_eq_integral_toReal_smul
    (measurable_referenceDensity j).ennreal_ofReal
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (referenceDensity_nonneg j _), smul_eq_mul]
  have hs := integral_comp_mul_left_Ioi'
    (fun E : ℝ => Real.exp (-t * E) * referenceDensity j E) 1 ha
  simp_rw [referenceLaplace_scale hj] at hs
  simp only [mul_one, integral_const_mul, smul_eq_mul,
    ← mul_assoc, mul_inv_cancel₀ ha.ne', one_mul] at hs
  simpa only [mul_comm, besselK0] using hs.symm

/-- Complex-valued ordinary integrability of the same physical Laplace kernel. -/
theorem integrable_cexp_neg_referenceMeasure {j : ℤ} (hj : j ≠ 0)
    {t : ℝ} (ht : 0 < t) :
    Integrable (fun E : ℝ => Complex.exp (-(t : ℂ) * E)) (referenceMeasure j) := by
  have hi : Integrable (fun E : ℝ => (Real.exp (-t * E) : ℂ)) (referenceMeasure j) :=
    (integrable_exp_neg_referenceMeasure hj ht).ofReal
  simpa only [← Complex.ofReal_neg, ← Complex.ofReal_mul, ← Complex.ofReal_exp] using hi

/-- The complex physical Laplace transform equals the embedded real Bessel integral. -/
theorem integral_cexp_neg_referenceMeasure {j : ℤ} (hj : j ≠ 0) (t : ℝ) :
    (∫ E : ℝ, Complex.exp (-(t : ℂ) * E) ∂referenceMeasure j) =
      (besselK0 (t * |(j : ℝ)|) : ℂ) := by
  simp only [← Complex.ofReal_neg, ← Complex.ofReal_mul, ← Complex.ofReal_exp]
  rw [integral_complex_ofReal, integral_exp_neg_referenceMeasure hj]

/-- The central physical Laplace integral converges at every positive height. -/
theorem integrable_centralLaplace_referenceMeasure {y : ℝ} (hy : 0 < y)
    {j : ℤ} (hj : j ≠ 0) :
    Integrable (fun E : ℝ => Complex.exp (-2 * (Real.pi : ℂ) * y * E))
      (referenceMeasure j) := by
  have he : (fun E : ℝ => Complex.exp (-2 * (Real.pi : ℂ) * y * E)) =
      (fun E : ℝ => Complex.exp (-((2 * Real.pi * y : ℝ) : ℂ) * E)) := by
    funext E
    congr 1
    push_cast
    ring
  rw [he]
  exact integrable_cexp_neg_referenceMeasure hj (by positivity)

/-- The physical-height normalization gives exactly the central Bessel value. -/
theorem integral_centralLaplace_referenceMeasure (y : ℝ) {j : ℤ} (hj : j ≠ 0) :
    (∫ E : ℝ, Complex.exp (-2 * (Real.pi : ℂ) * y * E) ∂referenceMeasure j) =
      (besselK0 (2 * Real.pi * |(j : ℝ)| * y) : ℂ) := by
  have he : (fun E : ℝ => Complex.exp (-2 * (Real.pi : ℂ) * y * E)) =
      (fun E : ℝ => Complex.exp (-((2 * Real.pi * y : ℝ) : ℂ) * E)) := by
    funext E
    congr 1
    push_cast
    ring
  rw [he, integral_cexp_neg_referenceMeasure hj]
  rw [show 2 * Real.pi * y * |(j : ℝ)| = 2 * Real.pi * |(j : ℝ)| * y by ring]

/-- The actual central Fourier factor is the Laplace transform of the constant
physical density, with its exact factor `2 sqrt y`. -/
theorem centralFourierFactor_zero_eq_referenceLaplace {y : ℝ} (_hy : 0 < y)
    {j : ℤ} (hj : j ≠ 0) :
    PoincareCentralFactor.centralFourierFactor y j 0 =
      2 * (Real.sqrt y : ℂ) *
        ∫ E : ℝ, Complex.exp (-2 * (Real.pi : ℂ) * y * E)
          ∂referenceMeasure j := by
  rw [PoincareCentralFactor.centralFourierFactor_zero,
    integral_centralLaplace_referenceMeasure y hj]

namespace PoincareCentralZeta

open PoincareCanonical PoincareFourierContinuation PoincareFourierRemainder

/-- The actual zero-spin, zero-energy input contributes no central density in
a nonzero output spin. -/
theorem centralZeta_zero_input (j : ℤ) (hj : j ≠ 0) :
    centralZeta j 0 0 = 0 := by
  rw [centralZeta_zero_eq_thresholdQuotient 1 zero_lt_one j 0 hj]
  simp [thresholdFourierCoefficient, thresholdSeed_zero, hj,
    fourierRemainder, fourierRemainderKernel]

end PoincareCentralZeta

end GapFamily.Analytic
