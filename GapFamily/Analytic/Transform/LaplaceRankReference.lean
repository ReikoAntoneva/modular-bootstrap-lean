import GapFamily.Analytic.Transform.LaplaceTest
import GapFamily.Analytic.Foundation.ReferenceMeasure
import GapFamily.Analytic.Kernel.FullKernel
import GapFamily.Analytic.Kernel.PositiveKernelIntegral
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Scalar rank correction under finite Laplace tests

The scalar square-root moment is evaluated against the actual physical
reference measure. Its product gives the ordinary, absolutely integrable
pairing of the rank correction, with exactly the spatial constant-six
normalization after four height evaluations.
-/

noncomputable section

namespace GapFamily.Analytic

open Real Set MeasureTheory

private theorem referenceDensity_zero_mul_sqrt_rpow {E : ℝ} (hE : 0 < E) :
    referenceDensity 0 E * sqrt E = E ^ (-(1 / 2 : ℝ)) := by
  rw [referenceDensity_zero hE.le, Real.rpow_neg hE.le, ← Real.sqrt_eq_rpow]
  have hs : sqrt E ≠ 0 := (Real.sqrt_pos.mpr hE).ne'
  field_simp
  exact Real.sq_sqrt hE.le

/-- The finite Laplace test has an ordinary scalar square-root moment. -/
theorem sqrt_laplaceTest_integrable_referenceMeasure (k : ℕ) :
    Integrable (fun E : ℝ => sqrt E * laplaceTest k E) (referenceMeasure 0) := by
  rw [referenceMeasure, integrable_withDensity_iff_integrable_smul'
    (measurable_referenceDensity 0).ennreal_ofReal (by simp)]
  simp only [Int.cast_zero, abs_zero,
    ENNReal.toReal_ofReal (referenceDensity_nonneg 0 _), smul_eq_mul]
  apply (scalar_laplaceTest_integrable k).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with E hE
  rw [← mul_assoc, referenceDensity_zero_mul_sqrt_rpow hE]

/-- Exact scalar square-root moment for the physical reference measure `dE/E`. -/
theorem integral_sqrt_laplaceTest_referenceMeasure (k : ℕ) :
    (∫ E, sqrt E * laplaceTest k E ∂referenceMeasure 0) =
      1 / sqrt (2 * laplaceHeight k) - 1 / sqrt (2 * laplaceHeight (k + 1)) := by
  rw [referenceMeasure, integral_withDensity_eq_integral_toReal_smul
    (measurable_referenceDensity 0).ennreal_ofReal (by simp)]
  simp only [Int.cast_zero, abs_zero,
    ENNReal.toReal_ofReal (referenceDensity_nonneg 0 _), smul_eq_mul]
  rw [← scalar_laplaceTest_integral k]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with E hE
  rw [← mul_assoc, referenceDensity_zero_mul_sqrt_rpow hE]

/-- The actual two-energy rank pairing is absolutely integrable. -/
theorem scalarRankKernel_laplaceTest_integrable (j J : ℤ) (k l : ℕ) :
    Integrable (fun p : ℝ × ℝ =>
      laplaceTest k p.1 * scalarRankKernel j J p.1 p.2 * laplaceTest l p.2)
      ((referenceMeasure j).prod (referenceMeasure J)) := by
  by_cases h : j = 0 ∧ J = 0
  · rcases h with ⟨rfl, rfl⟩
    have hi := ((sqrt_laplaceTest_integrable_referenceMeasure k).mul_prod
      (sqrt_laplaceTest_integrable_referenceMeasure l)).const_mul 12
    convert hi using 1
    ext p
    simp only [scalarRankKernel, and_self, ite_true]
    ring
  · simp [scalarRankKernel, h]

/-- The reference-measure rank pairing has its exact coefficient twelve. -/
theorem integral_scalarRankKernel_laplaceTest (j J : ℤ) (k l : ℕ) :
    (∫ p : ℝ × ℝ,
      laplaceTest k p.1 * scalarRankKernel j J p.1 p.2 * laplaceTest l p.2
        ∂((referenceMeasure j).prod (referenceMeasure J))) =
      if j = 0 ∧ J = 0 then
        12 * (1 / sqrt (2 * laplaceHeight k) -
          1 / sqrt (2 * laplaceHeight (k + 1))) *
          (1 / sqrt (2 * laplaceHeight l) -
            1 / sqrt (2 * laplaceHeight (l + 1))) else 0 := by
  by_cases h : j = 0 ∧ J = 0
  · rcases h with ⟨rfl, rfl⟩
    simp only [and_self, ite_true]
    have heq (p : ℝ × ℝ) :
        laplaceTest k p.1 * scalarRankKernel 0 0 p.1 p.2 * laplaceTest l p.2 =
          12 * ((sqrt p.1 * laplaceTest k p.1) *
            (sqrt p.2 * laplaceTest l p.2)) := by
      simp only [scalarRankKernel, and_self, ite_true]
      ring
    simp_rw [heq]
    rw [integral_const_mul, integral_prod_mul
      (fun E => sqrt E * laplaceTest k E) (fun E => sqrt E * laplaceTest l E),
      integral_sqrt_laplaceTest_referenceMeasure,
      integral_sqrt_laplaceTest_referenceMeasure]
    ring
  · simp [scalarRankKernel, h]

/-- The spatial constant six becomes the exact physical rank pairing. -/
theorem rank_one_four_height_reference_identity (k l : ℕ) :
    6 * ((1 / sqrt (laplaceHeight k) - 1 / sqrt (laplaceHeight (k + 1))) *
      (1 / sqrt (laplaceHeight l) - 1 / sqrt (laplaceHeight (l + 1)))) =
      ∫ p : ℝ × ℝ,
        laplaceTest k p.1 * scalarRankKernel 0 0 p.1 p.2 * laplaceTest l p.2
          ∂((referenceMeasure 0).prod (referenceMeasure 0)) := by
  rw [integral_scalarRankKernel_laplaceTest]
  simpa only [and_self, ite_true, scalar_laplaceTest_integral] using
    rank_one_four_height_identity k l

/-- The normalized height difference of the spatial constant six equals the
ordinary scalar rank pairing before horizontal Fourier projection. -/
theorem normalizedHeightDifference_six_eq_rank_pairing (k l : ℕ) (x y : ℝ) :
    normalizedHeightDifference (fun _ _ => 6) k l x y =
      ((∫ p : ℝ × ℝ,
        laplaceTest k p.1 * scalarRankKernel 0 0 p.1 p.2 * laplaceTest l p.2
          ∂((referenceMeasure 0).prod (referenceMeasure 0)) : ℝ) : ℂ) := by
  rw [← rank_one_four_height_reference_identity]
  simp only [normalizedHeightDifference, laplaceHeightWeight]
  push_cast
  ring

/-- Both horizontal Fourier projections of the spatial constant six recover
the actual scalar rank correction in every pair of integer spin rows. -/
theorem fourierHeight_six_eq_scalarRankKernel_pairing (j J : ℤ) (k l : ℕ) :
    (∫ x : ℝ in 0..1, ∫ y : ℝ in 0..1,
      horizontalPhase (-j) x *
        normalizedHeightDifference (fun _ _ => 6) k l x y * horizontalPhase J y) =
      ((∫ p : ℝ × ℝ,
        laplaceTest k p.1 * scalarRankKernel j J p.1 p.2 * laplaceTest l p.2
          ∂((referenceMeasure j).prod (referenceMeasure J)) : ℝ) : ℂ) := by
  simp_rw [normalizedHeightDifference_six_eq_rank_pairing,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_mul_const,
    integral_horizontalPhase]
  by_cases hj : j = 0 <;> by_cases hJ : J = 0 <;>
    simp [hj, hJ, integral_scalarRankKernel_laplaceTest]

end GapFamily.Analytic
