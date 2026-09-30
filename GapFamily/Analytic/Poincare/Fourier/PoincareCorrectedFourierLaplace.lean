import GapFamily.Analytic.Poincare.Fourier.PoincareFullFourierLaplace
import GapFamily.Analytic.Foundation.ScalarNormalization
import Mathlib.MeasureTheory.Integral.Prod

/-! The scalar rank correction is an ordinary reference density. Its exact
thermal transform is the constant added to the actual modular point seed. -/
noncomputable section
namespace GapFamily.Analytic.PoincareEnergyFourier
open Set MeasureTheory

private theorem scalar_reference_sqrt_density {e : ℝ} (he : 0 < e) :
    referenceDensity 0 e * Real.sqrt e = e ^ (-(1 / 2 : ℝ)) := by
  rw [referenceDensity_zero he.le, Real.rpow_neg he.le, ← Real.sqrt_eq_rpow]
  have hs := Real.sq_sqrt he.le
  have hn := Real.sqrt_ne_zero'.mpr he
  field_simp
  nlinarith

/-- The scalar square-root numerator is ordinarily integrable under the
physical reference measure at every positive thermal tilt. -/
theorem integrable_scalar_sqrt_reference (y : ℝ) (hy : 0 < y) :
    Integrable (fun e : ℝ => Real.exp (-2 * Real.pi * y * e) * Real.sqrt e)
      (referenceMeasure 0) := by
  unfold referenceMeasure
  rw [integrable_withDensity_iff_integrable_smul'
    (measurable_referenceDensity 0).ennreal_ofReal (by simp)]
  simp only [Int.cast_zero, abs_zero]
  apply (scalar_rank_one_integrable hy).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with e he
  rw [ENNReal.toReal_ofReal (referenceDensity_nonneg 0 e), smul_eq_mul]
  rw [mul_left_comm, scalar_reference_sqrt_density he]
  ring

/-- Exact ordinary scalar reference-measure normalization. -/
theorem scalar_sqrt_reference_normalization (y : ℝ) (hy : 0 < y) :
    Real.sqrt y * (∫ e : ℝ, Real.exp (-2 * Real.pi * y * e) * Real.sqrt e
      ∂referenceMeasure 0) = 1 / Real.sqrt 2 := by
  have hi : (∫ e : ℝ, Real.exp (-2 * Real.pi * y * e) * Real.sqrt e
      ∂referenceMeasure 0) =
      ∫ e : ℝ in Ioi 0, e ^ (-(1 / 2 : ℝ)) * Real.exp (-2 * Real.pi * y * e) := by
    unfold referenceMeasure
    rw [integral_withDensity_eq_integral_toReal_smul
      (measurable_referenceDensity 0).ennreal_ofReal (by simp)]
    simp only [Int.cast_zero, abs_zero]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with e he
    rw [ENNReal.toReal_ofReal (referenceDensity_nonneg 0 e), smul_eq_mul]
    rw [mul_left_comm, scalar_reference_sqrt_density he]
    ring
  rw [hi]
  exact scalar_rank_one_normalization hy

private theorem scalar_rank_laplace_eq (y E e : ℝ) :
    Complex.exp (-2 * (Real.pi : ℂ) * (y : ℂ) * (e : ℂ)) *
      (scalarRankKernel 0 0 e E : ℂ) =
      ((Real.exp (-2 * Real.pi * y * e) * Real.sqrt e : ℝ) : ℂ) *
        ((12 * Real.sqrt E : ℝ) : ℂ) := by
  simp only [scalarRankKernel, and_self, ite_true]
  rw [show -2 * (Real.pi : ℂ) * (y : ℂ) * (e : ℂ) =
    ((-2 * Real.pi * y * e : ℝ) : ℂ) by push_cast; ring,
    ← Complex.ofReal_exp]
  push_cast
  ring

/-- The scalar rank-one correction has an ordinary complex Laplace integral,
including the zero rows and columns of the rank-one kernel. -/
theorem integrable_scalarRankKernel_laplace (y : ℝ) (hy : 0 < y)
    (E : ℝ) (j J : ℤ) :
    Integrable (fun e : ℝ =>
      Complex.exp (-2 * (Real.pi : ℂ) * (y : ℂ) * (e : ℂ)) *
        (scalarRankKernel j J e E : ℂ)) (referenceMeasure j) := by
  by_cases h : j = 0 ∧ J = 0
  · obtain ⟨rfl, rfl⟩ := h
    simp_rw [scalar_rank_laplace_eq]
    exact (integrable_scalar_sqrt_reference y hy).ofReal.mul_const
      ((12 * Real.sqrt E : ℝ) : ℂ)
  · simp only [scalarRankKernel, ite_eq_right h, Complex.ofReal_zero, mul_zero]
    exact integrable_zero _ _ _

/-- Exact transform of the actual rank-one numerator against `referenceMeasure`.
The correction is a constant in height, rather than a threshold atom. -/
theorem scalarRankKernel_laplace_normalization (y : ℝ) (hy : 0 < y)
    (E : ℝ) (j J : ℤ) :
    (Real.sqrt y : ℂ) * (∫ e : ℝ,
      Complex.exp (-2 * (Real.pi : ℂ) * (y : ℂ) * (e : ℂ)) *
        (scalarRankKernel j J e E : ℂ) ∂referenceMeasure j) =
      if j = 0 ∧ J = 0 then ((12 * Real.sqrt E / Real.sqrt 2 : ℝ) : ℂ) else 0 := by
  by_cases h : j = 0 ∧ J = 0
  · obtain ⟨rfl, rfl⟩ := h
    simp only [and_self, ite_true, scalar_rank_laplace_eq, integral_mul_const,
      integral_complex_ofReal]
    rw [← mul_assoc, ← Complex.ofReal_mul, scalar_sqrt_reference_normalization y hy]
    push_cast
    ring
  · simp only [scalarRankKernel, ite_eq_right h, Complex.ofReal_zero, mul_zero,
      integral_zero]

/-- The same absolute convergence at an arbitrary positive thermal parameter. -/
theorem integrable_scalarRankKernel_thermal (t : ℝ) (ht : 0 < t)
    (E : ℝ) (j J : ℤ) :
    Integrable (fun e : ℝ => Complex.exp (-(t : ℂ) * (e : ℂ)) *
      (scalarRankKernel j J e E : ℂ)) (referenceMeasure j) := by
  have hp : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  have he : ∀ e : ℝ, -2 * (Real.pi : ℂ) * ((t / (2 * Real.pi) : ℝ) : ℂ) *
      (e : ℂ) = -(t : ℂ) * (e : ℂ) := by
    intro e
    push_cast
    field_simp
  simpa only [he] using integrable_scalarRankKernel_laplace
    (t / (2 * Real.pi)) (by positivity) E j J

/-- A bounded input-energy support gives absolute integrability on the actual
product of the input measure and the physical output measure. This also applies
to the total variation of any finite signed input measure. -/
theorem integrable_scalarRankKernel_laplace_prod (μ : Measure ℝ) [IsFiniteMeasure μ]
    (B : ℝ) (hμ : ∀ᵐ E ∂μ, E ≤ B) (y : ℝ) (hy : 0 < y) (j J : ℤ) :
    Integrable (fun p : ℝ × ℝ =>
      Complex.exp (-2 * (Real.pi : ℂ) * (y : ℂ) * (p.2 : ℂ)) *
        (scalarRankKernel j J p.2 p.1 : ℂ)) (μ.prod (referenceMeasure j)) := by
  by_cases h : j = 0 ∧ J = 0
  · obtain ⟨rfl, rfl⟩ := h
    have hi : Integrable Real.sqrt μ := by
      apply (integrable_const (Real.sqrt B)).mono' Real.continuous_sqrt.aestronglyMeasurable
      filter_upwards [hμ] with E hE
      simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg E)] using
        Real.sqrt_le_sqrt hE
    have hp := (hi.ofReal.const_mul (12 : ℂ)).mul_prod
      (integrable_scalar_sqrt_reference y hy).ofReal
    convert hp using 1
    ext p
    change Complex.exp (-2 * (Real.pi : ℂ) * (y : ℂ) * (p.2 : ℂ)) *
      (scalarRankKernel 0 0 p.2 p.1 : ℂ) =
      (12 : ℂ) * (Real.sqrt p.1 : ℂ) *
        ((Real.exp (-2 * Real.pi * y * p.2) * Real.sqrt p.2 : ℝ) : ℂ)
    rw [scalar_rank_laplace_eq]
    simp only [Complex.ofReal_mul, Complex.ofReal_ofNat]
    ring
  · simp only [scalarRankKernel, ite_eq_right h, Complex.ofReal_zero, mul_zero]
    exact integrable_zero _ _ _

/-- Product absolute integrability at an arbitrary positive thermal tilt. -/
theorem integrable_scalarRankKernel_thermal_prod (μ : Measure ℝ) [IsFiniteMeasure μ]
    (B : ℝ) (hμ : ∀ᵐ E ∂μ, E ≤ B) (t : ℝ) (ht : 0 < t) (j J : ℤ) :
    Integrable (fun p : ℝ × ℝ =>
      Complex.exp (-(t : ℂ) * (p.2 : ℂ)) *
        (scalarRankKernel j J p.2 p.1 : ℂ)) (μ.prod (referenceMeasure j)) := by
  have he : ∀ e : ℝ, -2 * (Real.pi : ℂ) * ((t / (2 * Real.pi) : ℝ) : ℂ) *
      (e : ℂ) = -(t : ℂ) * (e : ℂ) := by
    intro e
    push_cast
    field_simp
  simpa only [he] using integrable_scalarRankKernel_laplace_prod
    μ B hμ (t / (2 * Real.pi)) (by positivity) j J

/-- The complete corrected density has an ordinary thermal integral. -/
theorem integrable_correctedKernel_laplace (y : ℝ) (hy : 0 < y)
    (E : ℝ) (j J : ℤ) :
    Integrable (fun e : ℝ =>
      Complex.exp (-2 * (Real.pi : ℂ) * (y : ℂ) * (e : ℂ)) *
        correctedKernel j J e E) (referenceMeasure j) := by
  convert (integrable_fullKernelHol_laplace y hy (E : ℂ) j J).add
    (integrable_scalarRankKernel_laplace y hy E j J) using 1
  ext e
  exact mul_add _ _ _

end GapFamily.Analytic.PoincareEnergyFourier

namespace GapFamily.Analytic.PoincareEnergyContinuation
open scoped MatrixGroups

/-- The actual threshold point seed with its scalar rank-one constant. -/
def correctedPointSeed (E : ℝ) (J : ℤ) (τ : UpperHalfPlane) : ℂ :=
  generalThresholdSeed (E : ℂ) J τ +
    if J = 0 then ((12 * Real.sqrt E / Real.sqrt 2 : ℝ) : ℂ) else 0

/-- The scalar correction preserves continuity of the actual point seed. -/
theorem continuous_correctedPointSeed (E : ℝ) (J : ℤ) :
    Continuous (correctedPointSeed E J) :=
  (continuous_generalThresholdSeed (E : ℂ) J).add continuous_const

/-- The rank-one spatial constant preserves exact modular invariance. -/
theorem correctedPointSeed_smul (E : ℝ) (J : ℤ) (τ : UpperHalfPlane) (g : SL(2, ℤ)) :
    correctedPointSeed E J (g • τ) = correctedPointSeed E J τ := by
  simp only [correctedPointSeed, generalThresholdSeed_smul]

end GapFamily.Analytic.PoincareEnergyContinuation

namespace GapFamily.Analytic.PoincareEnergyFourier
open Set MeasureTheory PoincareEnergyContinuation PoincareFourier

/-- The ordinary Fourier coefficient of the corrected global point seed. -/
def correctedPointFourierCoefficient (y : ℝ) (hy : 0 < y) (E : ℝ) (j J : ℤ) : ℂ :=
  ∫ x in (0 : ℝ)..1, cuspFourierMode (-j) x *
    correctedPointSeed E J (rowPoint y hy x)

/-- The corrected Fourier coefficient is a genuine ordinary interval integral. -/
theorem intervalIntegrable_correctedPointFourierIntegrand (y : ℝ) (hy : 0 < y)
    (E : ℝ) (j J : ℤ) :
    IntervalIntegrable (fun x => cuspFourierMode (-j) x *
      correctedPointSeed E J (rowPoint y hy x)) volume 0 1 :=
  ((contDiff_cuspFourierMode (-j)).continuous.mul
    ((continuous_correctedPointSeed E J).comp (continuous_rowPoint y hy))).intervalIntegrable 0 1

/-- The added spatial constant contributes exactly at zero output spin. -/
theorem correctedPointFourierCoefficient_eq_add_rank (y : ℝ) (hy : 0 < y)
    (E : ℝ) (j J : ℤ) :
    correctedPointFourierCoefficient y hy E j J =
      generalThresholdFourierCoefficient y hy (E : ℂ) j J +
        if j = 0 ∧ J = 0 then ((12 * Real.sqrt E / Real.sqrt 2 : ℝ) : ℂ) else 0 := by
  unfold correctedPointFourierCoefficient correctedPointSeed
  simp only [mul_add]
  have hc : IntervalIntegrable (fun x : ℝ => cuspFourierMode (-j) x *
      (if J = 0 then ((12 * Real.sqrt E / Real.sqrt 2 : ℝ) : ℂ) else 0)) volume 0 1 :=
    ((contDiff_cuspFourierMode (-j)).continuous.mul continuous_const).intervalIntegrable 0 1
  rw [intervalIntegral.integral_add
    (intervalIntegrable_generalThresholdFourierIntegrand y hy (E : ℂ) j J)
    hc,
    intervalIntegral.integral_mul_const, integral_cuspFourierMode_zero_one]
  change generalThresholdFourierCoefficient y hy (E : ℂ) j J + _ = _
  by_cases hj : j = 0 <;> by_cases hJ : J = 0 <;> simp [hj, hJ]

/-- The full Fourier–Laplace formula of the corrected point seed uses the
actual corrected kernel and the ordinary physical reference measure. -/
theorem correctedPointFourierCoefficient_eq_full_laplace
    (y : ℝ) (hy : 0 < y) (E : ℝ) (j J : ℤ) :
    correctedPointFourierCoefficient y hy E j J =
      (if j = J then (Real.sqrt y : ℂ) *
        Complex.exp (-2 * (Real.pi : ℂ) * (E : ℂ) * (y : ℂ)) else 0) +
      (if j = 0 then (Real.sqrt y : ℂ) *
        PoincareScalarFourier.scalarThresholdCoefficient J else 0) +
      (Real.sqrt y : ℂ) * ∫ e : ℝ,
        Complex.exp (-2 * (Real.pi : ℂ) * (y : ℂ) * (e : ℂ)) *
          correctedKernel j J e E ∂referenceMeasure j := by
  rw [correctedPointFourierCoefficient_eq_add_rank,
    generalThresholdFourierCoefficient_eq_full_laplace]
  simp only [correctedKernel, mul_add]
  rw [integral_add (integrable_fullKernelHol_laplace y hy (E : ℂ) j J)
    (integrable_scalarRankKernel_laplace y hy E j J), mul_add,
    scalarRankKernel_laplace_normalization y hy E j J]
  ring

end GapFamily.Analytic.PoincareEnergyFourier
