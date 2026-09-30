import GapFamily.Analytic.Kernel.FullKernelSmoothingOperator
import GapFamily.Analytic.Foundation.ThresholdCoefficientBound

/-! The scalar threshold mass acts continuously on ordinary L1 numerators.
It is deliberately not defined as a bounded functional on the low-band
Hilbert space, whose scalar row need not have finite ordinary mass. -/

noncomputable section

open MeasureTheory Set
open scoped BigOperators

namespace GapFamily.Analytic

open PoincareScalarFourier

/-- The actual `c_J`-weighted ordinary mass of a finite family of L1 rows. -/
def lowBandThresholdFunctional {ι : Type*} [Fintype ι] (J : ι → ℤ) (B : ℝ) :
    CorrectedKernelSmoothingSpace J B →L[ℂ] ℂ :=
  ∑ i, scalarThresholdCoefficient (J i) •
    ((L1.integralCLM' ℂ).comp
      (PiLp.proj 1 (fun i => CorrectedKernelSmoothingRow (J i) B) i))

theorem lowBandThresholdFunctional_apply {ι : Type*} [Fintype ι]
    (J : ι → ℤ) (B : ℝ) (f : CorrectedKernelSmoothingSpace J B) :
    lowBandThresholdFunctional J B f =
      ∑ i, scalarThresholdCoefficient (J i) * ∫ e, f i e
        ∂(referenceMeasure (J i)).restrict (Ioo |(J i : ℝ)| B) := by
  simp only [lowBandThresholdFunctional, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, PiLp.proj_apply,
    smul_eq_mul, ← L1.integral_eq', L1.integral_eq_integral]

/-- A bound on the spin coefficients controls the functional in the ordinary
sum L1 norm, including the scalar endpoint. -/
theorem norm_lowBandThresholdFunctional_apply_le {ι : Type*} [Fintype ι]
    (J : ι → ℤ) (B C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ i, ‖scalarThresholdCoefficient (J i)‖ ≤ C)
    (f : CorrectedKernelSmoothingSpace J B) :
    ‖lowBandThresholdFunctional J B f‖ ≤ C * ‖f‖ := by
  rw [lowBandThresholdFunctional_apply, PiLp.norm_eq_of_L1]
  calc
    _ ≤ ∑ i, ‖scalarThresholdCoefficient (J i) * ∫ e, f i e
        ∂(referenceMeasure (J i)).restrict (Ioo |(J i : ℝ)| B)‖ := norm_sum_le _ _
    _ ≤ ∑ i, C * ‖f i‖ := by
      apply Finset.sum_le_sum
      intro i hi
      rw [norm_mul, ← L1.integral_eq_integral]
      exact mul_le_mul (hbound i) (L1.norm_integral_le (f i)) (norm_nonneg _) hC
    _ = _ := (Finset.mul_sum _ _ _).symm

theorem norm_lowBandThresholdFunctional_le {ι : Type*} [Fintype ι]
    (J : ι → ℤ) (B C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ i, ‖scalarThresholdCoefficient (J i)‖ ≤ C) :
    ‖lowBandThresholdFunctional J B‖ ≤ C :=
  ContinuousLinearMap.opNorm_le_bound _ hC
    (norm_lowBandThresholdFunctional_apply_le J B C hC hbound)

theorem norm_lowBandThresholdFunctional_le_physical {ι : Type*} [Fintype ι]
    (J : ι → ℤ) (B : ℝ) (hB : 1 ≤ B) (hband : ∀ i, |(J i : ℝ)| ≤ B) :
    ‖lowBandThresholdFunctional J B‖ ≤ 3 * B :=
  norm_lowBandThresholdFunctional_le J B (3 * B) (by linarith)
    (fun i => norm_scalarThresholdCoefficient_le_physical (J i) B hB (hband i))

/-- Smoothing first makes the actual threshold mass a legitimate bounded
functional on the Hilbert input. -/
def correctedSmoothingThresholdFunctional {ι : Type*} [Fintype ι]
    (J : ι → ℤ) (B : ℝ) (hB : 0 ≤ B) : LowBandHilbert J B →L[ℂ] ℂ :=
  (lowBandThresholdFunctional J B).comp (correctedKernelFiniteSmoothingOperator J J B hB)

theorem correctedSmoothingThresholdFunctional_apply {ι : Type*} [Fintype ι]
    (J : ι → ℤ) (B : ℝ) (hB : 0 ≤ B) (f : LowBandHilbert J B) :
    correctedSmoothingThresholdFunctional J B hB f =
      ∑ i, scalarThresholdCoefficient (J i) * ∫ e, correctedKernelResponse J B f (J i) e
        ∂(referenceMeasure (J i)).restrict (Ioo |(J i : ℝ)| B) := by
  rw [correctedSmoothingThresholdFunctional, ContinuousLinearMap.comp_apply,
    lowBandThresholdFunctional_apply]
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  exact integral_congr_ae (coeFn_correctedKernelSmoothingOperator J B hB (J i) f)

end GapFamily.Analytic
