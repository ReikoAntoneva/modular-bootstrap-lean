import BTZEntropy.Comparison.SpinImageBound
import BTZEntropy.Comparison.SpinCoefficient
import BTZEntropy.Analytic.ReferenceTransform
import Mathlib.Analysis.Fourier.PoissonSummation

/-!
# Actual thermal Poisson comparison of discrete and continuous spin

The denominator-one vacuum image satisfies the actual continuity, spatial
decay and Fourier-summability hypotheses of Poisson summation. Its central
image is the continuous-spin reference transform; every other integer image
belongs to the explicitly bounded tail. This result is on the positive real
thermal axis. Transferring it to the smoothed microcanonical observable still
requires the complex inversion and contour estimates.
-/

noncomputable section

open MeasureTheory GapFamily.Analytic
open scoped FourierTransform

namespace BTZEntropy

/-- The actual integer-spin leading reference, thermally transformed in energy. -/
def integerSpinReferenceThermal (a y : ℝ) : ℂ :=
  ∑' j : ℤ, ∫ e : ℝ,
    Complex.exp (-2 * (Real.pi : ℂ) * (y : ℂ) * (e : ℂ)) *
      (vacuumLeading a e j : ℂ) ∂referenceMeasure j

theorem spinImage_poisson {a y : ℝ} (ha : 2 ≤ a) (hy : 0 < y) :
    (∑' n : ℤ, spinImageKernel a y n) =
      ∑' j : ℤ, 𝓕 (spinImageKernel a y) (j : ℝ) := by
  simpa using Real.tsum_eq_tsum_fourier_of_rpow_decay_of_summable
    (continuous_spinImageKernel hy a) (by norm_num : (1 : ℝ) < 2)
    (spinImageKernel_isBigO ha hy) (summable_fourier_spinImageKernel hy a) 0

theorem integerSpinReferenceThermal_eq_images {a y : ℝ} (ha : 2 ≤ a) (hy : 0 < y) :
    (Real.sqrt y : ℂ) * integerSpinReferenceThermal a y =
      ∑' n : ℤ, spinImageKernel a y n := by
  rw [spinImage_poisson ha hy]
  simp only [fourier_spinImageKernel_eq_reference ha hy, tsum_mul_left,
    integerSpinReferenceThermal]

theorem spinImageKernel_zero_eq_reference {a y : ℝ} (ha : 2 ≤ a) (hy : 0 < y) :
    spinImageKernel a y 0 =
      (Real.sqrt y : ℂ) * (referencePrimaryTransform a (2 * Real.pi * y) : ℂ) := by
  rw [spinImageKernel_zero hy, referencePrimaryTransform_eq ha (by positivity)]
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  have hy0 : y ≠ 0 := ne_of_gt hy
  have h1 : 2 * Real.pi / (2 * Real.pi * y) = 1 / y := by field_simp
  have h2 : 4 * Real.pi ^ 2 * a / (2 * Real.pi * y) = 2 * Real.pi * a / y := by field_simp; ring
  have h3 : -4 * Real.pi ^ 2 / (2 * Real.pi * y) = -2 * Real.pi / y := by field_simp; ring
  rw [h1, h2, h3]
  push_cast
  ring

/-- Exact Poisson error identity, with the genuine continuum reference integral. -/
theorem integerSpinReferenceThermal_sub_reference {a y : ℝ} (ha : 2 ≤ a) (hy : 0 < y) :
    (Real.sqrt y : ℂ) *
        (integerSpinReferenceThermal a y - (referencePrimaryTransform a (2 * Real.pi * y) : ℂ)) =
      ∑' n : ℤ, spinImageTail a y n := by
  rw [mul_sub, integerSpinReferenceThermal_eq_images ha hy,
    ← spinImageKernel_zero_eq_reference ha hy,
    tsum_spinImageKernel_eq_central_add_tail ha hy]
  ring

/-- An explicit error bound follows from the actual noncentral image sum. -/
theorem norm_integerSpinReferenceThermal_sub_reference_le {a y : ℝ}
    (ha : 2 ≤ a) (hy : 0 < y) :
    ‖(Real.sqrt y : ℂ) *
        (integerSpinReferenceThermal a y - (referencePrimaryTransform a (2 * Real.pi * y) : ℂ))‖ ≤
      spinImageBoundConstant a y * ∑' n : ℤ, 1 / (n : ℝ) ^ 2 := by
  rw [integerSpinReferenceThermal_sub_reference ha hy]
  exact norm_tsum_spinImageTail_le ha hy

end BTZEntropy
