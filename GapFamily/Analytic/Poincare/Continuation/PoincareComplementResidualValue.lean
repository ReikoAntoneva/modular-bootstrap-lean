import GapFamily.Analytic.Poincare.Continuation.PoincareComplementCore
import GapFamily.Analytic.Cusp.CuspPoincareResidualWeightedInput

noncomputable section
namespace GapFamily.Analytic.PoincareComplement
open ModularGradient CuspFourierCutoff CuspSchurLocal

/-- The exponent convention places the actual common region inside Re s>2. -/
theorem exponent_re_gt_two {κ : ℂ} (hκ : (3 / 2 : ℝ) < κ.re) :
    2 < (exponent κ).re := by
  norm_num [exponent, Complex.add_re]
  linarith

/-- The constructed source core is exactly the actual unweighted residual plus
the eigenvalue multiple of the actual complementary Poincaré value class. -/
theorem laplacianSourceCore_value_exponent (J : ℤ) {κ : ℂ}
    (hκ : (3 / 2 : ℝ) < κ.re) :
    value (laplacianSourceCore J (exponent κ) (exponent_re_gt_two hκ)) =
      cuspPoincareResidualSource J 0 (by norm_num) κ +
        parameter κ • value (smoothCore J (exponent κ) (exponent_re_gt_two hκ)) := by
  rw [laplacianSourceCore_value, value_eq_hilbertSum, exponent_eigenvalue]
  have he : exponent κ - 1 / 2 = κ := by unfold exponent; ring
  rw [he]
  unfold cuspPoincareResidualSource
  rw [weightedForcing_zero]
  have hc : (2 * (Real.pi : ℂ) * (J : ℂ)) ^ 2 =
      (((2 * Real.pi * (J : ℝ)) ^ 2 : ℝ) : ℂ) := by push_cast; rfl
  rw [hc]

end GapFamily.Analytic.PoincareComplement
