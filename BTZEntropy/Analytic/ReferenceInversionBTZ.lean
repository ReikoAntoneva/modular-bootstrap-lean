import BTZEntropy.Analytic.ReferenceInversionTransform
import BTZEntropy.Analytic.ReferenceInversionContour

/-! The exact primary and descendant transforms agree with the complex BTZ
transform throughout the right half-plane, before contour inversion. -/

noncomputable section

namespace BTZEntropy

/-- Exact complex thermal assembly, including both finite shifts. -/
theorem complexReferenceFullTransform_eq_btz {a : ℝ} {z : ℂ}
    (ha : 2 ≤ a) (hz : 0 < z.re) :
    Complex.exp (z / 12) * (complexEulerProduct (Complex.exp (-z)))⁻¹ ^ 2 *
      complexReferencePrimaryTransform a z =
        complexPerturbativeBTZTransform (12 * a + 1) z := by
  rw [complexReferencePrimaryTransform_eq ha hz,
    complexPerturbativeBTZTransform, complexDualBoundaryGravitonFactor]
  have hz0 : z ≠ 0 := by intro h; simp [h] at hz
  have hexp : Complex.exp (z / 12) * Complex.exp (4 * (Real.pi : ℂ) ^ 2 * a / z) =
      Complex.exp ((Real.pi : ℂ) ^ 2 * ((12 * a + 1 : ℝ) : ℂ) / (3 * z)) *
        Complex.exp ((z - complexDualTemperature z) / 12) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    unfold complexDualTemperature
    push_cast
    field_simp
    ring
  have hnull : -complexDualTemperature z = -4 * (Real.pi : ℂ) ^ 2 / z := by
    unfold complexDualTemperature
    ring
  rw [hnull]
  calc
    _ = (Complex.exp (z / 12) * Complex.exp (4 * (Real.pi : ℂ) ^ 2 * a / z)) *
        ((2 * (Real.pi : ℂ) / z) * (1 - Complex.exp (-4 * (Real.pi : ℂ) ^ 2 / z)) ^ 2 *
          (complexEulerProduct (Complex.exp (-z)))⁻¹ ^ 2) := by ring
    _ = _ := by rw [hexp]; ring

end BTZEntropy
