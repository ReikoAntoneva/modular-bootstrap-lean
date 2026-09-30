import BTZEntropy.Analytic.SaddleCount

/-! Exact removal of the saddle normalization from the BTZ inverse contour. -/

noncomputable section

namespace BTZEntropy

open MeasureTheory

/-- The complex perturbative BTZ thermal transform, with the physical central charge. -/
def complexPerturbativeBTZTransform (c : ℝ) (z : ℂ) : ℂ :=
  Complex.exp ((Real.pi : ℂ) ^ 2 * (c : ℂ) / (3 * z)) *
    complexDualBoundaryGravitonFactor z

theorem complexPerturbativeBTZTransform_ofReal (c : ℝ) {β : ℝ} (hβ : 0 < β) :
    complexPerturbativeBTZTransform c (β : ℂ) = (perturbativeBTZTransform c β : ℂ) := by
  unfold complexPerturbativeBTZTransform perturbativeBTZTransform
  rw [complexDualBoundaryGravitonFactor_ofReal hβ]
  push_cast
  rfl

/-- The literal inverse contour, before the universal factor `1 / (2π)`. -/
def btzInverseIntegrand (φ : SmoothKernel) (β E c t : ℝ) : ℂ :=
  Complex.exp (saddleContour β t * (E : ℂ)) *
    complexKernelTransform φ (saddleContour β t) *
      complexPerturbativeBTZTransform c (saddleContour β t)

theorem btzInverseIntegrand_eq_normalized (φ : SmoothKernel) {x : ℝ}
    (hx : 0 < x) (c t : ℝ) :
    btzInverseIntegrand φ (saddleBeta x) (x * c) c t =
      (Real.exp (leadingAction x c) : ℂ) *
        (complexAmplitude φ (saddleContour (saddleBeta x) t) *
          normalizedSaddleExponential x c t) := by
  unfold btzInverseIntegrand complexPerturbativeBTZTransform complexAmplitude
    normalizedSaddleExponential
  rw [Complex.ofReal_exp]
  have he : (leadingAction x c : ℂ) + (c : ℂ) *
      (complexSaddlePhase x (saddleContour (saddleBeta x) t) -
        (saddlePhase x (saddleBeta x) : ℂ)) =
      saddleContour (saddleBeta x) t * ((x * c : ℝ) : ℂ) +
        (Real.pi : ℂ) ^ 2 * (c : ℂ) / (3 * saddleContour (saddleBeta x) t) := by
    rw [saddlePhase_at_saddle hx]
    unfold leadingAction complexSaddlePhase phaseConstant
    push_cast
    ring
  calc
    _ = (Complex.exp (saddleContour (saddleBeta x) t * ((x * c : ℝ) : ℂ)) *
        Complex.exp ((Real.pi : ℂ) ^ 2 * (c : ℂ) /
          (3 * saddleContour (saddleBeta x) t))) *
          (complexKernelTransform φ (saddleContour (saddleBeta x) t) *
            complexDualBoundaryGravitonFactor (saddleContour (saddleBeta x) t)) := by ring
    _ = _ := by rw [← Complex.exp_add, ← he, Complex.exp_add]; ring

theorem integrable_btzInverseIntegrand (φ : SmoothKernel) {x c : ℝ}
    (hx : 0 < x) (hc : 0 ≤ c) :
    Integrable (btzInverseIntegrand φ (saddleBeta x) (x * c) c) := by
  change Integrable (fun t => btzInverseIntegrand φ (saddleBeta x) (x * c) c t)
  simp_rw [btzInverseIntegrand_eq_normalized φ hx]
  exact (integrable_normalizedBTZContour φ hx hc).const_mul _

/-- `btzCount` is the real part of the literal, convergent inverse Laplace integral. -/
theorem btzCount_eq_inverseContour (φ : SmoothKernel) {x c : ℝ}
    (hx : 0 < x) :
    btzCount φ x c =
      ((1 / (2 * Real.pi) : ℂ) *
        ∫ t : ℝ, btzInverseIntegrand φ (saddleBeta x) (x * c) c t).re := by
  simp_rw [btzInverseIntegrand_eq_normalized φ hx]
  rw [integral_const_mul]
  change Real.exp (leadingAction x c) / (2 * Real.pi) *
    (normalizedBTZContour φ x c).re =
      ((1 / (2 * Real.pi) : ℂ) *
        ((Real.exp (leadingAction x c) : ℂ) * normalizedBTZContour φ x c)).re
  rw [← mul_assoc]
  have hc : (1 / (2 * Real.pi) : ℂ) * (Real.exp (leadingAction x c) : ℂ) =
      ((Real.exp (leadingAction x c) / (2 * Real.pi) : ℝ) : ℂ) := by push_cast; ring
  rw [hc]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

end BTZEntropy
