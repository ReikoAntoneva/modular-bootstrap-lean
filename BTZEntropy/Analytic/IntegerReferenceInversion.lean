import BTZEntropy.Analytic.IntegerReferenceInversionCount
import BTZEntropy.Analytic.IntegerReferenceInversionTransform
import BTZEntropy.Analytic.ReferenceInversion

/-!
# Full integer-spin reference contour

Both descendant towers and the exact cylinder shift are retained. The final
identity isolates the actual integer-spin minus continuous-spin correction
inside one absolutely convergent inverse thermal contour.
-/

noncomputable section

open MeasureTheory

namespace BTZEntropy

/-- Exact inversion of the full integer-spin reference count. -/
theorem integerReferenceSmoothCount_eq_contour (φ : SmoothKernel) {a β : ℝ}
    (ha : 2 ≤ a) (hβ : 0 < β) (E : ℝ) :
    (integerReferenceSmoothCount φ a E : ℂ) =
      (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ,
        Complex.exp (saddleContour β t * E) * complexKernelTransform φ (saddleContour β t) *
          integerReferenceComplexLaplace a (saddleContour β t) := by
  let : SFinite integerReferenceMeasure := by unfold integerReferenceMeasure; infer_instance
  exact weightedSmoothCount_eq_contour φ β E integerReferenceEnergy (integerReferenceWeight a)
    measurable_integerReferenceEnergy (measurable_integerReferenceWeight a)
    (integrable_integerReferenceThermal ha hβ)

/-- The continuous reference has the same inversion convention. -/
theorem physicalSmoothCount_eq_contour (φ : SmoothKernel) {a β : ℝ}
    (ha : 2 ≤ a) (hβ : 0 < β) (E : ℝ) :
    (physicalSmoothCount φ a E : ℂ) =
      (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ,
        Complex.exp (saddleContour β t * E) * complexKernelTransform φ (saddleContour β t) *
          physicalComplexLaplace a (saddleContour β t) := by
  let : SFinite physicalReferenceMeasure := by unfold physicalReferenceMeasure; infer_instance
  exact weightedSmoothCount_eq_contour φ β E physicalReferenceEnergy (physicalReferenceWeight a)
    measurable_physicalReferenceEnergy (measurable_physicalReferenceWeight a)
    (integrable_physicalReferenceThermal ha hβ)

/-- Exact thermal factorization of the full integer-spin correction. -/
theorem integerReferenceComplexLaplace_sub_physical {a : ℝ} {z : ℂ}
    (ha : 2 ≤ a) (hz : 0 < z.re) :
    integerReferenceComplexLaplace a z - physicalComplexLaplace a z =
      Complex.exp (z / 12) * (complexEulerProduct (Complex.exp (-z)))⁻¹ ^ 2 *
        (integerSpinPrimaryComplexTransform a z - complexReferencePrimaryTransform a z) := by
  rw [integerReferenceComplexLaplace_eq ha hz, physicalComplexLaplace_eq ha hz]
  ring

/-- Absolute convergence of the full integer-spin inverse contour. -/
theorem integrable_integerReferenceInverseContour (φ : SmoothKernel) {a β : ℝ}
    (ha : 2 ≤ a) (hβ : 0 < β) (E : ℝ) :
    Integrable (fun t : ℝ =>
      Complex.exp (saddleContour β t * E) * complexKernelTransform φ (saddleContour β t) *
        integerReferenceComplexLaplace a (saddleContour β t)) := by
  let : SFinite integerReferenceMeasure := by unfold integerReferenceMeasure; infer_instance
  exact integrable_weightedInverseContour φ β E integerReferenceEnergy (integerReferenceWeight a)
    measurable_integerReferenceEnergy (measurable_integerReferenceWeight a)
    (integrable_integerReferenceThermal ha hβ)

/-- The physical smoothed difference equals the primary spin correction with
its exact descendant and cylinder factors inside the contour. -/
theorem integerReferenceSmoothCount_sub_physical_eq_contour (φ : SmoothKernel) {a β : ℝ}
    (ha : 2 ≤ a) (hβ : 0 < β) (E : ℝ) :
    ((integerReferenceSmoothCount φ a E - physicalSmoothCount φ a E : ℝ) : ℂ) =
      (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ,
        Complex.exp (saddleContour β t * E) * complexKernelTransform φ (saddleContour β t) *
          (Complex.exp (saddleContour β t / 12) *
            (complexEulerProduct (Complex.exp (-saddleContour β t)))⁻¹ ^ 2 *
              (integerSpinPrimaryComplexTransform a (saddleContour β t) -
                complexReferencePrimaryTransform a (saddleContour β t))) := by
  let : SFinite physicalReferenceMeasure := by unfold physicalReferenceMeasure; infer_instance
  have hi := integrable_integerReferenceInverseContour φ ha hβ E
  have hp := integrable_weightedInverseContour φ β E physicalReferenceEnergy
    (physicalReferenceWeight a) measurable_physicalReferenceEnergy
    (measurable_physicalReferenceWeight a) (integrable_physicalReferenceThermal ha hβ)
  change Integrable (fun t : ℝ => Complex.exp (saddleContour β t * E) *
    complexKernelTransform φ (saddleContour β t) *
      physicalComplexLaplace a (saddleContour β t)) at hp
  rw [Complex.ofReal_sub, integerReferenceSmoothCount_eq_contour φ ha hβ,
    physicalSmoothCount_eq_contour φ ha hβ, ← mul_sub, ← integral_sub hi hp]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with t
  rw [← mul_sub, integerReferenceComplexLaplace_sub_physical ha (by
    simpa only [saddleContour_re] using hβ)]

/-- The original full-cone integer-spin observable differs from `btzCount`
by precisely the same convergent spin-correction contour. -/
theorem integerLeadingSmoothCount_sub_btz_eq_contour (φ : SmoothKernel) {a x β : ℝ}
    (ha : 2 ≤ a) (hx : 0 < x) (hβ : 0 < β) :
    ((Comparison.integerLeadingSmoothCount φ a 0 (x * (12 * a + 1)) -
      btzCount φ x (12 * a + 1) : ℝ) : ℂ) =
      (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ,
        Complex.exp (saddleContour β t * (x * (12 * a + 1))) *
          complexKernelTransform φ (saddleContour β t) *
            (Complex.exp (saddleContour β t / 12) *
              (complexEulerProduct (Complex.exp (-saddleContour β t)))⁻¹ ^ 2 *
                (integerSpinPrimaryComplexTransform a (saddleContour β t) -
                  complexReferencePrimaryTransform a (saddleContour β t))) := by
  rw [← integerReferenceSmoothCount_eq_leading φ ha,
    ← physicalSmoothCount_eq_btzCount φ ha hx]
  simpa only [Complex.ofReal_mul, Complex.ofReal_add, Complex.ofReal_ofNat, Complex.ofReal_one] using
    integerReferenceSmoothCount_sub_physical_eq_contour φ ha hβ (x * (12 * a + 1))

end BTZEntropy
