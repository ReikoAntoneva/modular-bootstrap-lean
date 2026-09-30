import BTZEntropy.Analytic.ReferenceInversionBTZ
import BTZEntropy.Analytic.ReferenceInversionPhysical

/-!
# Physical reference count and the BTZ inverse contour

The full continuous-spin reference is an actual weighted distribution on the
energy-spin cone times both descendant levels. Fourier inversion of the compact
kernel and absolute Fubini connect its physical smoothing to `btzCount`.
-/

noncomputable section

open MeasureTheory

namespace BTZEntropy

/-- The literal physical distribution has the complex BTZ Laplace transform. -/
theorem physicalComplexLaplace_eq_btz {a : ℝ} {z : ℂ}
    (ha : 2 ≤ a) (hz : 0 < z.re) :
    physicalComplexLaplace a z = complexPerturbativeBTZTransform (12 * a + 1) z := by
  rw [physicalComplexLaplace_eq ha hz]
  calc
    _ = Complex.exp (z / 12) * (complexEulerProduct (Complex.exp (-z)))⁻¹ ^ 2 *
        complexReferencePrimaryTransform a z := by ring
    _ = _ := complexReferenceFullTransform_eq_btz ha hz

/-- Every physical smoothing of the nonnegative reference is nonnegative. -/
theorem physicalSmoothCount_nonneg (φ : SmoothKernel) {a : ℝ}
    (ha : 2 ≤ a) (E : ℝ) : 0 ≤ physicalSmoothCount φ a E := by
  apply integral_nonneg
  intro p
  exact mul_nonneg (physicalReferenceWeight_nonneg ha p) (φ.nonneg _)

/-- Exact microcanonical identity: the actual continuous primary reference with
all descendants has the BTZ smoothed count, at the same cylinder energy. -/
theorem physicalSmoothCount_eq_btzCount (φ : SmoothKernel) {a x : ℝ}
    (ha : 2 ≤ a) (hx : 0 < x) :
    physicalSmoothCount φ a (x * (12 * a + 1)) = btzCount φ x (12 * a + 1) := by
  let : SFinite physicalReferenceMeasure := by
    unfold physicalReferenceMeasure
    infer_instance
  have h := weightedSmoothCount_eq_contour φ (saddleBeta x) (x * (12 * a + 1))
    physicalReferenceEnergy (physicalReferenceWeight a)
    measurable_physicalReferenceEnergy (measurable_physicalReferenceWeight a)
    (integrable_physicalReferenceThermal ha (saddleBeta_pos hx))
  have hthermal (t : ℝ) :
      weightedComplexLaplace physicalReferenceMeasure physicalReferenceEnergy
        (physicalReferenceWeight a) (saddleContour (saddleBeta x) t) =
          complexPerturbativeBTZTransform (12 * a + 1) (saddleContour (saddleBeta x) t) := by
    apply physicalComplexLaplace_eq_btz ha
    simpa only [saddleContour_re] using saddleBeta_pos hx
  simp_rw [hthermal] at h
  have hr := congrArg Complex.re h
  change physicalSmoothCount φ a (x * (12 * a + 1)) = _ at hr
  rw [btzCount_eq_inverseContour φ hx]
  exact hr

/-- The same equality in explicit descendant-module form. -/
theorem continuousReferenceModules_eq_btzCount (φ : SmoothKernel) {a x : ℝ}
    (ha : 2 ≤ a) (hx : 0 < x) :
    (∫ p : ℝ × ℝ in referenceCone,
      referencePrimaryDensity a p.1 p.2 *
        Comparison.moduleSmoothCount φ (fun n => (partitionCount n : ℝ))
          (p.1 - 1 / 12) (x * (12 * a + 1))) = btzCount φ x (12 * a + 1) := by
  rw [← physicalSmoothCount_eq_modules φ ha, physicalSmoothCount_eq_btzCount φ ha hx]

end BTZEntropy
