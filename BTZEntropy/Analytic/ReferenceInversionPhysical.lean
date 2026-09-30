import BTZEntropy.Analytic.ReferenceInversionPhysicalData
import BTZEntropy.Analytic.ReferenceInversionTransform
import BTZEntropy.Analytic.ReferenceInversionDescendant
import BTZEntropy.Analytic.ReferenceInversionMeasure
import BTZEntropy.Comparison.InitialPacket
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-!
# The complete physical reference distribution

The continuous primary density is combined with counting measure on every pair
of descendant levels. Both its Laplace transform and its smoothing are literal
integrals of this same weighted energy distribution.
-/

noncomputable section

open MeasureTheory

namespace BTZEntropy

/-- The actual complete-state reference Laplace transform. -/
def physicalComplexLaplace (a : ℝ) (z : ℂ) : ℂ :=
  ∫ p, (physicalReferenceWeight a p : ℂ) *
    Complex.exp (-z * (physicalReferenceEnergy p : ℂ)) ∂physicalReferenceMeasure

/-- The actual complete-state reference count, smoothed in cylinder energy. -/
def physicalSmoothCount (φ : SmoothKernel) (a E : ℝ) : ℝ :=
  ∫ p, physicalReferenceWeight a p * φ (physicalReferenceEnergy p - E)
    ∂physicalReferenceMeasure

theorem norm_complexPartitionThermalTerm (z : ℂ) (n : ℕ) :
    ‖(partitionCount n : ℂ) * Complex.exp (-z * (n : ℂ))‖ =
      partitionThermalTerm z.re n := by
  rw [norm_mul, Complex.norm_natCast, Complex.norm_exp]
  simp [partitionThermalTerm]

/-- Absolute convergence of the descendant pair with counting measure. -/
theorem integrable_complexPartitionPair_count {z : ℂ} (hz : 0 < z.re) :
    Integrable (fun v : ℕ × ℕ =>
      ((partitionCount v.1 : ℂ) * Complex.exp (-z * (v.1 : ℂ))) *
        ((partitionCount v.2 : ℂ) * Complex.exp (-z * (v.2 : ℂ)))) Measure.count := by
  apply integrable_count_iff.mpr
  simp only [norm_mul, Complex.norm_natCast, Complex.norm_exp]
  simpa [partitionThermalTerm] using
    (summable_partitionThermalTerm hz).mul_of_nonneg
      (summable_partitionThermalTerm hz) (partitionThermalTerm_nonneg z.re)
      (partitionThermalTerm_nonneg z.re)

theorem integral_complexPartitionPair_count {z : ℂ} (hz : 0 < z.re) :
    (∫ v : ℕ × ℕ,
      ((partitionCount v.1 : ℂ) * Complex.exp (-z * (v.1 : ℂ))) *
        ((partitionCount v.2 : ℂ) * Complex.exp (-z * (v.2 : ℂ))) ∂Measure.count) =
      (∑' n : ℕ, (partitionCount n : ℂ) * Complex.exp (-z * (n : ℂ))) ^ 2 := by
  have hi := integrable_complexPartitionPair_count hz
  have hs := (integrable_count_iff.mp hi).of_norm
  rw [integral_countable hi]
  simp only [count_real_singleton, one_smul]
  rw [hs.tsum_prod]
  simp only [tsum_mul_left, tsum_mul_right, pow_two]

/-- The complex moment has the same absolute majorant as its real thermal moment. -/
theorem integrable_physicalComplexThermal {a : ℝ} {z : ℂ}
    (ha : 2 ≤ a) (hz : 0 < z.re) :
    Integrable (fun p => (physicalReferenceWeight a p : ℂ) *
      Complex.exp (-z * (physicalReferenceEnergy p : ℂ))) physicalReferenceMeasure := by
  apply (integrable_physicalReferenceThermal ha hz).mono'
  · exact ((measurable_physicalReferenceWeight a).complex_ofReal.mul
      (Complex.measurable_exp.comp (measurable_const.mul
        measurable_physicalReferenceEnergy.complex_ofReal))).aestronglyMeasurable
  · filter_upwards [] with p
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (physicalReferenceWeight_nonneg ha p), Complex.norm_exp]
    simp

/-- Exact factorization into the primary transform and both descendant series. -/
theorem physicalComplexLaplace_eq_series {a : ℝ} {z : ℂ}
    (_ha : 2 ≤ a) (hz : 0 < z.re) :
    physicalComplexLaplace a z =
      Complex.exp (z / 12) * complexReferencePrimaryTransform a z *
        (∑' n : ℕ, (partitionCount n : ℂ) * Complex.exp (-z * (n : ℂ))) ^ 2 := by
  unfold physicalComplexLaplace
  simp_rw [physicalReferenceComplexThermal_factorization,
    mul_assoc (Complex.exp (z / 12))]
  rw [integral_const_mul, physicalReferenceMeasure,
    integral_prod_mul
      (fun p : ℝ × ℝ => (referencePrimaryDensity a p.1 p.2 : ℂ) *
        Complex.exp (-z * (p.1 : ℂ)))
      (fun v : ℕ × ℕ => ((partitionCount v.1 : ℂ) * Complex.exp (-z * (v.1 : ℂ))) *
        ((partitionCount v.2 : ℂ) * Complex.exp (-z * (v.2 : ℂ)))),
    integral_complexPartitionPair_count hz]
  have hp : (∫ p : ℝ × ℝ,
      (referencePrimaryDensity a p.1 p.2 : ℂ) * Complex.exp (-z * (p.1 : ℂ))
        ∂volume.restrict referenceCone) = complexReferencePrimaryTransform a z := by
    unfold complexReferencePrimaryTransform
    apply integral_congr_ae
    filter_upwards [] with p
    exact mul_comm _ _
  rw [hp]

/-- The complete reference Laplace transform contains the actual Euler product. -/
theorem physicalComplexLaplace_eq {a : ℝ} {z : ℂ}
    (ha : 2 ≤ a) (hz : 0 < z.re) :
    physicalComplexLaplace a z =
      Complex.exp (z / 12) * complexReferencePrimaryTransform a z *
        (complexEulerProduct (Complex.exp (-z)))⁻¹ ^ 2 := by
  rw [physicalComplexLaplace_eq_series ha hz, tsum_complexPartitionThermal hz]

/-- Every compact smoothing of the physical distribution is integrable. -/
theorem integrable_physicalSmoothTerm (φ : SmoothKernel) {a : ℝ}
    (ha : 2 ≤ a) (E : ℝ) :
    Integrable (fun p => physicalReferenceWeight a p *
      φ (physicalReferenceEnergy p - E)) physicalReferenceMeasure := by
  exact integrable_weightedSmoothCount φ 1 E physicalReferenceEnergy
    (physicalReferenceWeight a) measurable_physicalReferenceEnergy
    (measurable_physicalReferenceWeight a)
    (integrable_physicalReferenceThermal ha (by norm_num))

/-- Fubini identifies the literal weighted smoothing with all descendant modules. -/
theorem physicalSmoothCount_eq_modules (φ : SmoothKernel) {a : ℝ}
    (ha : 2 ≤ a) (E : ℝ) :
    physicalSmoothCount φ a E =
      ∫ p : ℝ × ℝ in referenceCone,
        referencePrimaryDensity a p.1 p.2 *
          Comparison.moduleSmoothCount φ (fun n => (partitionCount n : ℝ))
            (p.1 - 1 / 12) E := by
  have hi := integrable_physicalSmoothTerm φ ha E
  unfold physicalSmoothCount physicalReferenceMeasure
  rw [integral_prod _ hi]
  apply integral_congr_ae
  filter_upwards [hi.prod_right_ae] with p hp
  rw [integral_countable hp]
  simp only [count_real_singleton, one_smul, Comparison.moduleSmoothCount,
    ← tsum_mul_left]
  apply tsum_congr
  intro v
  unfold physicalReferenceWeight physicalReferenceEnergy Comparison.moduleSmoothTerm
  dsimp only
  rw [show p.1 + (v.1 : ℝ) + (v.2 : ℝ) - 1 / 12 - E =
    p.1 - 1 / 12 + (v.1 : ℝ) + (v.2 : ℝ) - E by ring]
  ring

end BTZEntropy
