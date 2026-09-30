import BTZEntropy.Analytic.IntegerReferenceInversionData
import BTZEntropy.Analytic.ReferenceInversionPhysical

/-!
# Complete integer-spin reference Laplace transform

The integer-spin primary reference and both descendant towers are integrated
against the same physical weighted measure. The exact residual cylinder shift
appears as `exp (z / 12)`.
-/

noncomputable section

open MeasureTheory

namespace BTZEntropy

/-- The actual complete integer-spin reference Laplace transform. -/
def integerReferenceComplexLaplace (a : ℝ) (z : ℂ) : ℂ :=
  weightedComplexLaplace integerReferenceMeasure integerReferenceEnergy
    (integerReferenceWeight a) z

/-- Every positive real thermal moment also controls the complex vertical line. -/
theorem integrable_integerReferenceComplexThermal {a : ℝ} {z : ℂ}
    (ha : 2 ≤ a) (hz : 0 < z.re) :
    Integrable (fun p => (integerReferenceWeight a p : ℂ) *
      Complex.exp (-z * (integerReferenceEnergy p : ℂ))) integerReferenceMeasure :=
  integrable_weightedComplexLaplace_integrand measurable_integerReferenceEnergy
    (measurable_integerReferenceWeight a) (integrable_integerReferenceThermal ha hz)

/-- Literal product-measure integration separates the two descendant series. -/
theorem integerReferenceComplexLaplace_eq_series {a : ℝ} {z : ℂ}
    (_ha : 2 ≤ a) (hz : 0 < z.re) :
    integerReferenceComplexLaplace a z =
      Complex.exp (z / 12) * integerSpinPrimaryComplexTransform a z *
        (∑' n : ℕ, (partitionCount n : ℂ) * Complex.exp (-z * (n : ℂ))) ^ 2 := by
  unfold integerReferenceComplexLaplace weightedComplexLaplace
  simp_rw [integerReferenceComplexThermal_factorization,
    mul_assoc (Complex.exp (z / 12))]
  rw [integral_const_mul, integerReferenceMeasure,
    integral_prod_mul
      (fun q : ℤ × ℝ => (spinReferenceWeight a q : ℂ) *
        Complex.exp (-z * (spinReferenceEnergy q : ℂ)))
      (fun v : ℕ × ℕ => ((partitionCount v.1 : ℂ) * Complex.exp (-z * (v.1 : ℂ))) *
        ((partitionCount v.2 : ℂ) * Complex.exp (-z * (v.2 : ℂ)))),
    integral_complexPartitionPair_count hz]
  rfl

/-- The exact full-state integer-spin transform contains the actual reciprocal Euler product. -/
theorem integerReferenceComplexLaplace_eq {a : ℝ} {z : ℂ}
    (ha : 2 ≤ a) (hz : 0 < z.re) :
    integerReferenceComplexLaplace a z =
      Complex.exp (z / 12) * integerSpinPrimaryComplexTransform a z *
        (complexEulerProduct (Complex.exp (-z)))⁻¹ ^ 2 := by
  rw [integerReferenceComplexLaplace_eq_series ha hz, tsum_complexPartitionThermal hz]

end BTZEntropy
