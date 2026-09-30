import GapFamily.Analytic.Kernel.FullKernelScalarColumnL1
import GapFamily.Analytic.Kernel.FullKernelInverseThreshold

/-! The actual scalar anchor response. Its mass is evaluated through the
ordinary L1 input column and the bounded smoothing map, so the definition is
holomorphic even though arbitrary scalar Hilbert vectors have no mass. -/

noncomputable section

open MeasureTheory Set Real
open scoped BigOperators ComplexConjugate

namespace GapFamily.Analytic

open PoincareScalarFourier

def scalarAnchorResponseHol {ι : Type*} [Fintype ι]
    (J : ι → ℤ) (B : ℝ) (hB : 0 ≤ B) (z : ℂ) : ℂ :=
  -1 - correctedInverseThresholdExpression J B hB
    (correctedScalarColumn J B hB z) (correctedScalarColumnL1 J B hB z)

theorem differentiable_scalarAnchorResponseHol {ι : Type*} [Fintype ι]
    (J : ι → ℤ) (B : ℝ) (hB : 0 ≤ B) :
    Differentiable ℂ (scalarAnchorResponseHol J B hB) :=
  (differentiable_const (-1 : ℂ)).sub (differentiable_correctedInverseThresholdExpression J B hB _ _
    (differentiable_correctedScalarColumn J B hB)
    (differentiable_correctedScalarColumnL1 J B hB))

@[simp] theorem scalarAnchorResponseHol_zero {ι : Type*} [Fintype ι]
    (J : ι → ℤ) (B : ℝ) (hB : 0 ≤ B) : scalarAnchorResponseHol J B hB 0 = -1 := by
  simp [scalarAnchorResponseHol, correctedInverseThresholdExpression]

/-- The holomorphic definition equals minus one minus the actual inverse
column's ordinary threshold mass. -/
theorem scalarAnchorResponseHol_eq_inverse_mass {ι : Type*} [Fintype ι]
    (J : ι → ℤ) (B : ℝ) (hB : 0 ≤ B)
    (hunit : IsUnit (correctedLowBandIdentityPlus J B)) (z : ℂ) :
    scalarAnchorResponseHol J B hB z = -1 - ∑ i,
      scalarThresholdCoefficient (J i) * ∫ e, correctedScalarInverseColumn J B hB z i e
        ∂(referenceMeasure (J i)).restrict (Ioo |(J i : ℝ)| B) := by
  rw [scalarAnchorResponseHol, correctedInverseThresholdExpression_eq_integral J B hB hunit
    _ _ (fun i => (correctedScalarColumnL1_ae J B hB z i).symm)]
  rfl

theorem conj_scalarAnchorResponseHol_ofReal {ι : Type*} [Fintype ι]
    (J : ι → ℤ) (B : ℝ) (hB : 0 ≤ B)
    (hunit : IsUnit (correctedLowBandIdentityPlus J B)) (t : ℝ) :
    conj (scalarAnchorResponseHol J B hB t) = scalarAnchorResponseHol J B hB t := by
  rw [scalarAnchorResponseHol_eq_inverse_mass J B hB hunit]
  simp only [map_sub, map_neg, map_one, map_sum, map_mul, conj_scalarThresholdCoefficient]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  rw [← integral_conj]
  exact integral_congr_ae ((lowBandIsReal_iff_ae J B _).mp
    (correctedScalarInverseColumn_real J B hB hunit t) i)

theorem scalarAnchorResponseHol_ofReal_re {ι : Type*} [Fintype ι]
    (J : ι → ℤ) (B : ℝ) (hB : 0 ≤ B)
    (hunit : IsUnit (correctedLowBandIdentityPlus J B)) (t : ℝ) :
    ((scalarAnchorResponseHol J B hB t).re : ℂ) = scalarAnchorResponseHol J B hB t := by
  have h := conj_scalarAnchorResponseHol_ofReal J B hB hunit t
  apply Complex.ext
  · simp
  · have him := congrArg Complex.im h
    simp only [Complex.conj_im] at him
    simp only [Complex.ofReal_im]
    linarith

/-- The physical scalar response is parametrized by nonnegative input energy. -/
def scalarAnchorResponsePhysical {ι : Type*} [Fintype ι]
    (J : ι → ℤ) (B : ℝ) (hB : 0 ≤ B) (E : ℝ) : ℝ :=
  (scalarAnchorResponseHol J B hB (sqrt (E / B))).re

theorem continuous_scalarAnchorResponsePhysical {ι : Type*} [Fintype ι]
    (J : ι → ℤ) (B : ℝ) (hB : 0 ≤ B) :
    Continuous (scalarAnchorResponsePhysical J B hB) :=
  Complex.continuous_re.comp ((differentiable_scalarAnchorResponseHol J B hB).continuous.comp
    (Complex.continuous_ofReal.comp (Real.continuous_sqrt.comp (continuous_id.div_const B))))

/-- Physical agreement uses the nonnegative square-root coordinate only. -/
theorem scalarAnchorResponseHol_eq_physical {ι : Type*} [Fintype ι]
    (J : ι → ℤ) (B : ℝ) (hB : 0 < B)
    (hunit : IsUnit (correctedLowBandIdentityPlus J B)) (t : ℝ) (ht : 0 ≤ t) :
    scalarAnchorResponseHol J B hB.le t =
      (scalarAnchorResponsePhysical J B hB.le (B * t ^ 2) : ℂ) := by
  unfold scalarAnchorResponsePhysical
  rw [mul_div_cancel_left₀ _ hB.ne', Real.sqrt_sq ht]
  exact (scalarAnchorResponseHol_ofReal_re J B hB.le hunit t).symm

end GapFamily.Analytic
