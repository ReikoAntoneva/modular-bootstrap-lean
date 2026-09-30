import GapFamily.Analytic.Kernel.FullKernelInputColumn
import GapFamily.Analytic.Kernel.FullKernelCoercivity
import GapFamily.Analytic.Kernel.FullKernelInverseThreshold

/-! Entire input columns for the actual bounded low-band inverse. The ordinary
threshold mass uses the simultaneous L1 column and the proved smoothing map;
no ordinary mass functional is asserted on arbitrary scalar Hilbert vectors. -/

noncomputable section

open MeasureTheory Real Set
open scoped BigOperators ComplexConjugate

namespace GapFamily.Analytic

open PoincareScalarFourier

variable {ι : Type*} [Fintype ι]

/-- The actual inverse applied to the entire corrected input column. -/
def correctedInputInverseColumn (J : ι → ℤ) (B : ℝ) (hB : 0 ≤ B)
    (jin : ℤ) (z : ℂ) : LowBandHilbert J B :=
  correctedLowBandInverse J B (correctedInputColumn J B hB jin z)

theorem differentiable_correctedInputInverseColumn (J : ι → ℤ) (B : ℝ)
    (hB : 0 ≤ B) (jin : ℤ) :
    Differentiable ℂ (correctedInputInverseColumn J B hB jin) :=
  (correctedLowBandInverse J B).differentiable.comp
    (differentiable_correctedInputColumn J B hB jin)

/-- Invertibility makes the entire inverse column real at every real parameter. -/
theorem correctedInputInverseColumn_real (J : ι → ℤ) (B : ℝ) (hB : 0 ≤ B)
    (hunit : IsUnit (correctedLowBandIdentityPlus J B)) (jin : ℤ) (t : ℝ) :
    LowBandIsReal J B (correctedInputInverseColumn J B hB jin (t : ℂ)) :=
  (correctedInputColumn_real J B hB jin t).correctedLowBandInverse J B hunit

/-- A disk bound retaining the norm of the actual inverse operator. -/
theorem norm_correctedInputInverseColumn_le (J : ι → ℤ) (B : ℝ) (hB : 0 ≤ B)
    (jin : ℤ) (R : ℝ) (hR : 0 ≤ R) (z : ℂ) (hz : ‖z‖ ≤ R) :
    ‖correctedInputInverseColumn J B hB jin z‖ ≤
      ‖correctedLowBandInverse J B‖ * (Fintype.card ι : ℝ) *
        (fullKernelCompactBound jin B (|(jin : ℝ)| + R ^ 2) * B + 12 * R * sqrt B) := by
  calc
    _ ≤ ‖correctedLowBandInverse J B‖ * ‖correctedInputColumn J B hB jin z‖ :=
      (correctedLowBandInverse J B).le_opNorm _
    _ ≤ ‖correctedLowBandInverse J B‖ * ((Fintype.card ι : ℝ) *
        (fullKernelCompactBound jin B (|(jin : ℝ)| + R ^ 2) * B + 12 * R * sqrt B)) :=
      mul_le_mul_of_nonneg_left
        (norm_correctedInputColumn_le J B hB jin R hR z hz) (norm_nonneg _)
    _ = _ := by ring

/-- Every row of the actual inverse column has ordinary L1 mass. -/
theorem correctedInputInverseColumn_integrable (J : ι → ℤ) (B : ℝ) (hB : 0 ≤ B)
    (hunit : IsUnit (correctedLowBandIdentityPlus J B)) (jin : ℤ) (z : ℂ) (i : ι) :
    Integrable (correctedInputInverseColumn J B hB jin z i)
      ((referenceMeasure (J i)).restrict (Ioo |(J i : ℝ)| B)) :=
  correctedLowBandInverse_integrable J B hB hunit _
    (correctedInputColumn_integrable J B hB jin z) i

/-- The inverse column's ordinary L1 representative, formed using bounded
smoothing after the Hilbert inverse. -/
def correctedInputInverseColumnL1 (J : ι → ℤ) (B : ℝ) (hB : 0 ≤ B)
    (jin : ℤ) (z : ℂ) : CorrectedKernelSmoothingSpace J B :=
  correctedInputColumnL1 J B hB jin z -
    correctedKernelFiniteSmoothingOperator J J B hB (correctedInputInverseColumn J B hB jin z)

theorem differentiable_correctedInputInverseColumnL1 (J : ι → ℤ) (B : ℝ)
    (hB : 0 ≤ B) (jin : ℤ) :
    Differentiable ℂ (correctedInputInverseColumnL1 J B hB jin) :=
  (differentiable_correctedInputColumnL1 J B hB jin).sub
    ((correctedKernelFiniteSmoothingOperator J J B hB).differentiable.comp
      (differentiable_correctedInputInverseColumn J B hB jin))

/-- The entire L1 column and actual Hilbert inverse have the same representative. -/
theorem correctedInputInverseColumnL1_ae (J : ι → ℤ) (B : ℝ) (hB : 0 ≤ B)
    (hunit : IsUnit (correctedLowBandIdentityPlus J B)) (jin : ℤ) (z : ℂ) (i : ι) :
    ⇑(correctedInputInverseColumnL1 J B hB jin z i) =ᵐ[
      (referenceMeasure (J i)).restrict (Ioo |(J i : ℝ)| B)]
      ⇑(correctedInputInverseColumn J B hB jin z i) := by
  simp only [correctedInputInverseColumnL1, PiLp.sub_apply,
    correctedKernelFiniteSmoothingOperator_apply]
  filter_upwards [Lp.coeFn_sub (correctedInputColumnL1 J B hB jin z i)
    (correctedKernelSmoothingOperator J B hB (J i)
      (correctedInputInverseColumn J B hB jin z)),
    correctedInputColumnL1_ae J B hB jin z i,
    coeFn_correctedKernelSmoothingOperator_eq_lowBandOperator J B hB
      (correctedInputInverseColumn J B hB jin z) i,
    correctedLowBandInverse_coeFn_eq_sub J B hunit (correctedInputColumn J B hB jin z) i]
    with E hsub hcol hsm hinv
  simp only [Pi.sub_apply] at hsub
  rw [hsub, hcol, hsm]
  exact hinv.symm

/-- The ordinary inverse norm is controlled by input mass and bounded smoothing. -/
theorem norm_correctedInputInverseColumnL1_le (J : ι → ℤ) (B : ℝ) (hB : 0 ≤ B)
    (jin : ℤ) (z : ℂ) :
    ‖correctedInputInverseColumnL1 J B hB jin z‖ ≤
      ‖correctedInputColumnL1 J B hB jin z‖ +
        (Fintype.card ι : ℝ) * (correctedSmoothingBound B * sqrt (Fintype.card ι : ℝ)) *
          ‖correctedInputInverseColumn J B hB jin z‖ :=
  (norm_sub_le _ _).trans (add_le_add le_rfl
    (norm_correctedKernelFiniteSmoothingOperator_apply_le J J B hB _))

theorem norm_correctedInputInverseColumnL1_eq_integral (J : ι → ℤ) (B : ℝ) (hB : 0 ≤ B)
    (hunit : IsUnit (correctedLowBandIdentityPlus J B)) (jin : ℤ) (z : ℂ) :
    ‖correctedInputInverseColumnL1 J B hB jin z‖ =
      ∑ i, ∫ e, ‖correctedInputInverseColumn J B hB jin z i e‖
        ∂(referenceMeasure (J i)).restrict (Ioo |(J i : ℝ)| B) := by
  rw [PiLp.norm_eq_of_L1]
  apply Finset.sum_congr rfl
  intro i hi
  rw [L1.norm_eq_integral_norm]
  apply integral_congr_ae
  exact (correctedInputInverseColumnL1_ae J B hB hunit jin z i).mono
    (fun _ he => congrArg norm he)

/-- The bounded expression for the inverse column's weighted ordinary mass. -/
def correctedInputInverseThreshold (J : ι → ℤ) (B : ℝ) (hB : 0 ≤ B)
    (jin : ℤ) (z : ℂ) : ℂ :=
  correctedInverseThresholdExpression J B hB (correctedInputColumn J B hB jin z)
    (correctedInputColumnL1 J B hB jin z)

theorem differentiable_correctedInputInverseThreshold (J : ι → ℤ) (B : ℝ)
    (hB : 0 ≤ B) (jin : ℤ) :
    Differentiable ℂ (correctedInputInverseThreshold J B hB jin) :=
  differentiable_correctedInverseThresholdExpression J B hB _ _
    (differentiable_correctedInputColumn J B hB jin)
    (differentiable_correctedInputColumnL1 J B hB jin)

theorem correctedInputInverseThreshold_eq_L1 (J : ι → ℤ) (B : ℝ) (hB : 0 ≤ B)
    (jin : ℤ) (z : ℂ) :
    correctedInputInverseThreshold J B hB jin z =
      lowBandThresholdFunctional J B (correctedInputInverseColumnL1 J B hB jin z) := by
  simp only [correctedInputInverseThreshold, correctedInverseThresholdExpression,
    correctedInputInverseColumnL1, map_sub, correctedSmoothingThresholdFunctional,
    ContinuousLinearMap.comp_apply, correctedInputInverseColumn, correctedLowBandInverse]

/-- Under actual invertibility, the entire expression is exactly the ordinary
weighted integral of the inverse column on all physical input rows. -/
theorem correctedInputInverseThreshold_eq_integral (J : ι → ℤ) (B : ℝ) (hB : 0 ≤ B)
    (hunit : IsUnit (correctedLowBandIdentityPlus J B)) (jin : ℤ) (z : ℂ) :
    correctedInputInverseThreshold J B hB jin z =
      ∑ i, scalarThresholdCoefficient (J i) *
        ∫ e, correctedInputInverseColumn J B hB jin z i e
          ∂(referenceMeasure (J i)).restrict (Ioo |(J i : ℝ)| B) :=
  correctedInverseThresholdExpression_eq_integral J B hB hunit _ _
    (fun i => (correctedInputColumnL1_ae J B hB jin z i).symm)

/-- The weighted inverse mass is real for every real input parameter. -/
theorem conj_correctedInputInverseThreshold_ofReal (J : ι → ℤ) (B : ℝ) (hB : 0 ≤ B)
    (hunit : IsUnit (correctedLowBandIdentityPlus J B)) (jin : ℤ) (t : ℝ) :
    conj (correctedInputInverseThreshold J B hB jin (t : ℂ)) =
      correctedInputInverseThreshold J B hB jin t := by
  rw [correctedInputInverseThreshold_eq_integral J B hB hunit]
  simp only [map_sum, map_mul, conj_scalarThresholdCoefficient]
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  rw [← integral_conj]
  exact integral_congr_ae ((lowBandIsReal_iff_ae J B _).mp
    (correctedInputInverseColumn_real J B hB hunit jin t) i)

theorem correctedInputInverseThreshold_ofReal_im (J : ι → ℤ) (B : ℝ) (hB : 0 ≤ B)
    (hunit : IsUnit (correctedLowBandIdentityPlus J B)) (jin : ℤ) (t : ℝ) :
    (correctedInputInverseThreshold J B hB jin (t : ℂ)).im = 0 :=
  Complex.conj_eq_iff_im.mp (conj_correctedInputInverseThreshold_ofReal J B hB hunit jin t)

end GapFamily.Analytic
