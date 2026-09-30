import GapFamily.Construction.MarkerReferenceBound
import GapFamily.Construction.MarkerReferenceInverse
import GapFamily.Analytic.Kernel.FullKernelInverse

/-!
# Ordinary variation bounds for the actual marker inverse

The actual signed inverse measure is bounded first by its true inverse norm.
Physical spin counting and the proved inverse estimate then give a polynomial
times the required square-root exponential envelope.
-/

noncomputable section

open MeasureTheory Real Set
open GapFamily.Analytic

namespace GapFamily.Construction

variable {ι : Type*} [Fintype ι]

/-- The ordinary mass majorant of one actual source row. -/
def markerReferenceSourceMassBound (a b : ℝ) : ℝ :=
  markerReferenceEnergyBound a b * b +
    (correctedKernelBound * sqrt b) * (b + 2 * sqrt b)

/-- The Hilbert majorant of one actual source row. -/
def markerReferenceSourceNormBound (a b : ℝ) : ℝ :=
  (markerReferenceEnergyBound a b + correctedKernelBound) * b

theorem markerReferenceSourceMassBound_nonneg (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ markerReferenceSourceMassBound a b := by
  unfold markerReferenceSourceMassBound
  have := markerReferenceEnergyBound_nonneg a b ha
  have := correctedKernelBound_pos
  positivity

theorem markerReferenceSourceNormBound_nonneg (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ markerReferenceSourceNormBound a b := by
  unfold markerReferenceSourceNormBound
  have := markerReferenceEnergyBound_nonneg a b ha
  have := correctedKernelBound_pos
  positivity

/-- The actual Hilbert inverse retains the source's square-root row-count bound. -/
theorem norm_markerReferenceInverse_le (J : ι → ℤ) (a b : ℝ)
    (ha : 2 ≤ a) (hb : 0 ≤ b) :
    ‖markerReferenceInverse J a b ha hb‖ ≤
      ‖Ring.inverse (correctedLowBandIdentityPlus J b)‖ *
        sqrt (Fintype.card ι : ℝ) * markerReferenceSourceNormBound a b := by
  calc
    _ ≤ ‖Ring.inverse (correctedLowBandIdentityPlus J b)‖ *
        ‖markerReferenceRhsHilbert J a b ha hb‖ :=
      (Ring.inverse (correctedLowBandIdentityPlus J b)).le_opNorm _
    _ ≤ ‖Ring.inverse (correctedLowBandIdentityPlus J b)‖ *
        (sqrt (Fintype.card ι : ℝ) * markerReferenceSourceNormBound a b) :=
      mul_le_mul_of_nonneg_left (norm_markerReferenceRhsHilbert_le J a b ha hb) (norm_nonneg _)
    _ = _ := by ring

/-- Ordinary variation of a single signed inverse row, retaining the true inverse norm. -/
theorem markerReferenceInverseMeasure_totalVariation_le (J : ι → ℤ) (a b : ℝ)
    (ha : 2 ≤ a) (hb : 0 ≤ b) (hunit : IsUnit (correctedLowBandIdentityPlus J b)) (i : ι) :
    (markerReferenceInverseMeasure J a b ha hb hunit i).variation.real univ ≤
      markerReferenceSourceMassBound a b +
        correctedSmoothingBound b * (Fintype.card ι : ℝ) *
          ‖Ring.inverse (correctedLowBandIdentityPlus J b)‖ * markerReferenceSourceNormBound a b := by
  have hsource : (∫ e, ‖markerReferenceRhsHilbert J a b ha hb i e‖
      ∂(referenceMeasure (J i)).restrict (Ioo |(J i : ℝ)| b)) ≤
      markerReferenceSourceMassBound a b := by
    calc
      _ = ∫ e, ‖markerReferenceRhs a b (J i) e‖
          ∂(referenceMeasure (J i)).restrict (Ioo |(J i : ℝ)| b) := by
        apply integral_congr_ae
        exact (markerReferenceRhsHilbert_coeFn J a b ha hb i).fun_comp (fun z : ℂ => ‖z‖)
      _ ≤ _ := integral_norm_markerReferenceRhs_le a b (J i) ha hb
  have hs := correctedLowBandInverseSignedMeasure_totalVariation_le J b hb hunit
    (markerReferenceRhsHilbert J a b ha hb) (markerReferenceRhsHilbert_integrable J a b ha hb)
    (markerReferenceRhsHilbert_real J a b ha hb) i
  calc
    _ ≤ (∫ e, ‖markerReferenceRhsHilbert J a b ha hb i e‖
        ∂(referenceMeasure (J i)).restrict (Ioo |(J i : ℝ)| b)) +
        correctedSmoothingBound b * sqrt (Fintype.card ι : ℝ) *
          ‖Ring.inverse (correctedLowBandIdentityPlus J b)‖ *
            ‖markerReferenceRhsHilbert J a b ha hb‖ := hs
    _ ≤ markerReferenceSourceMassBound a b +
        correctedSmoothingBound b * sqrt (Fintype.card ι : ℝ) *
          ‖Ring.inverse (correctedLowBandIdentityPlus J b)‖ *
            (sqrt (Fintype.card ι : ℝ) * markerReferenceSourceNormBound a b) := by
      apply add_le_add hsource
      exact mul_le_mul_of_nonneg_left (norm_markerReferenceRhsHilbert_le J a b ha hb)
        (mul_nonneg (mul_nonneg (correctedSmoothingBound_nonneg b hb) (sqrt_nonneg _))
          (norm_nonneg _))
    _ = _ := by
      have hn := sq_sqrt (Nat.cast_nonneg (α := ℝ) (Fintype.card ι))
      ring_nf
      rw [hn]
      ring

/-- Total ordinary variation of the actual inverse family, with its true inverse norm. -/
theorem sum_totalVariation_markerReferenceInverseMeasure_le (J : ι → ℤ) (a b : ℝ)
    (ha : 2 ≤ a) (hb : 0 ≤ b) (hunit : IsUnit (correctedLowBandIdentityPlus J b)) :
    (∑ i, (markerReferenceInverseMeasure J a b ha hb hunit i).variation.real univ) ≤
      (Fintype.card ι : ℝ) * markerReferenceSourceMassBound a b +
        (Fintype.card ι : ℝ) ^ 2 * correctedSmoothingBound b *
          ‖Ring.inverse (correctedLowBandIdentityPlus J b)‖ * markerReferenceSourceNormBound a b := by
  calc
    _ ≤ ∑ _i : ι, (markerReferenceSourceMassBound a b +
        correctedSmoothingBound b * (Fintype.card ι : ℝ) *
          ‖Ring.inverse (correctedLowBandIdentityPlus J b)‖ * markerReferenceSourceNormBound a b) :=
      Finset.sum_le_sum fun i _ => markerReferenceInverseMeasure_totalVariation_le J a b ha hb hunit i
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

private theorem markerReferenceSourceNormBound_le_envelope (a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    markerReferenceSourceNormBound a b ≤ 2 * markerReferenceEnvelope a b * b := by
  unfold markerReferenceSourceNormBound
  have h := add_le_add (markerReferenceEnergyBound_le_envelope a b ha)
    (correctedKernelBound_le_markerReferenceEnvelope a b ha)
  calc
    _ ≤ (markerReferenceEnvelope a b + markerReferenceEnvelope a b) * b :=
      mul_le_mul_of_nonneg_right h hb
    _ = _ := by ring

private theorem markerReferenceSourceMassBound_le_envelope (a b : ℝ)
    (ha : 0 ≤ a) (hb : 1 ≤ b) :
    markerReferenceSourceMassBound a b ≤ 4 * markerReferenceEnvelope a b * b ^ 2 := by
  have hb0 : 0 ≤ b := zero_le_one.trans hb
  have hE := markerReferenceEnvelope_nonneg a b ha
  have hs : sqrt b ≤ b := sqrt_le_self_iff.mpr (Or.inr hb)
  have hbb : b ≤ b ^ 2 := by nlinarith
  calc
    _ ≤ markerReferenceEnvelope a b * b +
        (markerReferenceEnvelope a b * sqrt b) * (b + 2 * sqrt b) := by
      unfold markerReferenceSourceMassBound
      gcongr
      · exact markerReferenceEnergyBound_le_envelope a b ha
      · exact correctedKernelBound_le_markerReferenceEnvelope a b ha
    _ ≤ markerReferenceEnvelope a b * b ^ 2 +
        (markerReferenceEnvelope a b * b) * (b + 2 * b) := by
      gcongr
    _ = _ := by ring

/-- A fixed positive coefficient for the total inverse variation envelope. -/
def markerReferenceInverseCoefficient : ℝ :=
  (20 + 200 * correctedKernelBound) * markerReferenceCoefficient

theorem markerReferenceInverseCoefficient_pos : 0 < markerReferenceInverseCoefficient := by
  unfold markerReferenceInverseCoefficient
  have := correctedKernelBound_pos
  have := markerReferenceCoefficient_pos
  positivity

/-- Physical spin counting and the actual inverse give C5's ordinary variation
growth: a fixed polynomial times `exp(4π sqrt(ab) + C b)`. -/
theorem sum_totalVariation_markerReferenceInverseMeasure_le_exp
    (J : ι → ℤ) (hJ : Function.Injective J) (a b : ℝ)
    (ha : 2 ≤ a) (hb : 1 ≤ b) (hband : ∀ i, |(J i : ℝ)| < b)
    (hunit : IsUnit (correctedLowBandIdentityPlus J b)) :
    (∑ i, (markerReferenceInverseMeasure J a b ha (zero_le_one.trans hb) hunit i).variation.real univ) ≤
      markerReferenceInverseCoefficient * (1 + a) * b ^ 5 *
        exp (4 * π * sqrt (a * b) + correctedLowBandCoercivityExponent * b) := by
  have ha0 : 0 ≤ a := by linarith
  have hb0 : 0 ≤ b := zero_le_one.trans hb
  have hC := correctedKernelBound_pos.le
  have hE := markerReferenceEnvelope_nonneg a b ha0
  have hS := correctedSmoothingBound_nonneg b hb0
  have hL := markerReferenceSourceMassBound_nonneg a b ha0 hb0
  have hK := markerReferenceSourceNormBound_nonneg a b ha0 hb0
  have hn := physicalLowBand_card_le J hJ hb hband
  have hinv : ‖Ring.inverse (correctedLowBandIdentityPlus J b)‖ ≤
      exp (correctedLowBandCoercivityExponent * b) :=
    norm_correctedLowBandInverse_le_exp J hJ b hb hband
  have hlarge : 1 ≤ exp (correctedLowBandCoercivityExponent * b) :=
    one_le_exp (mul_nonneg correctedLowBandCoercivityExponent_pos.le hb0)
  have hp : b ^ 3 ≤ b ^ 5 := pow_le_pow_right₀ hb (by norm_num : 3 ≤ 5)
  calc
    _ ≤ (Fintype.card ι : ℝ) * markerReferenceSourceMassBound a b +
        (Fintype.card ι : ℝ) ^ 2 * correctedSmoothingBound b *
          ‖Ring.inverse (correctedLowBandIdentityPlus J b)‖ * markerReferenceSourceNormBound a b :=
      sum_totalVariation_markerReferenceInverseMeasure_le J a b ha hb0 hunit
    _ ≤ (5 * b) * (4 * markerReferenceEnvelope a b * b ^ 2) +
        (5 * b) ^ 2 * (4 * correctedKernelBound * b ^ 2) *
          exp (correctedLowBandCoercivityExponent * b) * (2 * markerReferenceEnvelope a b * b) := by
      gcongr
      · exact markerReferenceSourceMassBound_le_envelope a b ha0 hb
      · exact correctedSmoothingBound_le b hb
      · exact markerReferenceSourceNormBound_le_envelope a b ha0 hb0
    _ = 20 * markerReferenceEnvelope a b * b ^ 3 +
        200 * correctedKernelBound * markerReferenceEnvelope a b * b ^ 5 *
          exp (correctedLowBandCoercivityExponent * b) := by ring
    _ ≤ 20 * markerReferenceEnvelope a b * b ^ 5 *
          exp (correctedLowBandCoercivityExponent * b) +
        200 * correctedKernelBound * markerReferenceEnvelope a b * b ^ 5 *
          exp (correctedLowBandCoercivityExponent * b) := by
      refine add_le_add ?_ le_rfl
      calc
        _ ≤ 20 * markerReferenceEnvelope a b * b ^ 5 :=
          mul_le_mul_of_nonneg_left hp (by positivity)
        _ ≤ _ := le_mul_of_one_le_right (by positivity) hlarge
    _ = _ := by
      rw [exp_add]
      unfold markerReferenceInverseCoefficient markerReferenceEnvelope
      ring

/-- The physical version uses the proved inverse directly, with no invertibility hypothesis. -/
theorem sum_totalVariation_markerReferenceInverseMeasure_le_physical
    (J : ι → ℤ) (hJ : Function.Injective J) (a b : ℝ)
    (ha : 2 ≤ a) (hb : 1 ≤ b) (hband : ∀ i, |(J i : ℝ)| < b) :
    (∑ i, (markerReferenceInverseMeasure J a b ha (zero_le_one.trans hb)
      (isUnit_correctedLowBandIdentityPlus J hJ b hb hband) i).variation.real univ) ≤
      markerReferenceInverseCoefficient * (1 + a) * b ^ 5 *
        exp (4 * π * sqrt (a * b) + correctedLowBandCoercivityExponent * b) :=
  sum_totalVariation_markerReferenceInverseMeasure_le_exp J hJ a b ha hb hband
    (isUnit_correctedLowBandIdentityPlus J hJ b hb hband)

end GapFamily.Construction
