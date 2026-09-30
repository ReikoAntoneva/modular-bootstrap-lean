import GapFamily.Construction.MarkerReferenceInverseBound
import GapFamily.Construction.MarkerReferenceCanonical
import GapFamily.Analytic.Poincare.Repair.PoincareCanonicalAnchorBound

/-!
# Ordinary mass of the actual marker reference input

The literal unit marker, low-band inverse, and threshold-normalizing anchor
have a uniform polynomial times square-root exponential variation bound.
The estimate retains the coefficient `4π` of `sqrt (a * b)`.
-/

noncomputable section

open MeasureTheory Set Real
open scoped BigOperators
open GapFamily.Analytic

namespace GapFamily.Construction

private theorem variation_real_add_le (μ ν : SignedMeasure ℝ) :
    (μ + ν).variation.real univ ≤ μ.variation.real univ + ν.variation.real univ := by
  simpa using signedMeasure_variation_real_sub_le μ (-ν)

private theorem variation_real_smul (μ : SignedMeasure ℝ) (c : ℝ) :
    (c • μ).variation.real univ = |c| * μ.variation.real univ := by
  simp [VectorMeasure.variation_smul, Measure.real, Measure.smul_apply,
    ENNReal.toReal_mul, Real.norm_eq_abs]

/-- The exact three-term construction obeys its ordinary variation triangle bound. -/
theorem sum_totalVariation_markerReferenceInput_le
    (S : Finset ℤ) (h0 : 0 ∈ S) (a b : ℝ) (ha : 2 ≤ a) (hb : 0 < b)
    (hunit : IsUnit (correctedLowBandIdentityPlus (fun j : S => (j : ℤ)) b)) :
    (∑ j ∈ S, (markerReferenceInput S a b ha hb hunit j).variation.real univ) ≤
      1 + (∑ j ∈ S, (markerReferenceInverseInput S a b ha hb.le hunit j).variation.real univ) +
        |markerReferenceAnchorCoefficient S a b ha hb hunit| *
          ∑ j ∈ S, (actualLocalAnchorInput S b hb hunit j).variation.real univ := by
  have hrow (j : ℤ) :
      (markerReferenceInput S a b ha hb hunit j).variation.real univ ≤
        (markerInput b j).variation.real univ +
          (markerReferenceInverseInput S a b ha hb.le hunit j).variation.real univ +
          |markerReferenceAnchorCoefficient S a b ha hb hunit| *
            (actualLocalAnchorInput S b hb hunit j).variation.real univ := by
    change ((markerInput b j + markerReferenceInverseInput S a b ha hb.le hunit j) +
      markerReferenceAnchorCoefficient S a b ha hb hunit •
        actualLocalAnchorInput S b hb hunit j).variation.real univ ≤ _
    exact (variation_real_add_le _ _).trans
      (add_le_add (variation_real_add_le _ _) (variation_real_smul _ _).le)
  calc
    _ ≤ ∑ j ∈ S, ((markerInput b j).variation.real univ +
        (markerReferenceInverseInput S a b ha hb.le hunit j).variation.real univ +
        |markerReferenceAnchorCoefficient S a b ha hb hunit| *
          (actualLocalAnchorInput S b hb hunit j).variation.real univ) :=
      Finset.sum_le_sum fun j _ => hrow j
    _ = _ := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, markerInput_totalVariation]
      simp [h0]

/-- On the actual physical spin band, threshold mass is controlled by ordinary
variation with one linear cutoff factor. -/
theorem abs_finiteSignedThresholdMass_le_variation (S : Finset ℤ)
    (ν : ℤ → SignedMeasure ℝ) (b : ℝ) (hb : 1 ≤ b)
    (hband : ∀ j ∈ S, |(j : ℝ)| < b) :
    |finiteSignedThresholdMass S ν| ≤
      3 * b * ∑ j ∈ S, (ν j).variation.real univ := by
  rw [finiteSignedThresholdMass, Finset.mul_sum]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro j hj
  rw [abs_mul]
  let := signedMeasure_isFiniteMeasure_variation (ν j)
  have hm : |ν j univ| ≤ (ν j).variation.real univ := by
    simpa only [Real.norm_eq_abs] using
      (VectorMeasure.norm_measure_le_variation (μ := ν j) (E := univ))
  exact mul_le_mul
    (PoincareScalarFourier.abs_re_scalarThresholdCoefficient_le_physical j b hb
      (hband j hj).le) hm (abs_nonneg _) (by linarith)

/-- A fixed positive coefficient for the actual reference input. -/
def markerReferenceInputCoefficient : ℝ := 8 + 4 * markerReferenceInverseCoefficient

theorem markerReferenceInputCoefficient_pos : 0 < markerReferenceInputCoefficient := by
  unfold markerReferenceInputCoefficient
  have := markerReferenceInverseCoefficient_pos
  positivity

/-- A fixed positive rate includes both the actual inverse and the actual anchor. -/
def markerReferenceInputExponent : ℝ :=
  correctedLowBandCoercivityExponent + canonicalLocalAnchorExponent

theorem markerReferenceInputExponent_pos : 0 < markerReferenceInputExponent := by
  unfold markerReferenceInputExponent
  exact add_pos correctedLowBandCoercivityExponent_pos canonicalLocalAnchorExponent_pos

private theorem reference_mass_absorb (C P A b : ℝ)
    (hC : 0 ≤ C) (hP : 1 ≤ P) (hA : 1 ≤ A) (hb : 1 ≤ b) :
    1 + C * P + (7 + 3 * b * (C * P)) * A ≤ (8 + 4 * C) * (b * P * A) := by
  have hP0 : 0 ≤ P := zero_le_one.trans hP
  have hA0 : 0 ≤ A := zero_le_one.trans hA
  have hbP : 1 ≤ b * P := one_le_mul_of_one_le_of_one_le hb hP
  have h1 : 1 ≤ b * P * A := one_le_mul_of_one_le_of_one_le hbP hA
  have hPZ : P ≤ b * P * A := by
    calc
      P ≤ b * P := le_mul_of_one_le_left hP0 hb
      _ ≤ b * P * A := le_mul_of_one_le_right (by positivity) hA
  have hAZ : A ≤ b * P * A := le_mul_of_one_le_left hA0 hbP
  calc
    _ = 1 + C * P + 7 * A + 3 * C * (b * P * A) := by ring
    _ ≤ (b * P * A) + C * (b * P * A) + 7 * (b * P * A) +
        3 * C * (b * P * A) := by
      exact add_le_add (add_le_add
        (add_le_add h1 (mul_le_mul_of_nonneg_left hPZ hC))
        (mul_le_mul_of_nonneg_left hAZ (show (0 : ℝ) ≤ 7 by norm_num))) le_rfl
    _ = _ := by ring

/-- The actual canonical input has a fixed polynomial variation bound, with
the sharp vacuum square-root exponent and no external inverse hypothesis. -/
theorem signedSeedMass_canonicalMarkerReferenceInput_le (a b : ℝ)
    (ha : 2 ≤ a) (hb : 1 ≤ b) :
    signedSeedMass (fun J : lowBandSpinSet b => canonicalMarkerReferenceInput a b ha hb J) ≤
      markerReferenceInputCoefficient * (1 + a) * b ^ 6 *
        exp (4 * π * sqrt (a * b) + markerReferenceInputExponent * b) := by
  have hb0 : 0 ≤ b := zero_le_one.trans hb
  have hbpos : 0 < b := zero_lt_one.trans_le hb
  have h0 : 0 ∈ lowBandSpinSet b := (zero_mem_lowBandSpinSet b).mpr hbpos
  let hunit := isUnit_correctedLowBandIdentityPlus_canonical b hb
  let μ := markerReferenceInverseInput (lowBandSpinSet b) a b ha hb0 hunit
  let U := ∑ j ∈ lowBandSpinSet b, (μ j).variation.real univ
  let P := (1 + a) * b ^ 5 *
    exp (4 * π * sqrt (a * b) + correctedLowBandCoercivityExponent * b)
  let A := exp (canonicalLocalAnchorExponent * b)
  have hU : 0 ≤ U := Finset.sum_nonneg fun _ _ => measureReal_nonneg
  have hP : 1 ≤ P := by
    exact one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le (by linarith) (one_le_pow₀ hb))
      (one_le_exp (by
        have := correctedLowBandCoercivityExponent_pos.le
        positivity))
  have hA : 1 ≤ A := one_le_exp
    (mul_nonneg canonicalLocalAnchorExponent_pos.le hb0)
  have hμ : U ≤ markerReferenceInverseCoefficient * P := by
    calc
      U = ∑ j : lowBandSpinSet b,
          (markerReferenceInverseMeasure (fun j : lowBandSpinSet b => (j : ℤ))
            a b ha hb0 hunit j).variation.real univ := by
        dsimp [U, μ]
        rw [← Finset.sum_coe_sort]
        apply Finset.sum_congr rfl
        intro j _
        rw [markerReferenceInverseInput_apply _ _ _ _ _ _ j j.property]
      _ ≤ markerReferenceInverseCoefficient * (1 + a) * b ^ 5 *
          exp (4 * π * sqrt (a * b) + correctedLowBandCoercivityExponent * b) :=
        sum_totalVariation_markerReferenceInverseMeasure_le_exp
          (fun j : lowBandSpinSet b => (j : ℤ)) Subtype.val_injective a b ha hb
          (fun j => (mem_lowBandSpinSet b j).mp j.property) hunit
      _ = _ := by dsimp [P]; ring
  have ht : |markerReferenceAnchorCoefficient (lowBandSpinSet b) a b ha hbpos hunit| ≤
      7 + 3 * b * U := by
    change |7 - finiteSignedThresholdMass (lowBandSpinSet b) μ| ≤ _
    calc
      _ ≤ |(7 : ℝ)| + |finiteSignedThresholdMass (lowBandSpinSet b) μ| := abs_sub _ _
      _ ≤ 7 + 3 * b * U := by
        rw [abs_of_nonneg (show (0 : ℝ) ≤ 7 by norm_num)]
        exact add_le_add le_rfl (abs_finiteSignedThresholdMass_le_variation
          (lowBandSpinSet b) μ b hb (fun j hj => (mem_lowBandSpinSet b j).mp hj))
  have hθ : (∑ j ∈ lowBandSpinSet b,
      (actualLocalAnchorInput (lowBandSpinSet b) b hbpos hunit j).variation.real univ) ≤ A :=
    sum_totalVariation_canonicalLocalAnchorInput_le_exp b hb
  have hraw : signedSeedMass
      (fun J : lowBandSpinSet b => canonicalMarkerReferenceInput a b ha hb J) ≤
      1 + U + |markerReferenceAnchorCoefficient (lowBandSpinSet b) a b ha hbpos hunit| *
        ∑ j ∈ lowBandSpinSet b,
          (actualLocalAnchorInput (lowBandSpinSet b) b hbpos hunit j).variation.real univ := by
    rw [signedSeedMass, Finset.sum_coe_sort (lowBandSpinSet b)
      (fun j : ℤ => (canonicalMarkerReferenceInput a b ha hb j).variation.real univ)]
    exact sum_totalVariation_markerReferenceInput_le (lowBandSpinSet b) h0 a b ha hbpos hunit
  calc
    _ ≤ 1 + U + (7 + 3 * b * U) * A := hraw.trans
      (add_le_add le_rfl (mul_le_mul ht hθ
        (Finset.sum_nonneg fun _ _ => measureReal_nonneg) (by positivity)))
    _ ≤ 1 + markerReferenceInverseCoefficient * P +
        (7 + 3 * b * (markerReferenceInverseCoefficient * P)) * A := by
      gcongr
    _ ≤ (8 + 4 * markerReferenceInverseCoefficient) * (b * P * A) :=
      reference_mass_absorb _ _ _ _ markerReferenceInverseCoefficient_pos.le hP hA hb
    _ = _ := by
      dsimp [P, A, markerReferenceInputCoefficient, markerReferenceInputExponent]
      simp only [add_mul, exp_add]
      ring

end GapFamily.Construction
