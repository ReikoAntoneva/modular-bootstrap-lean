import GapFamily.Construction.MarkerReferenceDensityBound

/-! Ordinary absolute and negative mass of the actual canonical reference.
The reference's growing positive part is integrated only on finite bands;
its entire negative part is integrable and confined below the fixed cutoff. -/

noncomputable section

open MeasureTheory Set Real
open scoped BigOperators
open GapFamily.Analytic

namespace GapFamily.Construction

/-- The complete actual density has the same compact polynomial-exponential
bound as the literal direct input and full kernel numerator. -/
theorem integral_abs_canonicalMarkerReferenceDensity_le
    (R a b : ℝ) (hR : 1 ≤ R) (ha : 2 ≤ a) (hb : 1 ≤ b) (hba : b ≤ a) (j : ℤ) :
    (∫ e, |canonicalMarkerReferenceDensity a b ha hb j e|
      ∂(referenceMeasure j).restrict (Ioo |(j : ℝ)| (R * b))) ≤
      markerReferenceCompactMassCoefficient R * (1 + a) ^ 9 *
        exp (markerReferenceCompactMassExponent R * sqrt (a * b)) := by
  have hd := canonicalMarkerReferenceDirectDensity_integrable a b ha hb j
  have hk := canonicalMarkerReferenceKernelNumerator_integrable a b (R * b) ha hb j
  have hdm : (∫ e, |canonicalMarkerReferenceDirectDensity a b ha hb j e| ∂referenceMeasure j) ≤
      signedSeedMass (fun J : lowBandSpinSet b => canonicalMarkerReferenceInput a b ha hb J) + 1 := by
    simpa only [Finset.sum_singleton] using
      sum_integral_abs_canonicalMarkerReferenceDirectDensity_le {j} a b ha hb
  calc
    _ ≤ (∫ e, |canonicalMarkerReferenceDirectDensity a b ha hb j e|
        ∂(referenceMeasure j).restrict (Ioo |(j : ℝ)| (R * b))) +
        ∫ e, |canonicalMarkerReferenceKernelNumerator a b ha hb j e|
          ∂(referenceMeasure j).restrict (Ioo |(j : ℝ)| (R * b)) := by
      rw [← integral_add hd.restrict.abs hk.abs]
      exact integral_mono_ae (canonicalMarkerReferenceDensity_integrable a b (R * b) ha hb j).abs
        (hd.restrict.abs.add hk.abs) (Filter.Eventually.of_forall fun e => abs_add_le _ _)
    _ ≤ (∫ e, |canonicalMarkerReferenceDirectDensity a b ha hb j e| ∂referenceMeasure j) +
        ∫ e, |canonicalMarkerReferenceKernelNumerator a b ha hb j e|
          ∂(referenceMeasure j).restrict (Ioo |(j : ℝ)| (R * b)) :=
      add_le_add (setIntegral_le_integral hd.abs (Filter.Eventually.of_forall fun _ => abs_nonneg _)) le_rfl
    _ ≤ (signedSeedMass (fun J : lowBandSpinSet b => canonicalMarkerReferenceInput a b ha hb J) + 1) +
        ∫ e, |canonicalMarkerReferenceKernelNumerator a b ha hb j e|
          ∂(referenceMeasure j).restrict (Ioo |(j : ℝ)| (R * b)) := add_le_add hdm le_rfl
    _ = 1 + signedSeedMass (fun J : lowBandSpinSet b => canonicalMarkerReferenceInput a b ha hb J) +
        ∫ e, |canonicalMarkerReferenceKernelNumerator a b ha hb j e|
          ∂(referenceMeasure j).restrict (Ioo |(j : ℝ)| (R * b)) := by ring
    _ ≤ _ := canonicalMarkerReference_compactMass_le R a b hR ha hb hba j

/-- A fixed positive coefficient bounds every low-row negative mass. -/
def markerReferenceNegativeCoefficient : ℝ :=
  markerReferenceCompactMassCoefficient ((markerReferenceRadius : ℝ) + 1)

theorem markerReferenceNegativeCoefficient_pos : 0 < markerReferenceNegativeCoefficient :=
  markerReferenceCompactMassCoefficient_pos _ (by positivity)

/-- The fixed negative-mass exponent is chosen before the later initial-cell
ratio and therefore supports the ordered parameter choice. -/
def markerReferenceNegativeExponent : ℝ :=
  markerReferenceCompactMassExponent ((markerReferenceRadius : ℝ) + 1)

theorem markerReferenceNegativeExponent_pos : 0 < markerReferenceNegativeExponent :=
  markerReferenceCompactMassExponent_pos _

/-- The actual ordinary negative mass obeys the square-root exponential
bound uniformly on every spin `|j| ≤ T`. -/
theorem canonicalMarkerReferenceDensity_negativeMass_le
    (a b : ℝ) (ha : 2 ≤ a) (hb : 1 ≤ b) (j : ℤ)
    (hnb : (markerReferenceBandThreshold : ℝ) ≤ b) (hba : b ≤ a)
    (hj : |(j : ℝ)| ≤ (markerReferenceRadius : ℝ) * b) :
    (∫ e, max (-canonicalMarkerReferenceDensity a b ha hb j e) 0 ∂referenceMeasure j) ≤
      markerReferenceNegativeCoefficient * (1 + a) ^ 9 *
        exp (markerReferenceNegativeExponent * sqrt (a * b)) := by
  let Z := (markerReferenceRadius : ℝ) * b + 1
  let W := ((markerReferenceRadius : ℝ) + 1) * b
  have hZW : Z ≤ W := by dsimp [Z, W]; nlinarith
  have hqZ := canonicalMarkerReferenceDensity_integrable a b Z ha hb j
  have hqW := canonicalMarkerReferenceDensity_integrable a b W ha hb j
  rw [canonicalMarkerReferenceDensity_negativeMass_eq_cutoff a b ha hb j hnb hba hj]
  calc
    _ ≤ ∫ e in Ioo |(j : ℝ)| Z,
        |canonicalMarkerReferenceDensity a b ha hb j e| ∂referenceMeasure j := by
      apply integral_mono_ae hqZ.neg_part hqZ.abs
      exact Filter.Eventually.of_forall fun e => max_le (neg_le_abs _) (abs_nonneg _)
    _ ≤ ∫ e in Ioo |(j : ℝ)| W,
        |canonicalMarkerReferenceDensity a b ha hb j e| ∂referenceMeasure j :=
      setIntegral_mono_set hqW.abs (Filter.Eventually.of_forall fun _ => abs_nonneg _)
        (Filter.Eventually.of_forall fun _ he => ⟨he.1, he.2.trans_le hZW⟩)
    _ ≤ _ := integral_abs_canonicalMarkerReferenceDensity_le
      ((markerReferenceRadius : ℝ) + 1) a b (by exact le_add_of_nonneg_left (Nat.cast_nonneg _)) ha hb hba j

/-- The finite family of low-spin rows has one combined ordinary negative-mass
bound. Its constants are fixed before any later initial-cell parameter. -/
theorem sum_negativeMass_canonicalMarkerReferenceDensity_le
    (S : Finset ℤ) (a b : ℝ) (ha : 2 ≤ a) (hb : 1 ≤ b)
    (hnb : (markerReferenceBandThreshold : ℝ) ≤ b) (hba : b ≤ a)
    (hS : ∀ j ∈ S, |(j : ℝ)| ≤ (markerReferenceRadius : ℝ) * b) :
    (∑ j ∈ S, ∫ e, max (-canonicalMarkerReferenceDensity a b ha hb j e) 0
      ∂referenceMeasure j) ≤
      (5 * ((markerReferenceRadius : ℝ) + 1) * markerReferenceNegativeCoefficient) *
        (1 + a) ^ 10 * exp (markerReferenceNegativeExponent * sqrt (a * b)) := by
  let R : ℝ := (markerReferenceRadius : ℝ) + 1
  have hR : 1 ≤ R := by dsimp [R]; exact le_add_of_nonneg_left (Nat.cast_nonneg _)
  have hbpos : 0 < b := by linarith
  have hn : (S.card : ℝ) ≤ 5 * (R * b) := by
    simpa only [Fintype.card_coe] using
      physicalLowBand_card_le (fun j : S => (j : ℤ)) Subtype.val_injective
        (one_le_mul_of_one_le_of_one_le hR hb)
        (fun j => (hS j j.property).trans_lt (by dsimp [R]; nlinarith))
  have hC := markerReferenceNegativeCoefficient_pos.le
  have hE := exp_nonneg (markerReferenceNegativeExponent * sqrt (a * b))
  have ha0 : 0 ≤ a := by linarith
  calc
    _ ≤ ∑ _j ∈ S, markerReferenceNegativeCoefficient * (1 + a) ^ 9 *
        exp (markerReferenceNegativeExponent * sqrt (a * b)) :=
      Finset.sum_le_sum fun j hj =>
        canonicalMarkerReferenceDensity_negativeMass_le a b ha hb j hnb hba (hS j hj)
    _ = (S.card : ℝ) * (markerReferenceNegativeCoefficient * (1 + a) ^ 9 *
        exp (markerReferenceNegativeExponent * sqrt (a * b))) := by simp
    _ ≤ (5 * (R * b)) * (markerReferenceNegativeCoefficient * (1 + a) ^ 9 *
        exp (markerReferenceNegativeExponent * sqrt (a * b))) :=
      mul_le_mul_of_nonneg_right hn (by positivity)
    _ = (5 * R * markerReferenceNegativeCoefficient) * (b * (1 + a) ^ 9) *
        exp (markerReferenceNegativeExponent * sqrt (a * b)) := by ring
    _ ≤ (5 * R * markerReferenceNegativeCoefficient) * ((1 + a) * (1 + a) ^ 9) *
        exp (markerReferenceNegativeExponent * sqrt (a * b)) := by
      gcongr
      linarith
    _ = _ := by dsimp [R]; ring

/-- Logarithmic form of the combined negative-mass estimate: the only growing
terms are a fixed square-root exponent and ten logarithms of the vacuum scale. -/
theorem log_one_add_sum_negativeMass_canonicalMarkerReferenceDensity_le
    (S : Finset ℤ) (a b : ℝ) (ha : 2 ≤ a) (hb : 1 ≤ b)
    (hnb : (markerReferenceBandThreshold : ℝ) ≤ b) (hba : b ≤ a)
    (hS : ∀ j ∈ S, |(j : ℝ)| ≤ (markerReferenceRadius : ℝ) * b) :
    log (1 + ∑ j ∈ S, ∫ e, max (-canonicalMarkerReferenceDensity a b ha hb j e) 0
      ∂referenceMeasure j) ≤
      log (1 + 5 * ((markerReferenceRadius : ℝ) + 1) * markerReferenceNegativeCoefficient) +
        10 * log (1 + a) + markerReferenceNegativeExponent * sqrt (a * b) := by
  let N := ∑ j ∈ S, ∫ e, max (-canonicalMarkerReferenceDensity a b ha hb j e) 0
    ∂referenceMeasure j
  let C := 5 * ((markerReferenceRadius : ℝ) + 1) * markerReferenceNegativeCoefficient
  let X := (1 + a) ^ 10 * exp (markerReferenceNegativeExponent * sqrt (a * b))
  have hN : 0 ≤ N := Finset.sum_nonneg fun _ _ => integral_nonneg fun _ => le_max_right _ _
  have hC : 0 < C := by
    dsimp [C]
    have := markerReferenceNegativeCoefficient_pos
    positivity
  have hX : 1 ≤ X := by
    apply one_le_mul_of_one_le_of_one_le
    · exact one_le_pow₀ (by linarith)
    · exact one_le_exp (mul_nonneg markerReferenceNegativeExponent_pos.le (sqrt_nonneg _))
  have hbound : N ≤ C * X := by
    simpa only [N, C, X, mul_assoc] using
      sum_negativeMass_canonicalMarkerReferenceDensity_le S a b ha hb hnb hba hS
  have htot : 1 + N ≤ (1 + C) * X := by nlinarith
  change log (1 + N) ≤ _
  calc
    _ ≤ log ((1 + C) * X) := Real.log_le_log (by linarith) htot
    _ = _ := by
      dsimp [X, C]
      rw [Real.log_mul (by positivity) (by positivity),
        Real.log_mul (by positivity) (exp_ne_zero _), Real.log_pow, Real.log_exp]
      norm_num
      ring

end GapFamily.Construction
