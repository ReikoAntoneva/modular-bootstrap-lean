import GapFamily.Construction.FixedCutoffReferenceDensity
import GapFamily.Construction.FixedCutoffMarkerTransferExteriorBound
import GapFamily.Construction.MarkerReferenceDensityMass

/-! Ordinary compact and negative mass of the fixed-cutoff reference.
All coefficients are chosen before the marker position in `[0,B]`.
The scalar reference measure is controlled by the output-energy zero of
the transfer density, including on the anchor's direct band. -/

noncomputable section

open MeasureTheory Set Real
open scoped BigOperators
open GapFamily.Analytic

namespace GapFamily.Construction

private theorem fixedCutoffLowBand_integral_energy_le (j : ℤ) (W : ℝ) (hW : 0 ≤ W) :
    (∫ e, e ∂(referenceMeasure j).restrict (Ioo |(j : ℝ)| W)) ≤ W := by
  by_cases hj : |(j : ℝ)| ≤ W
  · rw [lowBand_integral_energy j hj]
    exact (sqrt_le_left hW).mpr (by nlinarith [sq_nonneg (j : ℝ)])
  · simp [Ioo_eq_empty_of_le (le_of_not_ge hj), hW]

/-- The complete transfer density has at most linear energy growth. -/
theorem abs_fixedCutoffMarkerRepairDensity_le
    (B δ : ℝ) (hB : 1 ≤ B) (hδ : 0 ≤ δ) (hδB : δ ≤ B)
    (e : ℝ) (j : ℤ) (he : |(j : ℝ)| ≤ e) :
    |fixedCutoffMarkerRepairDensity B δ hB j e| ≤
      e * exp (fixedCutoffMarkerTransferExteriorExponent * B) := by
  by_cases hcut : 2 * B < e
  · rw [fixedCutoffMarkerRepairDensity, indicator_of_mem (show e ∈ Ioi (2 * B) from hcut)]
    exact abs_re_canonicalRepairExteriorNumerator_fixedCutoffMarkerTransfer_le
      B δ hB hδ hδB e j he hcut.le
  · rw [fixedCutoffMarkerRepairDensity, indicator_of_notMem (show e ∉ Ioi (2 * B) from hcut), abs_zero]
    exact mul_nonneg ((abs_nonneg _).trans he) (exp_pos _).le

/-- The literal transfer, including its direct anchor band, has a compact
ordinary mass bound uniform in the prescribed marker energy. -/
theorem integral_abs_fixedCutoffMarkerRepairDensity_le
    (W B δ : ℝ) (hW : 0 ≤ W) (hB : 1 ≤ B) (hδ : 0 ≤ δ) (hδB : δ ≤ B)
    (j : ℤ) :
    (∫ e, |fixedCutoffMarkerRepairDensity B δ hB j e|
      ∂(referenceMeasure j).restrict (Ioo |(j : ℝ)| W)) ≤
      W * exp (fixedCutoffMarkerTransferExteriorExponent * B) := by
  have hr : Integrable (fixedCutoffMarkerRepairDensity B δ hB j)
      ((referenceMeasure j).restrict (Ioo |(j : ℝ)| W)) :=
    (integrableOn_re_canonicalRepairExteriorNumerator (fixedCutoffMarkerTransfer B δ)
      (2 * B) (by linarith) (fixedCutoffMarkerTransfer_repairSupport B δ hB hδ hδB)
      j W).indicator measurableSet_Ioi
  calc
    _ ≤ ∫ e, exp (fixedCutoffMarkerTransferExteriorExponent * B) * e
        ∂(referenceMeasure j).restrict (Ioo |(j : ℝ)| W) := by
      apply integral_mono_ae hr.abs ((lowBand_energy_integrable j W).const_mul _)
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with e he
      simpa only [mul_comm] using
        abs_fixedCutoffMarkerRepairDensity_le B δ hB hδ hδB e j he.1.le
    _ = exp (fixedCutoffMarkerTransferExteriorExponent * B) *
        ∫ e, e ∂(referenceMeasure j).restrict (Ioo |(j : ℝ)| W) := integral_const_mul _ _
    _ ≤ exp (fixedCutoffMarkerTransferExteriorExponent * B) * W :=
      mul_le_mul_of_nonneg_left (fixedCutoffLowBand_integral_energy_le j W hW) (exp_pos _).le
    _ = _ := by ring

/-- A compact-mass coefficient fixed independently of the marker position. -/
def fixedCutoffReferenceCompactMassCoefficient (R : ℝ) : ℝ :=
  markerReferenceCompactMassCoefficient R + R

theorem fixedCutoffReferenceCompactMassCoefficient_pos (R : ℝ) (hR : 0 ≤ R) :
    0 < fixedCutoffReferenceCompactMassCoefficient R :=
  add_pos_of_pos_of_nonneg (markerReferenceCompactMassCoefficient_pos R hR) hR

/-- A square-root exponential rate covering both the vacuum reference and
the complete marker-transfer repair. -/
def fixedCutoffReferenceCompactMassExponent (R : ℝ) : ℝ :=
  markerReferenceCompactMassExponent R + fixedCutoffMarkerTransferExteriorExponent

theorem fixedCutoffReferenceCompactMassExponent_pos (R : ℝ) :
    0 < fixedCutoffReferenceCompactMassExponent R :=
  add_pos (markerReferenceCompactMassExponent_pos R)
    fixedCutoffMarkerTransferExteriorExponent_pos

/-- The same compact ordinary absolute-mass budget applies to all marker
positions in the closed interval `[0,B]`, including zero. -/
theorem integral_abs_fixedCutoffReferenceDensity_le
    (R a B δ : ℝ) (hR : 1 ≤ R) (ha : 2 ≤ a) (hB : 1 ≤ B)
    (hδ : 0 ≤ δ) (hδB : δ ≤ B) (hBa : B ≤ a) (j : ℤ) :
    (∫ e, |fixedCutoffReferenceDensity a B δ ha hB j e|
      ∂(referenceMeasure j).restrict (Ioo |(j : ℝ)| (R * B))) ≤
      fixedCutoffReferenceCompactMassCoefficient R * (1 + a) ^ 9 *
        exp (fixedCutoffReferenceCompactMassExponent R * sqrt (a * B)) := by
  have hR0 : 0 ≤ R := zero_le_one.trans hR
  have hB0 : 0 ≤ B := zero_le_one.trans hB
  have ha0 : 0 ≤ a := by linarith
  have hBS : B ≤ sqrt (a * B) := by
    apply (le_sqrt hB0 (mul_nonneg ha0 hB0)).2
    nlinarith only [mul_le_mul_of_nonneg_right hBa hB0]
  have hBP : B ≤ (1 + a) ^ 9 := by
    calc
      B ≤ 1 + a := by linarith
      _ = (1 + a) ^ 1 := by ring
      _ ≤ _ := pow_le_pow_right₀ (by linarith) (by norm_num)
  let E := exp (fixedCutoffReferenceCompactMassExponent R * sqrt (a * B))
  have hOldExp : exp (markerReferenceCompactMassExponent R * sqrt (a * B)) ≤ E := by
    apply exp_le_exp.mpr
    dsimp [fixedCutoffReferenceCompactMassExponent]
    nlinarith only [mul_nonneg fixedCutoffMarkerTransferExteriorExponent_pos.le (sqrt_nonneg (a * B))]
  have hTransferExp : exp (fixedCutoffMarkerTransferExteriorExponent * B) ≤ E := by
    apply exp_le_exp.mpr
    calc
      _ ≤ fixedCutoffMarkerTransferExteriorExponent * sqrt (a * B) :=
        mul_le_mul_of_nonneg_left hBS fixedCutoffMarkerTransferExteriorExponent_pos.le
      _ ≤ fixedCutoffReferenceCompactMassExponent R * sqrt (a * B) := by
        unfold fixedCutoffReferenceCompactMassExponent
        nlinarith only [mul_nonneg (markerReferenceCompactMassExponent_pos R).le (sqrt_nonneg (a * B))]
  have hc := canonicalMarkerReferenceDensity_integrable a B (R * B) ha hB j
  have hr : Integrable (fixedCutoffMarkerRepairDensity B δ hB j)
      ((referenceMeasure j).restrict (Ioo |(j : ℝ)| (R * B))) :=
    (integrableOn_re_canonicalRepairExteriorNumerator (fixedCutoffMarkerTransfer B δ)
      (2 * B) (by linarith) (fixedCutoffMarkerTransfer_repairSupport B δ hB hδ hδB)
      j (R * B)).indicator measurableSet_Ioi
  calc
    _ ≤ (∫ e, |canonicalMarkerReferenceDensity a B ha hB j e|
        ∂(referenceMeasure j).restrict (Ioo |(j : ℝ)| (R * B))) +
        ∫ e, |fixedCutoffMarkerRepairDensity B δ hB j e|
          ∂(referenceMeasure j).restrict (Ioo |(j : ℝ)| (R * B)) := by
      rw [← integral_add hc.abs hr.abs]
      apply integral_mono_ae
        (fixedCutoffReferenceDensity_integrable a B δ ha hB hδ hδB (R * B) j).abs
        (hc.abs.add hr.abs)
      exact Filter.Eventually.of_forall fun e => abs_add_le _ _
    _ ≤ markerReferenceCompactMassCoefficient R * (1 + a) ^ 9 *
        exp (markerReferenceCompactMassExponent R * sqrt (a * B)) +
        (R * B) * exp (fixedCutoffMarkerTransferExteriorExponent * B) :=
      add_le_add (integral_abs_canonicalMarkerReferenceDensity_le R a B hR ha hB hBa j)
        (integral_abs_fixedCutoffMarkerRepairDensity_le (R * B) B δ (mul_nonneg hR0 hB0)
          hB hδ hδB j)
    _ ≤ markerReferenceCompactMassCoefficient R * (1 + a) ^ 9 * E +
        (R * (1 + a) ^ 9) * E := by
      have hC := (markerReferenceCompactMassCoefficient_pos R hR0).le
      gcongr
    _ = _ := by dsimp [E, fixedCutoffReferenceCompactMassCoefficient]; ring

private theorem fixedCutoffReferenceDensity_nonneg_off_cutoff
    (a B δ : ℝ) (ha : 2 ≤ a) (hB : 1 ≤ B) (hδ : 0 ≤ δ) (hδB : δ ≤ B) (j : ℤ)
    (hnB : (fixedCutoffReferenceBandThreshold : ℝ) ≤ B) (hBa : B ≤ a)
    (hj : |(j : ℝ)| ≤ (fixedCutoffReferenceRadius : ℝ) * B) :
    ∀ᵐ e ∂(referenceMeasure j).restrict
      (Ioo |(j : ℝ)| ((fixedCutoffReferenceRadius : ℝ) * B + 1))ᶜ,
      0 ≤ fixedCutoffReferenceDensity a B δ ha hB j e := by
  filter_upwards [ae_restrict_of_ae (referenceMeasure_ae_above_edge j),
    ae_restrict_mem measurableSet_Ioo.compl] with e hedge hout
  have he : (fixedCutoffReferenceRadius : ℝ) * B + 1 ≤ e := by
    by_contra h
    exact hout ⟨hedge, lt_of_not_ge h⟩
  exact (fixedCutoffReferenceDensity_pos_above a B δ ha hB hδ hδB j hnB hBa hj he).le

/-- Its entire negative part is ordinarily integrable. -/
theorem fixedCutoffReferenceDensity_negativePart_integrable
    (a B δ : ℝ) (ha : 2 ≤ a) (hB : 1 ≤ B) (hδ : 0 ≤ δ) (hδB : δ ≤ B) (j : ℤ)
    (hnB : (fixedCutoffReferenceBandThreshold : ℝ) ≤ B) (hBa : B ≤ a)
    (hj : |(j : ℝ)| ≤ (fixedCutoffReferenceRadius : ℝ) * B) :
    Integrable (fun e => max (-fixedCutoffReferenceDensity a B δ ha hB j e) 0)
      (referenceMeasure j) :=
  integrable_negPart_of_local measurableSet_Ioo
    (fixedCutoffReferenceDensity_integrable a B δ ha hB hδ hδB
      ((fixedCutoffReferenceRadius : ℝ) * B + 1) j)
    (fixedCutoffReferenceDensity_nonneg_off_cutoff a B δ ha hB hδ hδB j hnB hBa hj)

/-- All ordinary negative mass is confined to one uniform compact band. -/
theorem fixedCutoffReferenceDensity_negativeMass_eq_cutoff
    (a B δ : ℝ) (ha : 2 ≤ a) (hB : 1 ≤ B) (hδ : 0 ≤ δ) (hδB : δ ≤ B) (j : ℤ)
    (hnB : (fixedCutoffReferenceBandThreshold : ℝ) ≤ B) (hBa : B ≤ a)
    (hj : |(j : ℝ)| ≤ (fixedCutoffReferenceRadius : ℝ) * B) :
    (∫ e, max (-fixedCutoffReferenceDensity a B δ ha hB j e) 0 ∂referenceMeasure j) =
      ∫ e in Ioo |(j : ℝ)| ((fixedCutoffReferenceRadius : ℝ) * B + 1),
        max (-fixedCutoffReferenceDensity a B δ ha hB j e) 0 ∂referenceMeasure j :=
  integral_negPart_eq_setIntegral measurableSet_Ioo
    (fixedCutoffReferenceDensity_nonneg_off_cutoff a B δ ha hB hδ hδB j hnB hBa hj)

/-- A fixed positive coefficient bounds every low-row negative mass. -/
def fixedCutoffReferenceNegativeCoefficient : ℝ :=
  fixedCutoffReferenceCompactMassCoefficient ((fixedCutoffReferenceRadius : ℝ) + 1)

theorem fixedCutoffReferenceNegativeCoefficient_pos : 0 < fixedCutoffReferenceNegativeCoefficient :=
  fixedCutoffReferenceCompactMassCoefficient_pos _ (by positivity)

/-- The fixed negative-mass exponent is chosen before the later initial-cell
ratio and therefore supports the ordered parameter choice. -/
def fixedCutoffReferenceNegativeExponent : ℝ :=
  fixedCutoffReferenceCompactMassExponent ((fixedCutoffReferenceRadius : ℝ) + 1)

theorem fixedCutoffReferenceNegativeExponent_pos : 0 < fixedCutoffReferenceNegativeExponent :=
  fixedCutoffReferenceCompactMassExponent_pos _

/-- The actual ordinary negative mass obeys the square-root exponential
bound uniformly on every spin `|j| ≤ T`. -/
theorem fixedCutoffReferenceDensity_negativeMass_le
    (a b δ : ℝ) (ha : 2 ≤ a) (hb : 1 ≤ b)
    (hδ : 0 ≤ δ) (hδb : δ ≤ b) (j : ℤ)
    (hnb : (fixedCutoffReferenceBandThreshold : ℝ) ≤ b) (hba : b ≤ a)
    (hj : |(j : ℝ)| ≤ (fixedCutoffReferenceRadius : ℝ) * b) :
    (∫ e, max (-fixedCutoffReferenceDensity a b δ ha hb j e) 0 ∂referenceMeasure j) ≤
      fixedCutoffReferenceNegativeCoefficient * (1 + a) ^ 9 *
        exp (fixedCutoffReferenceNegativeExponent * sqrt (a * b)) := by
  let Z := (fixedCutoffReferenceRadius : ℝ) * b + 1
  let W := ((fixedCutoffReferenceRadius : ℝ) + 1) * b
  have hZW : Z ≤ W := by dsimp [Z, W]; nlinarith
  have hqZ := fixedCutoffReferenceDensity_integrable a b δ ha hb hδ hδb Z j
  have hqW := fixedCutoffReferenceDensity_integrable a b δ ha hb hδ hδb W j
  rw [fixedCutoffReferenceDensity_negativeMass_eq_cutoff a b δ ha hb hδ hδb j hnb hba hj]
  calc
    _ ≤ ∫ e in Ioo |(j : ℝ)| Z,
        |fixedCutoffReferenceDensity a b δ ha hb j e| ∂referenceMeasure j := by
      apply integral_mono_ae hqZ.neg_part hqZ.abs
      exact Filter.Eventually.of_forall fun e => max_le (neg_le_abs _) (abs_nonneg _)
    _ ≤ ∫ e in Ioo |(j : ℝ)| W,
        |fixedCutoffReferenceDensity a b δ ha hb j e| ∂referenceMeasure j :=
      setIntegral_mono_set hqW.abs (Filter.Eventually.of_forall fun _ => abs_nonneg _)
        (Filter.Eventually.of_forall fun _ he => ⟨he.1, he.2.trans_le hZW⟩)
    _ ≤ _ := integral_abs_fixedCutoffReferenceDensity_le
      ((fixedCutoffReferenceRadius : ℝ) + 1) a b δ (by exact le_add_of_nonneg_left (Nat.cast_nonneg _)) ha hb hδ hδb hba j

/-- The finite family of low-spin rows has one combined ordinary negative-mass
bound. Its constants are fixed before any later initial-cell parameter. -/
theorem sum_negativeMass_fixedCutoffReferenceDensity_le
    (S : Finset ℤ) (a b δ : ℝ) (ha : 2 ≤ a) (hb : 1 ≤ b)
    (hδ : 0 ≤ δ) (hδb : δ ≤ b)
    (hnb : (fixedCutoffReferenceBandThreshold : ℝ) ≤ b) (hba : b ≤ a)
    (hS : ∀ j ∈ S, |(j : ℝ)| ≤ (fixedCutoffReferenceRadius : ℝ) * b) :
    (∑ j ∈ S, ∫ e, max (-fixedCutoffReferenceDensity a b δ ha hb j e) 0
      ∂referenceMeasure j) ≤
      (5 * ((fixedCutoffReferenceRadius : ℝ) + 1) * fixedCutoffReferenceNegativeCoefficient) *
        (1 + a) ^ 10 * exp (fixedCutoffReferenceNegativeExponent * sqrt (a * b)) := by
  let R : ℝ := (fixedCutoffReferenceRadius : ℝ) + 1
  have hR : 1 ≤ R := by dsimp [R]; exact le_add_of_nonneg_left (Nat.cast_nonneg _)
  have hbpos : 0 < b := by linarith
  have hn : (S.card : ℝ) ≤ 5 * (R * b) := by
    simpa only [Fintype.card_coe] using
      physicalLowBand_card_le (fun j : S => (j : ℤ)) Subtype.val_injective
        (one_le_mul_of_one_le_of_one_le hR hb)
        (fun j => (hS j j.property).trans_lt (by dsimp [R]; nlinarith))
  have hC := fixedCutoffReferenceNegativeCoefficient_pos.le
  have hE := exp_nonneg (fixedCutoffReferenceNegativeExponent * sqrt (a * b))
  have ha0 : 0 ≤ a := by linarith
  calc
    _ ≤ ∑ _j ∈ S, fixedCutoffReferenceNegativeCoefficient * (1 + a) ^ 9 *
        exp (fixedCutoffReferenceNegativeExponent * sqrt (a * b)) :=
      Finset.sum_le_sum fun j hj =>
        fixedCutoffReferenceDensity_negativeMass_le a b δ ha hb hδ hδb j hnb hba (hS j hj)
    _ = (S.card : ℝ) * (fixedCutoffReferenceNegativeCoefficient * (1 + a) ^ 9 *
        exp (fixedCutoffReferenceNegativeExponent * sqrt (a * b))) := by simp
    _ ≤ (5 * (R * b)) * (fixedCutoffReferenceNegativeCoefficient * (1 + a) ^ 9 *
        exp (fixedCutoffReferenceNegativeExponent * sqrt (a * b))) :=
      mul_le_mul_of_nonneg_right hn (by positivity)
    _ = (5 * R * fixedCutoffReferenceNegativeCoefficient) * (b * (1 + a) ^ 9) *
        exp (fixedCutoffReferenceNegativeExponent * sqrt (a * b)) := by ring
    _ ≤ (5 * R * fixedCutoffReferenceNegativeCoefficient) * ((1 + a) * (1 + a) ^ 9) *
        exp (fixedCutoffReferenceNegativeExponent * sqrt (a * b)) := by
      gcongr
      linarith
    _ = _ := by dsimp [R]; ring

/-- Logarithmic form of the combined negative-mass estimate: the only growing
terms are a fixed square-root exponent and ten logarithms of the vacuum scale. -/
theorem log_one_add_sum_negativeMass_fixedCutoffReferenceDensity_le
    (S : Finset ℤ) (a b δ : ℝ) (ha : 2 ≤ a) (hb : 1 ≤ b)
    (hδ : 0 ≤ δ) (hδb : δ ≤ b)
    (hnb : (fixedCutoffReferenceBandThreshold : ℝ) ≤ b) (hba : b ≤ a)
    (hS : ∀ j ∈ S, |(j : ℝ)| ≤ (fixedCutoffReferenceRadius : ℝ) * b) :
    log (1 + ∑ j ∈ S, ∫ e, max (-fixedCutoffReferenceDensity a b δ ha hb j e) 0
      ∂referenceMeasure j) ≤
      log (1 + 5 * ((fixedCutoffReferenceRadius : ℝ) + 1) * fixedCutoffReferenceNegativeCoefficient) +
        10 * log (1 + a) + fixedCutoffReferenceNegativeExponent * sqrt (a * b) := by
  let N := ∑ j ∈ S, ∫ e, max (-fixedCutoffReferenceDensity a b δ ha hb j e) 0
    ∂referenceMeasure j
  let C := 5 * ((fixedCutoffReferenceRadius : ℝ) + 1) * fixedCutoffReferenceNegativeCoefficient
  let X := (1 + a) ^ 10 * exp (fixedCutoffReferenceNegativeExponent * sqrt (a * b))
  have hN : 0 ≤ N := Finset.sum_nonneg fun _ _ => integral_nonneg fun _ => le_max_right _ _
  have hC : 0 < C := by
    dsimp [C]
    have := fixedCutoffReferenceNegativeCoefficient_pos
    positivity
  have hX : 1 ≤ X := by
    apply one_le_mul_of_one_le_of_one_le
    · exact one_le_pow₀ (by linarith)
    · exact one_le_exp (mul_nonneg fixedCutoffReferenceNegativeExponent_pos.le (sqrt_nonneg _))
  have hbound : N ≤ C * X := by
    simpa only [N, C, X, mul_assoc] using
      sum_negativeMass_fixedCutoffReferenceDensity_le S a b δ ha hb hδ hδb hnb hba hS
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
