import GapFamily.Construction.MarkerReferenceKernelNumerator
import GapFamily.Construction.MarkerReferenceInputBound

/-!
# Ordinary compact mass of the actual marker reference

For each fixed band ratio, the actual input variation and the ordinary
absolute kernel mass on that band admit a uniform polynomial times
`exp (C * sqrt (a * b))` bound. The scalar endpoint uses the genuine
ordinary integral against `referenceMeasure`.
-/

noncomputable section

open MeasureTheory Set Real
open scoped BigOperators
open GapFamily.Analytic

namespace GapFamily.Construction

/-- A positive square-root growth rate for each fixed compact-band ratio. -/
def markerReferenceCompactMassExponent (R : ℝ) : ℝ :=
  4 * π * (1 + sqrt R) + markerReferenceInputExponent

theorem markerReferenceCompactMassExponent_pos (R : ℝ) :
    0 < markerReferenceCompactMassExponent R := by
  unfold markerReferenceCompactMassExponent
  have := markerReferenceInputExponent_pos
  positivity

/-- A coefficient depending only on the compact-band ratio. -/
def markerReferenceCompactMassCoefficient (R : ℝ) : ℝ :=
  1 + markerReferenceInputCoefficient + markerReferenceCoefficient * R +
    12 * R * correctedKernelBound * markerReferenceInputCoefficient

theorem markerReferenceCompactMassCoefficient_pos (R : ℝ) (hR : 0 ≤ R) :
    0 < markerReferenceCompactMassCoefficient R := by
  unfold markerReferenceCompactMassCoefficient
  have := markerReferenceInputCoefficient_pos
  have := markerReferenceCoefficient_pos
  have := correctedKernelBound_pos
  positivity

private theorem compact_kernel_factor_le (R b : ℝ) (hR : 1 ≤ R) (hb : 1 ≤ b) :
    3 * b * (R * b) + sqrt (3 * b) * (R * b + 2 * sqrt (R * b)) ≤
      12 * R * b ^ 2 := by
  have hb0 : 0 ≤ b := zero_le_one.trans hb
  have hR0 : 0 ≤ R := zero_le_one.trans hR
  have hRb : 1 ≤ R * b := one_le_mul_of_one_le_of_one_le hR hb
  have hs3 : sqrt (3 * b) ≤ 3 * b := sqrt_le_self_iff.mpr (Or.inr (by linarith))
  have hsR : sqrt (R * b) ≤ R * b := sqrt_le_self_iff.mpr (Or.inr hRb)
  calc
    _ ≤ 3 * b * (R * b) + (3 * b) * (R * b + 2 * (R * b)) := by gcongr
    _ = _ := by ring

private theorem band_le_sqrt_product (a b : ℝ) (hb : 0 ≤ b) (hba : b ≤ a) :
    b ≤ sqrt (a * b) := by
  apply (le_sqrt hb (mul_nonneg (hb.trans hba) hb)).2
  nlinarith [mul_le_mul_of_nonneg_right hba hb]

/-- Uniform ordinary compact mass of every actual output row, including
both the original signed input mass and the full kernel numerator. -/
theorem canonicalMarkerReference_compactMass_le (R a b : ℝ)
    (hR : 1 ≤ R) (ha : 2 ≤ a) (hb : 1 ≤ b) (hba : b ≤ a) (j : ℤ) :
    1 + signedSeedMass
        (fun J : lowBandSpinSet b => canonicalMarkerReferenceInput a b ha hb J) +
      (∫ e, |canonicalMarkerReferenceKernelNumerator a b ha hb j e|
        ∂(referenceMeasure j).restrict (Ioo |(j : ℝ)| (R * b))) ≤
      markerReferenceCompactMassCoefficient R * (1 + a) ^ 9 *
        exp (markerReferenceCompactMassExponent R * sqrt (a * b)) := by
  have ha0 : 0 ≤ a := by linarith
  have hb0 : 0 ≤ b := zero_le_one.trans hb
  have hR0 : 0 ≤ R := zero_le_one.trans hR
  have ha1 : 1 ≤ 1 + a := by linarith
  have hbA : b ≤ 1 + a := by linarith
  have ht : b ≤ sqrt (a * b) := band_le_sqrt_product a b hb0 hba
  let E := exp (markerReferenceCompactMassExponent R * sqrt (a * b))
  let H := (1 + a) ^ 9 * E
  let M := signedSeedMass
    (fun J : lowBandSpinSet b => canonicalMarkerReferenceInput a b ha hb J)
  have hC := markerReferenceInputCoefficient_pos.le
  have hK := correctedKernelBound_pos.le
  have hV := markerReferenceCoefficient_pos.le
  have hD := markerReferenceInputExponent_pos.le
  have hE : 1 ≤ E := one_le_exp (by
    have := (markerReferenceCompactMassExponent_pos R).le
    positivity)
  have hH : 1 ≤ H := one_le_mul_of_one_le_of_one_le (one_le_pow₀ ha1) hE
  have hInputExp : exp (4 * π * sqrt (a * b) + markerReferenceInputExponent * b) ≤ E := by
    apply exp_le_exp.mpr
    calc
      _ ≤ 4 * π * sqrt (a * b) + markerReferenceInputExponent * sqrt (a * b) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left ht hD)
      _ ≤ markerReferenceCompactMassExponent R * sqrt (a * b) := by
        unfold markerReferenceCompactMassExponent
        nlinarith [mul_nonneg (show 0 ≤ 4 * π * sqrt R by positivity) (sqrt_nonneg (a * b))]
  have hVacuumExp : exp (4 * π * sqrt (a * (R * b))) ≤ E := by
    apply exp_le_exp.mpr
    rw [show a * (R * b) = R * (a * b) by ring, sqrt_mul hR0]
    unfold markerReferenceCompactMassExponent
    nlinarith [mul_nonneg (show 0 ≤ 4 * π + markerReferenceInputExponent by positivity)
      (sqrt_nonneg (a * b))]
  have hM : M ≤ markerReferenceInputCoefficient * (1 + a) ^ 7 * E := by
    calc
      _ ≤ markerReferenceInputCoefficient * (1 + a) * b ^ 6 *
          exp (4 * π * sqrt (a * b) + markerReferenceInputExponent * b) :=
        signedSeedMass_canonicalMarkerReferenceInput_le a b ha hb
      _ ≤ markerReferenceInputCoefficient * (1 + a) * (1 + a) ^ 6 * E := by gcongr
      _ = _ := by ring
  have hM9 : M ≤ markerReferenceInputCoefficient * H := by
    apply hM.trans
    dsimp [H]
    rw [← mul_assoc]
    gcongr
    norm_num
  have hVac : markerReferenceEnergyBound a (R * b) * (R * b) ≤
      (markerReferenceCoefficient * R) * H := by
    calc
      _ ≤ markerReferenceEnvelope a (R * b) * (R * b) :=
        mul_le_mul_of_nonneg_right (markerReferenceEnergyBound_le_envelope a (R * b) ha0)
          (mul_nonneg hR0 hb0)
      _ ≤ (markerReferenceCoefficient * (1 + a) * E) * (R * (1 + a)) := by
        unfold markerReferenceEnvelope
        gcongr
      _ = (markerReferenceCoefficient * R) * (1 + a) ^ 2 * E := by ring
      _ ≤ (markerReferenceCoefficient * R) * H := by
        dsimp [H]
        rw [← mul_assoc]
        gcongr
        norm_num
  have hResponse : M * correctedKernelBound *
      (3 * b * (R * b) + sqrt (3 * b) * (R * b + 2 * sqrt (R * b))) ≤
      (12 * R * correctedKernelBound * markerReferenceInputCoefficient) * H := by
    have hM0 : 0 ≤ M := signedSeedMass_nonneg _
    calc
      _ ≤ (markerReferenceInputCoefficient * (1 + a) ^ 7 * E) * correctedKernelBound *
          (12 * R * (1 + a) ^ 2) := by
        apply mul_le_mul
          (mul_le_mul_of_nonneg_right hM hK)
          ((compact_kernel_factor_le R b hR hb).trans (by gcongr))
          (by positivity) (by positivity)
      _ = _ := by dsimp [H]; ring
  have hIntegral : (∫ e, |canonicalMarkerReferenceKernelNumerator a b ha hb j e|
      ∂(referenceMeasure j).restrict (Ioo |(j : ℝ)| (R * b))) ≤
      (markerReferenceCoefficient * R) * H +
        (12 * R * correctedKernelBound * markerReferenceInputCoefficient) * H :=
    (integral_abs_canonicalMarkerReferenceKernelNumerator_le a b (R * b) ha hb
      (mul_nonneg hR0 hb0) j).trans (add_le_add hVac hResponse)
  calc
    _ ≤ H + markerReferenceInputCoefficient * H +
        ((markerReferenceCoefficient * R) * H +
          (12 * R * correctedKernelBound * markerReferenceInputCoefficient) * H) :=
      add_le_add (add_le_add hH hM9) hIntegral
    _ = _ := by dsimp [H, E, markerReferenceCompactMassCoefficient]; ring

/-- The finite physical spin count adds one polynomial degree. -/
def markerReferenceTotalCompactMassCoefficient (R : ℝ) : ℝ :=
  (1 + 5 * R) * markerReferenceCompactMassCoefficient R

theorem markerReferenceTotalCompactMassCoefficient_pos (R : ℝ) (hR : 0 ≤ R) :
    0 < markerReferenceTotalCompactMassCoefficient R := by
  unfold markerReferenceTotalCompactMassCoefficient
  exact mul_pos (by positivity) (markerReferenceCompactMassCoefficient_pos R hR)

/-- The actual input and all compact physical kernel rows together have an
ordinary mass bound uniform in the vacuum and marker parameters. -/
theorem canonicalMarkerReference_totalCompactMass_le (R a b : ℝ)
    (hR : 1 ≤ R) (ha : 2 ≤ a) (hb : 1 ≤ b) (hba : b ≤ a) :
    1 + signedSeedMass
        (fun J : lowBandSpinSet b => canonicalMarkerReferenceInput a b ha hb J) +
      (∑ j ∈ lowBandSpinSet (R * b),
        ∫ e, |canonicalMarkerReferenceKernelNumerator a b ha hb j e|
          ∂(referenceMeasure j).restrict (Ioo |(j : ℝ)| (R * b))) ≤
      markerReferenceTotalCompactMassCoefficient R * (1 + a) ^ 10 *
        exp (markerReferenceCompactMassExponent R * sqrt (a * b)) := by
  have hR0 : 0 ≤ R := zero_le_one.trans hR
  have hb0 : 0 ≤ b := zero_le_one.trans hb
  have ha1 : 1 ≤ 1 + a := by linarith
  have hbA : b ≤ 1 + a := by linarith
  let M := signedSeedMass
    (fun J : lowBandSpinSet b => canonicalMarkerReferenceInput a b ha hb J)
  let I (j : ℤ) := ∫ e, |canonicalMarkerReferenceKernelNumerator a b ha hb j e|
    ∂(referenceMeasure j).restrict (Ioo |(j : ℝ)| (R * b))
  let H := (1 + a) ^ 9 * exp (markerReferenceCompactMassExponent R * sqrt (a * b))
  have hM : 0 ≤ M := signedSeedMass_nonneg _
  have hI (j : ℤ) : 0 ≤ I j := integral_nonneg fun _ => abs_nonneg _
  have hC := (markerReferenceCompactMassCoefficient_pos R hR0).le
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hrow (j : ℤ) : 1 + M + I j ≤ markerReferenceCompactMassCoefficient R * H := by
    simpa only [H, mul_assoc] using canonicalMarkerReference_compactMass_le R a b hR ha hb hba j
  have hbase : 1 + M ≤ (1 + a) * (markerReferenceCompactMassCoefficient R * H) :=
    ((le_add_of_nonneg_right (hI 0)).trans (hrow 0)).trans
      (le_mul_of_one_le_left (mul_nonneg hC hH) ha1)
  have hsum : (∑ j ∈ lowBandSpinSet (R * b), I j) ≤
      5 * R * (1 + a) * (markerReferenceCompactMassCoefficient R * H) := by
    calc
      _ ≤ ∑ _j ∈ lowBandSpinSet (R * b), markerReferenceCompactMassCoefficient R * H := by
        apply Finset.sum_le_sum
        intro j _
        have := hrow j
        linarith
      _ = ((lowBandSpinSet (R * b)).card : ℝ) *
          (markerReferenceCompactMassCoefficient R * H) := by simp
      _ ≤ (5 * (R * b)) * (markerReferenceCompactMassCoefficient R * H) :=
        mul_le_mul_of_nonneg_right (lowBandSpinSet_card_le (R * b)
          (one_le_mul_of_one_le_of_one_le hR hb)) (mul_nonneg hC hH)
      _ ≤ (5 * (R * (1 + a))) * (markerReferenceCompactMassCoefficient R * H) := by gcongr
      _ = _ := by ring
  calc
    _ ≤ (1 + a) * (markerReferenceCompactMassCoefficient R * H) +
        5 * R * (1 + a) * (markerReferenceCompactMassCoefficient R * H) := add_le_add hbase hsum
    _ = _ := by dsimp [H, markerReferenceTotalCompactMassCoefficient]; ring

end GapFamily.Construction
