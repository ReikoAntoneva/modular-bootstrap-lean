import GapFamily.Construction.MarkerReferenceKernelNumerator
import GapFamily.Construction.MarkerReferenceInputBound
import GapFamily.Construction.ReferenceErrorAbsorption
import GapFamily.Construction.ReferenceDensityBound

/-! The actual reference input obeys the exterior vacuum approximation after
one universal band enlargement, chosen before later cell parameters. -/

noncomputable section

open MeasureTheory Set Real
open GapFamily.Analytic

namespace GapFamily.Construction

/-- A fixed coefficient for the actual exterior reference correction. -/
def markerReferenceExteriorCoefficient : ℝ :=
  6 * correctedKernelBound * markerReferenceInputCoefficient

theorem markerReferenceExteriorCoefficient_pos : 0 < markerReferenceExteriorCoefficient := by
  unfold markerReferenceExteriorCoefficient
  have := correctedKernelBound_pos
  have := markerReferenceInputCoefficient_pos
  positivity

/-- The full signed correction has fixed polynomial degree and the actual
square-root input exponent. -/
theorem norm_correctedSignedResponse_canonicalMarkerReference_le
    (a b e : ℝ) (ha : 2 ≤ a) (hb : 1 ≤ b) (j : ℤ)
    (he : |(j : ℝ)| ≤ e) (hbe : b ≤ e) :
    ‖correctedSignedResponse
      (fun J : lowBandSpinSet b => canonicalMarkerReferenceInput a b ha hb J)
      Subtype.val j e‖ ≤
      markerReferenceExteriorCoefficient * (1 + a + b + e) ^ 9 *
        exp (4 * π * sqrt (a * b) + markerReferenceInputExponent * b) := by
  have ha0 : 0 ≤ a := by linarith
  have hb0 : 0 ≤ b := by linarith
  have he0 : 0 ≤ e := hb0.trans hbe
  have hp : (1 + a) * b ^ 7 * e ≤ (1 + a + b + e) ^ 9 := by
    have h1 : 1 + a ≤ 1 + a + b + e := by linarith
    have hbS : b ≤ 1 + a + b + e := by linarith
    have heS : e ≤ 1 + a + b + e := by linarith
    have hS : 0 ≤ 1 + a + b + e := by positivity
    calc
      _ ≤ (1 + a + b + e) * (1 + a + b + e) ^ 7 * (1 + a + b + e) :=
        mul_le_mul (mul_le_mul h1 (pow_le_pow_left₀ hb0 hbS 7)
          (by positivity) hS) heS he0 (by positivity)
      _ = _ := by ring
  calc
    _ ≤ signedSeedMass (fun J : lowBandSpinSet b => canonicalMarkerReferenceInput a b ha hb J) *
        (6 * correctedKernelBound * b * e) :=
      norm_correctedSignedResponse_le_exterior
        (fun J : lowBandSpinSet b => canonicalMarkerReferenceInput a b ha hb J) Subtype.val j b hb
        (fun J => canonicalMarkerReferenceInput_physicalSupport a b ha hb J) e he hbe
    _ ≤ (markerReferenceInputCoefficient * (1 + a) * b ^ 6 *
        exp (4 * π * sqrt (a * b) + markerReferenceInputExponent * b)) *
        (6 * correctedKernelBound * b * e) := by
      exact mul_le_mul_of_nonneg_right (signedSeedMass_canonicalMarkerReferenceInput_le a b ha hb)
        (by have := correctedKernelBound_pos; positivity)
    _ = markerReferenceExteriorCoefficient * ((1 + a) * b ^ 7 * e) *
        exp (4 * π * sqrt (a * b) + markerReferenceInputExponent * b) := by
      unfold markerReferenceExteriorCoefficient
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hp markerReferenceExteriorCoefficient_pos.le) (exp_nonneg _)

/-- One universal enlargement and one later band threshold suffice for the
literal canonical reference error, uniformly in every physical output row. -/
theorem exists_canonicalMarkerReferenceKernelNumerator_uniform_error :
    ∃ R₀ : ℕ, 3 < R₀ ∧ ∃ n₀ : ℕ, 100 ≤ n₀ ∧ ∀ (a b : ℝ)
      (ha : 2 ≤ a) (hb : 1 ≤ b) (e : ℝ) (j : ℤ),
      (n₀ : ℝ) ≤ b → b ≤ a → (R₀ : ℝ) * b ≤ e → |(j : ℝ)| ≤ e →
      |canonicalMarkerReferenceKernelNumerator a b ha hb j e - vacuumLeading a e j| ≤
        exp (7 * sqrt (a * e)) / 2 := by
  obtain ⟨R₀, hR₀, n₁, hn₁, herr⟩ := exists_referenceError_absorption 9
    markerReferenceExteriorCoefficient_pos.le (by positivity : 0 ≤ 4 * π)
    markerReferenceInputExponent_pos.le
  obtain ⟨A, hA, hvac⟩ := exists_vacuumNumerator_uniform_error_bound
  obtain ⟨n₀, hn₀⟩ := exists_nat_ge (max A (n₁ : ℝ))
  have hnA : A ≤ (n₀ : ℝ) := (le_max_left _ _).trans hn₀
  have hn₁₀ : (n₁ : ℝ) ≤ n₀ := (le_max_right _ _).trans hn₀
  have hn0 : 100 ≤ n₀ := by
    exact_mod_cast hA.trans hnA
  refine ⟨R₀, hR₀, n₀, hn0, ?_⟩
  intro a b ha hb e j hnb hba he hj
  have hb0 : 0 ≤ b := by linarith
  have hR1 : (1 : ℝ) ≤ R₀ := by exact_mod_cast (by omega : 1 ≤ R₀)
  have hbe : b ≤ e := (le_mul_of_one_le_left hb0 hR1).trans he
  have hcor := (norm_correctedSignedResponse_canonicalMarkerReference_le a b e ha hb j hj hbe).trans
    (herr a b e (hn₁₀.trans hnb) hba he)
  have hv := hvac a e j (hnA.trans (hnb.trans hba)) (hb.trans hbe) hj
  have hraw' : |canonicalMarkerReferenceKernelNumerator a b ha hb j e - vacuumLeading a e j| ≤
      |Analytic.vacuumNumerator a e j - vacuumLeading a e j| +
        ‖correctedSignedResponse
          (fun J : lowBandSpinSet b => canonicalMarkerReferenceInput a b ha hb J)
          Subtype.val j e‖ := by
    unfold canonicalMarkerReferenceKernelNumerator
    calc
      _ = |(Analytic.vacuumNumerator a e j - vacuumLeading a e j) +
          (correctedSignedResponse
            (fun J : lowBandSpinSet b => canonicalMarkerReferenceInput a b ha hb J)
            Subtype.val j e).re| := by congr 1; ring
      _ ≤ _ := (abs_add_le _ _).trans (add_le_add le_rfl (Complex.abs_re_le_norm _))
  linarith

/-- The fixed enlargement is selected from the actual reference bound before
any initial-cell or tail-cell parameters are chosen. -/
def markerReferenceRadius : ℕ :=
  Classical.choose exists_canonicalMarkerReferenceKernelNumerator_uniform_error

theorem markerReferenceRadius_gt_three : 3 < markerReferenceRadius :=
  (Classical.choose_spec exists_canonicalMarkerReferenceKernelNumerator_uniform_error).1

/-- The corresponding universal band threshold. -/
def markerReferenceBandThreshold : ℕ :=
  Classical.choose
    (Classical.choose_spec exists_canonicalMarkerReferenceKernelNumerator_uniform_error).2

theorem markerReferenceBandThreshold_ge_hundred : 100 ≤ markerReferenceBandThreshold :=
  (Classical.choose_spec
    (Classical.choose_spec exists_canonicalMarkerReferenceKernelNumerator_uniform_error).2).1

/-- The chosen constants apply to the literal canonical reference. -/
theorem canonicalMarkerReferenceKernelNumerator_uniform_error
    (a b : ℝ) (ha : 2 ≤ a) (hb : 1 ≤ b) (e : ℝ) (j : ℤ)
    (hnb : (markerReferenceBandThreshold : ℝ) ≤ b) (hba : b ≤ a)
    (he : (markerReferenceRadius : ℝ) * b ≤ e) (hj : |(j : ℝ)| ≤ e) :
    |canonicalMarkerReferenceKernelNumerator a b ha hb j e - vacuumLeading a e j| ≤
      exp (7 * sqrt (a * e)) / 2 :=
  (Classical.choose_spec
    (Classical.choose_spec exists_canonicalMarkerReferenceKernelNumerator_uniform_error).2).2
      a b ha hb e j hnb hba he hj

end GapFamily.Construction
