import GapFamily.Construction.FixedCutoffMarkerTransferBound
import GapFamily.Construction.MarkerReferenceExteriorBound

/-!
# Exterior control uniform in the prescribed gap

The marker transfer has uniformly bounded input variation before repair.
Its complete repair costs one exponential in the clearing cutoff, so the
same universal enlargement argument applies also to a growing cutoff.
-/

noncomputable section

open MeasureTheory Set Real
open GapFamily.Analytic

namespace GapFamily.Construction

/-- The kernel part of the transferred reference. Direct anchor inputs are
supported through `6B`; beyond that point this is the complete numerator. -/
def fixedCutoffReferenceKernelNumerator (a B δ : ℝ) (ha : 2 ≤ a) (hB : 1 ≤ B)
    (hδ : 0 ≤ δ) (hδB : δ ≤ B) (j : ℤ) (e : ℝ) : ℝ :=
  canonicalMarkerReferenceKernelNumerator a B ha hB j e +
    (correctedSignedResponse (fun J : lowBandSpinSet (2 * B) =>
      fixedCutoffMarkerRepairInput B δ hB hδ hδB J) Subtype.val j e).re

def fixedCutoffReferenceExteriorCoefficient : ℝ :=
  markerReferenceExteriorCoefficient + 12 * correctedKernelBound

theorem fixedCutoffReferenceExteriorCoefficient_pos :
    0 < fixedCutoffReferenceExteriorCoefficient := by
  unfold fixedCutoffReferenceExteriorCoefficient
  have := markerReferenceExteriorCoefficient_pos
  have := correctedKernelBound_pos
  positivity

def fixedCutoffReferenceInputExponent : ℝ :=
  markerReferenceInputExponent + fixedCutoffMarkerRepairExponent

theorem fixedCutoffReferenceInputExponent_pos : 0 < fixedCutoffReferenceInputExponent :=
  add_pos markerReferenceInputExponent_pos fixedCutoffMarkerRepairExponent_pos

/-- A single square-root exponential bound controls both actual correction
responses uniformly in all prescribed marker locations. -/
theorem fixedCutoffReferenceKernelNumerator_correction_bound
    (a B δ e : ℝ) (ha : 2 ≤ a) (hB : 1 ≤ B) (hδ : 0 ≤ δ) (hδB : δ ≤ B)
    (j : ℤ) (he : |(j : ℝ)| ≤ e) (hBe : 2 * B ≤ e) :
    |fixedCutoffReferenceKernelNumerator a B δ ha hB hδ hδB j e -
      Analytic.vacuumNumerator a e j| ≤
      fixedCutoffReferenceExteriorCoefficient * (1 + a + B + e) ^ 9 *
        exp (4 * π * sqrt (a * B) + fixedCutoffReferenceInputExponent * B) := by
  have hB0 : 0 ≤ B := by linarith
  have he0 : 0 ≤ e := (abs_nonneg _).trans he
  have hS : 1 ≤ 1 + a + B + e := by linarith
  have hpoly : B * e ≤ (1 + a + B + e) ^ 9 := by
    calc
      _ ≤ (1 + a + B + e) * (1 + a + B + e) := by gcongr <;> linarith
      _ = (1 + a + B + e) ^ 2 := by ring
      _ ≤ _ := pow_le_pow_right₀ hS (by norm_num)
  have hexp1 : exp (4 * π * sqrt (a * B) + markerReferenceInputExponent * B) ≤
      exp (4 * π * sqrt (a * B) + fixedCutoffReferenceInputExponent * B) := by
    apply exp_le_exp.mpr
    unfold fixedCutoffReferenceInputExponent
    nlinarith only [mul_nonneg fixedCutoffMarkerRepairExponent_pos.le hB0]
  have hexp2 : exp (fixedCutoffMarkerRepairExponent * B) ≤
      exp (4 * π * sqrt (a * B) + fixedCutoffReferenceInputExponent * B) := by
    apply exp_le_exp.mpr
    unfold fixedCutoffReferenceInputExponent
    nlinarith only [mul_nonneg markerReferenceInputExponent_pos.le hB0,
      mul_nonneg Real.pi_pos.le (sqrt_nonneg (a * B))]
  have hfirst := norm_correctedSignedResponse_canonicalMarkerReference_le a B e ha hB j he
    (by linarith)
  have hsecond := norm_correctedSignedResponse_fixedCutoffMarkerRepair_le B δ hB hδ hδB e j he hBe
  have hfirst' := hfirst.trans (mul_le_mul_of_nonneg_left hexp1
    (mul_nonneg markerReferenceExteriorCoefficient_pos.le (by positivity)))
  have hsecond' : ‖correctedSignedResponse (fun J : lowBandSpinSet (2 * B) =>
      fixedCutoffMarkerRepairInput B δ hB hδ hδB J) Subtype.val j e‖ ≤
      12 * correctedKernelBound * (1 + a + B + e) ^ 9 *
        exp (4 * π * sqrt (a * B) + fixedCutoffReferenceInputExponent * B) := by
    apply hsecond.trans
    rw [mul_assoc (12 * correctedKernelBound) B e]
    exact mul_le_mul (mul_le_mul_of_nonneg_left hpoly (by have := correctedKernelBound_pos; positivity))
      hexp2 (exp_nonneg _) (by have := correctedKernelBound_pos; positivity)
  unfold fixedCutoffReferenceKernelNumerator canonicalMarkerReferenceKernelNumerator
  have habs := abs_add_le
    (correctedSignedResponse
      (fun J : lowBandSpinSet B => canonicalMarkerReferenceInput a B ha hB J)
      Subtype.val j e).re
    (correctedSignedResponse (fun J : lowBandSpinSet (2 * B) =>
      fixedCutoffMarkerRepairInput B δ hB hδ hδB J) Subtype.val j e).re
  have hreal1 := Complex.abs_re_le_norm (correctedSignedResponse
    (fun J : lowBandSpinSet B => canonicalMarkerReferenceInput a B ha hB J) Subtype.val j e)
  have hreal2 := Complex.abs_re_le_norm (correctedSignedResponse
    (fun J : lowBandSpinSet (2 * B) => fixedCutoffMarkerRepairInput B δ hB hδ hδB J)
    Subtype.val j e)
  have halgebra : Analytic.vacuumNumerator a e j +
      (correctedSignedResponse
        (fun J : lowBandSpinSet B => canonicalMarkerReferenceInput a B ha hB J)
        Subtype.val j e).re +
      (correctedSignedResponse (fun J : lowBandSpinSet (2 * B) =>
        fixedCutoffMarkerRepairInput B δ hB hδ hδB J) Subtype.val j e).re -
      Analytic.vacuumNumerator a e j =
      (correctedSignedResponse
        (fun J : lowBandSpinSet B => canonicalMarkerReferenceInput a B ha hB J)
        Subtype.val j e).re +
      (correctedSignedResponse (fun J : lowBandSpinSet (2 * B) =>
        fixedCutoffMarkerRepairInput B δ hB hδ hδB J) Subtype.val j e).re := by ring
  rw [halgebra]
  apply habs.trans
  apply (add_le_add hreal1 hreal2).trans
  simpa only [fixedCutoffReferenceExteriorCoefficient, add_mul] using
    add_le_add hfirst' hsecond'

/-- Auxiliary constants are fixed before the marker location, cutoff, and
central charge. The radius also lies past every direct anchor input. -/
theorem exists_fixedCutoffReferenceKernelNumerator_uniform_error :
    ∃ R₀ : ℕ, 6 < R₀ ∧ ∃ n₀ : ℕ, 100 ≤ n₀ ∧ ∀ (a B δ : ℝ)
      (ha : 2 ≤ a) (hB : 1 ≤ B) (hδ : 0 ≤ δ) (hδB : δ ≤ B) (e : ℝ) (j : ℤ),
      (n₀ : ℝ) ≤ B → B ≤ a → (R₀ : ℝ) * B ≤ e → |(j : ℝ)| ≤ e →
      |fixedCutoffReferenceKernelNumerator a B δ ha hB hδ hδB j e - vacuumLeading a e j| ≤
        exp (7 * sqrt (a * e)) / 2 := by
  obtain ⟨R, hR, n, hn, herr⟩ := exists_referenceError_absorption 9
    fixedCutoffReferenceExteriorCoefficient_pos.le (by positivity : 0 ≤ 4 * π)
    fixedCutoffReferenceInputExponent_pos.le
  obtain ⟨A, hA, hvac⟩ := exists_vacuumNumerator_uniform_error_bound
  obtain ⟨n₀, hn₀⟩ := exists_nat_ge (max A (n : ℝ))
  have hnA : A ≤ (n₀ : ℝ) := (le_max_left _ _).trans hn₀
  have hnn : (n : ℝ) ≤ n₀ := (le_max_right _ _).trans hn₀
  refine ⟨R + 7, by omega, n₀, ?_, ?_⟩
  · exact_mod_cast hA.trans hnA
  intro a B δ ha hB hδ hδB e j hnB hBa hRe hje
  have hB0 : 0 ≤ B := by linarith
  have hRe' : (R : ℝ) * B ≤ e := by
    have : (R : ℝ) ≤ (R + 7 : ℕ) := by exact_mod_cast (by omega : R ≤ R + 7)
    exact (mul_le_mul_of_nonneg_right this hB0).trans hRe
  have hBe : 2 * B ≤ e := by
    have : (2 : ℝ) ≤ R := by exact_mod_cast (by omega : 2 ≤ R)
    exact (mul_le_mul_of_nonneg_right this hB0).trans hRe'
  have hcor := (fixedCutoffReferenceKernelNumerator_correction_bound
    a B δ e ha hB hδ hδB j hje hBe).trans
      (herr a B e (hnn.trans hnB) hBa hRe')
  have hv := hvac a e j (hnA.trans (hnB.trans hBa)) (by linarith) hje
  have htriangle := abs_add_le
    (fixedCutoffReferenceKernelNumerator a B δ ha hB hδ hδB j e -
      Analytic.vacuumNumerator a e j)
    (Analytic.vacuumNumerator a e j - vacuumLeading a e j)
  rw [sub_add_sub_cancel] at htriangle
  linarith

/-- The universal reference radius is selected independently of both gap and charge. -/
def fixedCutoffReferenceRadius : ℕ :=
  Classical.choose exists_fixedCutoffReferenceKernelNumerator_uniform_error

theorem fixedCutoffReferenceRadius_gt_six : 6 < fixedCutoffReferenceRadius :=
  (Classical.choose_spec exists_fixedCutoffReferenceKernelNumerator_uniform_error).1

/-- The chosen common clearing-band threshold for this reference construction. -/
def fixedCutoffReferenceBandThreshold : ℕ :=
  Classical.choose
    (Classical.choose_spec exists_fixedCutoffReferenceKernelNumerator_uniform_error).2

theorem fixedCutoffReferenceBandThreshold_ge_hundred :
    100 ≤ fixedCutoffReferenceBandThreshold :=
  (Classical.choose_spec
    (Classical.choose_spec exists_fixedCutoffReferenceKernelNumerator_uniform_error).2).1

theorem fixedCutoffReferenceKernelNumerator_uniform_error
    (a B δ : ℝ) (ha : 2 ≤ a) (hB : 1 ≤ B) (hδ : 0 ≤ δ) (hδB : δ ≤ B)
    (e : ℝ) (j : ℤ) (hnB : (fixedCutoffReferenceBandThreshold : ℝ) ≤ B)
    (hBa : B ≤ a) (hRe : (fixedCutoffReferenceRadius : ℝ) * B ≤ e)
    (hje : |(j : ℝ)| ≤ e) :
    |fixedCutoffReferenceKernelNumerator a B δ ha hB hδ hδB j e - vacuumLeading a e j| ≤
      exp (7 * sqrt (a * e)) / 2 :=
  (Classical.choose_spec
    (Classical.choose_spec exists_fixedCutoffReferenceKernelNumerator_uniform_error).2).2
      a B δ ha hB hδ hδB e j hnB hBa hRe hje

end GapFamily.Construction
