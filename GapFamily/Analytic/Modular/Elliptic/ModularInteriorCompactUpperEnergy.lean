import GapFamily.Analytic.Modular.Elliptic.ModularInteriorCompactUpperSmooth
import GapFamily.Analytic.Modular.Elliptic.ModularInteriorCompactCore
import GapFamily.Analytic.Modular.Geometry.ModularSeamCoordinate

/-!
# Actual cutoff energy across modular seams

The compact-coordinate estimate comes from the finite translated closed-tile
cover. A smooth cutoff can therefore cross seams while retaining an actual
uniform bound by the modular form norm.
-/

noncomputable section

namespace GapFamily.Analytic.ModularGradient

open Set MeasureTheory UpperHalfPlane
open scoped ContDiff

theorem exists_upperCutoff_coefficient_bound {χ : ℂ → ℂ}
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) :
    ∃ A : ℝ, 0 < A ∧ ∀ z ∈ tsupport χ, ‖χ z‖ ≤ A ∧ ‖fderiv ℝ χ z‖ ≤ A := by
  have hD : Continuous (fderiv ℝ χ) := hχ.continuous_fderiv (by simp)
  obtain ⟨C, hC⟩ := hc.bddAbove_image
    (hχ.continuous.norm.add hD.norm).continuousOn
  refine ⟨max 1 C, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro z hz
  have hb := (hC ⟨z, hz, rfl⟩).trans (le_max_right 1 C)
  simp only [Pi.add_apply] at hb
  exact ⟨by linarith [norm_nonneg (fderiv ℝ χ z)], by linarith [norm_nonneg (χ z)]⟩

theorem upperCutoff_value_le {χ : ℂ → ℂ} {A : ℝ}
    (hb : ∀ z ∈ tsupport χ, ‖χ z‖ ≤ A)
    (F : smoothCore) {z : ℂ} (hz : z ∈ tsupport χ) :
    ‖χ z * F.val z‖ ^ 2 ≤ A ^ 2 * (‖F.val z‖ ^ 2 +
      ‖fderiv ℝ F.val z 1‖ ^ 2 + ‖fderiv ℝ F.val z Complex.I‖ ^ 2) := by
  rw [norm_mul, mul_pow]
  calc
    _ ≤ A ^ 2 * ‖F.val z‖ ^ 2 := mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (norm_nonneg _) (hb z hz) 2) (sq_nonneg _)
    _ ≤ _ := mul_le_mul_of_nonneg_left (by
      nlinarith [sq_nonneg ‖fderiv ℝ F.val z 1‖,
        sq_nonneg ‖fderiv ℝ F.val z Complex.I‖]) (sq_nonneg _)

theorem upperCutoff_derivative_le {χ : ℂ → ℂ} (hχ : ContDiff ℝ ∞ χ)
    (hs : tsupport χ ⊆ upperHalfPlaneSet) {A : ℝ}
    (hb : ∀ z ∈ tsupport χ, ‖χ z‖ ≤ A ∧ ‖fderiv ℝ χ z‖ ≤ A)
    (F : smoothCore) {z : ℂ} (hz : z ∈ tsupport χ) :
    ‖fderiv ℝ (fun w => χ w * F.val w) z‖ ^ 2 ≤
      4 * A ^ 2 * (‖F.val z‖ ^ 2 +
        ‖fderiv ℝ F.val z 1‖ ^ 2 + ‖fderiv ℝ F.val z Complex.I‖ ^ 2) := by
  have hχsq := pow_le_pow_left₀ (norm_nonneg _) (hb z hz).1 2
  have hDsq := pow_le_pow_left₀ (norm_nonneg _) (hb z hz).2 2
  have hp := upperCutoff_norm_fderiv_sq_le hχ hs F z
  have h₁ := mul_le_mul_of_nonneg_right hDsq (sq_nonneg ‖F.val z‖)
  have h₂ := mul_le_mul_of_nonneg_right hχsq
    (add_nonneg (sq_nonneg ‖fderiv ℝ F.val z 1‖) (sq_nonneg ‖fderiv ℝ F.val z Complex.I‖))
  nlinarith [mul_nonneg (sq_nonneg A) (sq_nonneg ‖F.val z‖)]

/-- An actual cutoff supported anywhere in the upper half-plane has uniform
ordinary Euclidean value and derivative energy bounds by the modular form norm. -/
theorem exists_upperCutoff_energy_bound {χ : ℂ → ℂ} (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ upperHalfPlaneSet) :
    ∃ B : ℝ, 0 < B ∧ ∀ F : smoothCore,
      (∫ z : ℂ, ‖χ z * F.val z‖ ^ 2) ≤
        B ^ 2 * (‖value F‖ ^ 2 + ‖coreGradient F‖ ^ 2) ∧
      (∫ z : ℂ, ‖fderiv ℝ (fun w => χ w * F.val w) z‖ ^ 2) ≤
        B ^ 2 * (‖value F‖ ^ 2 + ‖coreGradient F‖ ^ 2) := by
  obtain ⟨A, hA, hb⟩ := exists_upperCutoff_coefficient_bound hχ hc
  obtain ⟨C, hC, hlocal⟩ := exists_compact_euclidean_graphEnergy_bound hc hs
  let B : ℝ := 2 * A * (C + 1)
  have hB : 0 < B := by dsimp [B]; positivity
  have hCrel : C ≤ (C + 1) ^ 2 := by nlinarith [sq_nonneg C]
  have hcoef : 4 * A ^ 2 * C ≤ B ^ 2 := by
    calc
      _ ≤ 4 * A ^ 2 * (C + 1) ^ 2 :=
        mul_le_mul_of_nonneg_left hCrel (by positivity)
      _ = _ := by dsimp [B]; ring
  have hcoef' : A ^ 2 * C ≤ B ^ 2 := by
    have hnon : 0 ≤ A ^ 2 * C := mul_nonneg (sq_nonneg _) hC.le
    linarith
  refine ⟨B, hB, fun F => ?_⟩
  have hE : 0 ≤ ‖value F‖ ^ 2 + ‖coreGradient F‖ ^ 2 := by positivity
  obtain ⟨hi, hbound⟩ := hlocal F
  constructor
  · calc
      _ = ∫ z in tsupport χ, ‖χ z * F.val z‖ ^ 2 := by
        symm
        apply setIntegral_eq_integral_of_forall_compl_eq_zero
        intro z hz
        simp [image_eq_zero_of_notMem_tsupport hz]
      _ ≤ ∫ z in tsupport χ, A ^ 2 * (‖F.val z‖ ^ 2 +
          ‖fderiv ℝ F.val z 1‖ ^ 2 + ‖fderiv ℝ F.val z Complex.I‖ ^ 2) := by
        apply integral_mono_of_nonneg
          (Filter.Eventually.of_forall fun _ => sq_nonneg _) (hi.const_mul _)
        filter_upwards [ae_restrict_mem (isClosed_tsupport χ).measurableSet] with z hz
        exact upperCutoff_value_le (fun z hz => (hb z hz).1) F hz
      _ = A ^ 2 * ∫ z in tsupport χ, (‖F.val z‖ ^ 2 +
          ‖fderiv ℝ F.val z 1‖ ^ 2 + ‖fderiv ℝ F.val z Complex.I‖ ^ 2) :=
        integral_const_mul _ _
      _ ≤ A ^ 2 * (C * (‖value F‖ ^ 2 + ‖coreGradient F‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left hbound (sq_nonneg _)
      _ ≤ _ := by
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_right hcoef' hE
  · calc
      _ = ∫ z in tsupport χ, ‖fderiv ℝ (fun w => χ w * F.val w) z‖ ^ 2 := by
        symm
        apply setIntegral_eq_integral_of_forall_compl_eq_zero
        intro z hz
        have hnot : z ∉ tsupport (fun w => χ w * F.val w) :=
          fun h => hz (cutoff_tsupport_subset χ F h)
        simp [fderiv_of_notMem_tsupport ℝ hnot]
      _ ≤ ∫ z in tsupport χ, 4 * A ^ 2 * (‖F.val z‖ ^ 2 +
          ‖fderiv ℝ F.val z 1‖ ^ 2 + ‖fderiv ℝ F.val z Complex.I‖ ^ 2) := by
        apply integral_mono_of_nonneg
          (Filter.Eventually.of_forall fun _ => sq_nonneg _) (hi.const_mul _)
        filter_upwards [ae_restrict_mem (isClosed_tsupport χ).measurableSet] with z hz
        exact upperCutoff_derivative_le hχ hs hb F hz
      _ = 4 * A ^ 2 * ∫ z in tsupport χ, (‖F.val z‖ ^ 2 +
          ‖fderiv ℝ F.val z 1‖ ^ 2 + ‖fderiv ℝ F.val z Complex.I‖ ^ 2) :=
        integral_const_mul _ _
      _ ≤ 4 * A ^ 2 * (C * (‖value F‖ ^ 2 + ‖coreGradient F‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left hbound (by positivity)
      _ ≤ _ := by
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_right hcoef hE

end GapFamily.Analytic.ModularGradient
