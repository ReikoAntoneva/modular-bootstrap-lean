import GapFamily.Analytic.Modular.Elliptic.ModularInteriorCompactUpperEnergy
import GapFamily.Analytic.Modular.Elliptic.ModularInteriorCompactCore
import GapFamily.Analytic.Elliptic.LocalSobolevCompactRellich

/-! # Rellich compactness for actual cutoff families crossing modular seams -/

noncomputable section

namespace GapFamily.Analytic.ModularGradient

open Set MeasureTheory UpperHalfPlane
open scoped ContDiff

theorem totallyBounded_upperCutoff_core {χ : ℂ → ℂ} (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ upperHalfPlaneSet)
    (T : Set ℂ) [CompactSpace T] {R : ℝ} (hR : 0 ≤ R) :
    TotallyBounded (range (fun F : {F : smoothCore // ‖coreForm F‖ ≤ R} =>
      LocalSobolev.restrictedLp T (fun z => χ z * F.val.val z)
        (upperCutoff_contDiff hχ hs F.val).continuous)) := by
  obtain ⟨B, hB, hb⟩ := exists_upperCutoff_energy_bound hχ hc hs
  let : CompactSpace (tsupport χ) := isCompact_iff_compactSpace.mp hc
  let g : {F : smoothCore // ‖coreForm F‖ ≤ R} → ℂ → ℂ :=
    fun F z => χ z * F.val.val z
  have hg (F : {F : smoothCore // ‖coreForm F‖ ≤ R}) : ContDiff ℝ 1 (g F) :=
    (upperCutoff_contDiff hχ hs F.val).of_le (by simp)
  have hsupport (F : {F : smoothCore // ‖coreForm F‖ ≤ R}) :
      tsupport (g F) ⊆ tsupport χ := cutoff_tsupport_subset χ F.val
  have hv (F : {F : smoothCore // ‖coreForm F‖ ≤ R}) :
      (∫ z : ℂ, ‖g F z‖ ^ 2) ≤ (B * R) ^ 2 := by
    have h := (hb F.val).1
    rw [← coreForm_norm_sq] at h
    calc
      _ ≤ B ^ 2 * ‖coreForm F.val‖ ^ 2 := h
      _ ≤ B ^ 2 * R ^ 2 := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg _) F.property 2) (sq_nonneg _)
      _ = _ := by ring
  have he (F : {F : smoothCore // ‖coreForm F‖ ≤ R}) :
      (∫ z : ℂ, ‖fderiv ℝ (g F) z‖ ^ 2) ≤ (B * R) ^ 2 := by
    have h := (hb F.val).2
    rw [← coreForm_norm_sq] at h
    calc
      _ ≤ B ^ 2 * ‖coreForm F.val‖ ^ 2 := h
      _ ≤ B ^ 2 * R ^ 2 := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg _) F.property 2) (sq_nonneg _)
      _ = _ := by ring
  exact LocalSobolev.totallyBounded_restrictedLp_of_uniform_energy
    (tsupport χ) T g hg hsupport (mul_nonneg hB.le hR) (mul_nonneg hB.le hR) hv he

end GapFamily.Analytic.ModularGradient
