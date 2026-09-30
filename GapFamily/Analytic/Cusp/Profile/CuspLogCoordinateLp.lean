import GapFamily.Analytic.Cusp.Profile.CuspLogCoordinateBasic

/-!
# Actual square-integrability transport for measurable scalar profiles

This equivalence uses the existing inverse-square half-line measure and the
ordinary logarithmic half-line measure. It requires no compactness or decay
oracle, and includes measurability in the standard `MemLp` statements.
-/

noncomputable section

namespace GapFamily.Analytic

open Set MeasureTheory

theorem measurable_cuspLogCoordinate {b : ℝ → ℂ} (hb : Measurable b) :
    Measurable (cuspLogCoordinate b) := by
  unfold cuspLogCoordinate
  fun_prop

theorem integrable_cuspMeasure_norm_sq_iff_cuspLogCoordinate (b : ℝ → ℂ) :
    Integrable (fun y => ‖b y‖ ^ 2) (cuspMeasure 1) ↔
      IntegrableOn (fun t => ‖cuspLogCoordinate b t‖ ^ 2) (Ioi 0) := by
  rw [cuspMeasure, integrable_withDensity_iff_integrable_smul' (by fun_prop) (by simp)]
  have heq : (fun y : ℝ => (ENNReal.ofReal ((y ^ 2)⁻¹)).toReal • ‖b y‖ ^ 2) =
      (fun y : ℝ => ‖b y‖ ^ 2 / y ^ 2) := by
    funext y
    rw [ENNReal.toReal_ofReal (by positivity), smul_eq_mul]
    simp [div_eq_mul_inv, mul_comm]
  rw [heq]
  change IntegrableOn (fun y => ‖b y‖ ^ 2 / y ^ 2) (Ici 1) ↔ _
  rw [integrableOn_Ici_iff_integrableOn_Ioi]
  exact integrableOn_cuspLogCoordinate_mass_iff b

/-- Genuine weighted scalar `L²` membership is equivalent to ordinary logarithmic `L²`. -/
theorem memLp_two_cuspLogCoordinate_iff {b : ℝ → ℂ} (hb : Measurable b) :
    MemLp b 2 (cuspMeasure 1) ↔
      MemLp (cuspLogCoordinate b) 2 (volume.restrict (Ioi 0)) := by
  rw [memLp_two_iff_integrable_sq_norm hb.aestronglyMeasurable,
    memLp_two_iff_integrable_sq_norm (measurable_cuspLogCoordinate hb).aestronglyMeasurable]
  exact integrable_cuspMeasure_norm_sq_iff_cuspLogCoordinate b

end GapFamily.Analytic
