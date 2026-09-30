import GapFamily.Analytic.Cusp.CuspPoincareDirectRemnant
import GapFamily.Analytic.Cusp.Fourier.CuspFourierCutoffWeighted

noncomputable section
namespace GapFamily.Analytic
open MeasureTheory CuspFourierCutoff

/-- The actual weighted direct remainder has a norm independent of the Fourier spin. -/
theorem norm_cuspPoincareDirectRemnant_eq_zero_spin (J : ℤ) (α : ℝ) {w : ℂ}
    (hw : 0 < w.re + α) :
    ‖cuspPoincareDirectRemnant J α w‖ = ‖cuspPoincareDirectRemnant 0 α w‖ := by
  rw [Lp.norm_def, Lp.norm_def]
  congr 1
  apply eLpNorm_congr_norm_ae (Lp.aestronglyMeasurable _) (Lp.aestronglyMeasurable _)
  filter_upwards [cuspPoincareDirectRemnant_ae J α hw,
    cuspPoincareDirectRemnant_ae 0 α hw] with τ hJ h0
  rw [hJ, h0]
  simp only [cuspPoincareDirectRemnantTerm, complexPointSeed_zero_eq_cuspFourierMode,
    norm_mul, norm_cuspFourierMode]

/-- The genuine compact weighted forcing has a norm independent of the Fourier spin. -/
theorem norm_weightedForcing_eq_zero_spin (J : ℤ) (α : ℝ) (κ : ℂ) :
    ‖weightedForcing J α κ‖ = ‖weightedForcing 0 α κ‖ := by
  rw [Lp.norm_def, Lp.norm_def]
  congr 1
  apply eLpNorm_congr_norm_ae (Lp.aestronglyMeasurable _) (Lp.aestronglyMeasurable _)
  filter_upwards [weightedForcing_ae J α κ, weightedForcing_ae 0 α κ] with τ hJ h0
  rw [hJ, h0]
  simp only [norm_mul, norm_cuspFourierMode]

end GapFamily.Analytic
