import GapFamily.Analytic.Poincare.Seed.PoincareGeneralThreshold
import GapFamily.Analytic.Poincare.Threshold.PoincareThresholdSmooth

/-! Actual spatial smoothness of the canonical threshold seed at every energy. -/
noncomputable section
namespace GapFamily.Analytic.PoincareEnergyContinuation
open Set UpperHalfPlane PoincareCanonical
open scoped ContDiff

/-- The canonical full threshold seed is real C∞ near every upper point, for
every complex input energy and every integer spin. -/
theorem contDiffAt_generalThresholdSeed (E : ℂ) (J : ℤ) (τ : UpperHalfPlane) :
    ContDiffAt ℝ ∞ (fun z : ℂ => generalThresholdSeed E J (ofComplex z)) (τ : ℂ) := by
  exact (PoincareThresholdSmooth.contDiffAt_thresholdSeed J τ).add
    (PoincareEnergySeriesSmooth.contDiffAt_complexPoincareEnergyDifference
      E J (s := (1 / 2 : ℂ)) (by norm_num) τ)

/-- Smoothness holds on the entire open upper half-plane, including all modular seams. -/
theorem contDiffOn_generalThresholdSeed (E : ℂ) (J : ℤ) :
    ContDiffOn ℝ ∞ (fun z : ℂ => generalThresholdSeed E J (ofComplex z)) upperHalfPlaneSet := by
  apply isOpen_upperHalfPlaneSet.contDiffOn_iff.mpr
  intro z hz
  exact contDiffAt_generalThresholdSeed E J ⟨z, hz⟩

end GapFamily.Analytic.PoincareEnergyContinuation
