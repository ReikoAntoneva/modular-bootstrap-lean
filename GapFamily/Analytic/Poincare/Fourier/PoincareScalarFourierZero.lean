import GapFamily.Analytic.Poincare.PoincareScalarIdentification
import GapFamily.Analytic.Poincare.Fourier.PoincareGeneralFourier

noncomputable section

namespace GapFamily.Analytic.PoincareEnergyFourier

open PoincareCanonical PoincareFourierContinuation
open PoincareEnergyContinuation

/-- The actual zero-energy scalar threshold coefficient vanishes. -/
theorem thresholdFourierCoefficient_zero_zero (y : ℝ) (hy : 0 < y) :
    thresholdFourierCoefficient y hy 0 0 = 0 := by
  simp [thresholdFourierCoefficient, thresholdSeed_zero]

/-- The general-energy definition has the same zero-energy scalar normalization. -/
theorem generalThresholdFourierCoefficient_zero_zero_zero (y : ℝ) (hy : 0 < y) :
    generalThresholdFourierCoefficient y hy 0 0 0 = 0 := by
  simp [generalThresholdFourierCoefficient, generalThresholdSeed_zero_energy,
    thresholdSeed_zero]

end GapFamily.Analytic.PoincareEnergyFourier
