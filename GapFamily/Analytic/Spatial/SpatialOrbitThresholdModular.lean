import GapFamily.Analytic.Spatial.SpatialOrbitThresholdEvaluation
import GapFamily.Analytic.Foundation.UpperWeightedThresholdModular

/-! Modular invariance in both variables of the canonical threshold kernel. -/
noncomputable section
namespace GapFamily.Analytic.SpatialPoint
open MeasureTheory UpperHalfPlane
open scoped MatrixGroups

theorem spatialOrbitWeightedSource_modular_right
    (α : ℝ) (hα : 0 ≤ α) (hhalf : α < 1 / 2)
    (s : ℂ) (hs : 1 < s.re) (γ : SL(2, ℤ)) (w : UpperHalfPlane) :
    spatialOrbitWeightedSource α hα hhalf s (γ • w) =
      spatialOrbitWeightedSource α hα hhalf s w := by
  apply Lp.ext
  filter_upwards [spatialOrbitWeightedSource_ae α hα hhalf s hs (γ • w),
    spatialOrbitWeightedSource_ae α hα hhalf s hs w] with z hγ hz
  rw [hγ, hz, spatialOrbitKernel_modular_right]

theorem spatialOrbitThresholdInput_modular_right
    (s : ℂ) (hs : 0 < s.re) (γ : SL(2, ℤ)) (w : UpperHalfPlane) :
    spatialOrbitThresholdInput s (γ • w) = spatialOrbitThresholdInput s w := by
  unfold spatialOrbitThresholdInput
  rw [spatialOrbitWeightedSource_modular_right]
  simp only [Complex.add_re, Complex.one_re]
  linarith

theorem spatialThresholdKernel_modular_right
    (γ : SL(2, ℤ)) (z w : UpperHalfPlane) :
    spatialThresholdKernel z (γ • w) = spatialThresholdKernel z w := by
  unfold spatialThresholdKernel
  rw [spatialOrbitThresholdInput_modular_right (1 / 2) (by norm_num)]

theorem spatialThresholdCorrectedKernel_modular_right
    (γ : SL(2, ℤ)) (z w : UpperHalfPlane) :
    spatialThresholdCorrectedKernel z (γ • w) = spatialThresholdCorrectedKernel z w := by
  unfold spatialThresholdCorrectedKernel
  rw [spatialThresholdKernel_modular_right]

theorem spatialThresholdKernel_modular_left
    (γ : SL(2, ℤ)) (z w : UpperHalfPlane) :
    spatialThresholdKernel (γ • z) w = spatialThresholdKernel z w :=
  UpperWeightedCoherence.weightedThresholdValue_modular (1 / 4) (by norm_num)
    (spatialOrbitThresholdInput (1 / 2) w) γ z

theorem spatialThresholdCorrectedKernel_modular_left
    (γ : SL(2, ℤ)) (z w : UpperHalfPlane) :
    spatialThresholdCorrectedKernel (γ • z) w = spatialThresholdCorrectedKernel z w := by
  unfold spatialThresholdCorrectedKernel
  rw [spatialThresholdKernel_modular_left]

theorem spatialThresholdKernel_modular
    (γ δ : SL(2, ℤ)) (z w : UpperHalfPlane) :
    spatialThresholdKernel (γ • z) (δ • w) = spatialThresholdKernel z w := by
  rw [spatialThresholdKernel_modular_left, spatialThresholdKernel_modular_right]

theorem spatialThresholdCorrectedKernel_modular
    (γ δ : SL(2, ℤ)) (z w : UpperHalfPlane) :
    spatialThresholdCorrectedKernel (γ • z) (δ • w) = spatialThresholdCorrectedKernel z w := by
  rw [spatialThresholdCorrectedKernel_modular_left, spatialThresholdCorrectedKernel_modular_right]

end GapFamily.Analytic.SpatialPoint
