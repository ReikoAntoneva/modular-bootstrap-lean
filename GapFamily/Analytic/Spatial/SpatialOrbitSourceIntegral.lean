import GapFamily.Analytic.Spatial.SpatialOrbitWeightedSourceContinuity
import GapFamily.Analytic.Spatial.SpatialOrbitOperator

/-! Bochner integration of actual weighted point sources reproduces the actual
spatial orbit integral operator after removing the cusp weight. -/

noncomputable section
namespace GapFamily.Analytic.SpatialPoint
open Set Filter MeasureTheory UpperHalfPlane
open scoped Topology

/-- Compact support of the density makes its actual weighted source
superposition ordinarily Bochner integrable. -/
theorem integrable_smul_spatialOrbitWeightedSource_of_compact_support
    (α : ℝ) (hα : 0 ≤ α) (hhalf : α < 1 / 2)
    (s : ℂ) (hs : 1 < s.re) (f : ModularHilbert)
    (S : Set UpperHalfPlane) (hS : IsCompact S)
    (hf : ∀ᵐ w ∂modularMeasure, w ∉ S → f w = 0) :
    Integrable (fun w => f w • spatialOrbitWeightedSource α hα hhalf s w)
      modularMeasure := by
  have hW := continuous_spatialOrbitWeightedSource_source α hα hhalf s hs
  obtain ⟨C, hC⟩ := hS.exists_bound_of_continuousOn hW.continuousOn
  have hfi : Integrable (fun w => ‖f w‖) modularMeasure :=
    (MemLp.integrable (by norm_num : (1 : ENNReal) ≤ 2) (Lp.memLp f)).norm
  apply (hfi.const_mul C).mono'
    ((Lp.aestronglyMeasurable f).smul hW.aestronglyMeasurable)
  filter_upwards [hf] with w hw
  change ‖f w • spatialOrbitWeightedSource α hα hhalf s w‖ ≤ C * ‖f w‖
  by_cases hwS : w ∈ S
  · rw [norm_smul, mul_comm C]
    exact mul_le_mul_of_nonneg_left (hC w hwS) (norm_nonneg _)
  · simp [hw hwS]

/-- The Hilbert pairing with an unweighted actual source is its literal scalar
kernel pairing, with no choice of representatives left in the statement. -/
theorem inner_cuspWeightedInput_spatialOrbitWeightedSource
    (α : ℝ) (hα : 0 ≤ α) (hhalf : α < 1 / 2)
    (s : ℂ) (hs : 1 < s.re) (w : UpperHalfPlane) (g : ModularHilbert) :
    inner ℂ g (cuspWeightedInput α hα (spatialOrbitWeightedSource α hα hhalf s w)) =
      ∫ z, star (g z) * spatialOrbitKernel s z w ∂modularMeasure := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [cuspWeightedInput_spatialOrbitWeightedSource_ae α hα hhalf s hs w]
    with z hz
  simp only [hz, RCLike.inner_apply]
  exact mul_comm _ _

/-- Any ordinarily integrable Bochner superposition of the actual weighted
sources unweights to the literal Schur integral operator. -/
theorem cuspWeightedInput_integral_spatialOrbitWeightedSource
    (α : ℝ) (hα : 0 ≤ α) (hhalf : α < 1 / 2)
    (s : ℝ) (hs : 1 < s) (f : ModularHilbert)
    (hi : Integrable (fun w => f w • spatialOrbitWeightedSource α hα hhalf (s : ℂ) w)
      modularMeasure) :
    cuspWeightedInput α hα
      (∫ w, f w • spatialOrbitWeightedSource α hα hhalf (s : ℂ) w ∂modularMeasure) =
        spatialOrbitIntegralOperator s hs f := by
  apply ext_inner_left ℂ
  intro g
  have hi' := (cuspWeightedInput α hα).integrable_comp hi
  have hp := SchurKernelPairing.integrable_pairing
    (spatialOrbitKernelData s hs).measurable (spatialOrbitKernelData s hs).nonneg
    (spatialOrbitKernelData s hs).row_integrable (spatialOrbitKernelData s hs).row_bound
    (spatialOrbitKernelData s hs).column_integrable (spatialOrbitKernelData s hs).column_bound f g
  calc
    inner ℂ g (cuspWeightedInput α hα
        (∫ w, f w • spatialOrbitWeightedSource α hα hhalf (s : ℂ) w ∂modularMeasure)) =
        ∫ w, inner ℂ g (cuspWeightedInput α hα
          (f w • spatialOrbitWeightedSource α hα hhalf (s : ℂ) w)) ∂modularMeasure := by
      rw [← (cuspWeightedInput α hα).integral_comp_comm hi]
      exact ((innerSL ℂ g).integral_comp_comm hi').symm
    _ = ∫ w, (∫ z, star (g z) * spatialOrbitKernel (s : ℂ) z w ∂modularMeasure) *
        f w ∂modularMeasure := by
      apply integral_congr_ae
      apply Eventually.of_forall
      intro w
      dsimp only
      rw [map_smul, inner_smul_right,
        inner_cuspWeightedInput_spatialOrbitWeightedSource α hα hhalf (s : ℂ)
          (by simpa using hs) w g, mul_comm]
    _ = inner ℂ g (spatialOrbitIntegralOperator s hs f) := by
      rw [spatialOrbitIntegralOperator, SchurIntegralOperator.inner_integralOperator]
      exact (SchurKernelPairing.pairing_fubini f g hp).symm

/-- For every compactly supported L² density, integrating the actual weighted
point sources and removing the weight reproduces the actual spatial operator. -/
theorem cuspWeightedInput_integral_spatialOrbitWeightedSource_of_compact_support
    (α : ℝ) (hα : 0 ≤ α) (hhalf : α < 1 / 2)
    (s : ℝ) (hs : 1 < s) (f : ModularHilbert)
    (S : Set UpperHalfPlane) (hS : IsCompact S)
    (hf : ∀ᵐ w ∂modularMeasure, w ∉ S → f w = 0) :
    cuspWeightedInput α hα
      (∫ w, f w • spatialOrbitWeightedSource α hα hhalf (s : ℂ) w ∂modularMeasure) =
        spatialOrbitIntegralOperator s hs f :=
  cuspWeightedInput_integral_spatialOrbitWeightedSource α hα hhalf s hs f
    (integrable_smul_spatialOrbitWeightedSource_of_compact_support
      α hα hhalf (s : ℂ) (by simpa using hs) f S hS hf)

end GapFamily.Analytic.SpatialPoint
