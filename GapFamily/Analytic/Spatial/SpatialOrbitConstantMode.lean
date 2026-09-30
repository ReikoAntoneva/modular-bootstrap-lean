import GapFamily.Analytic.Spatial.SpatialOrbitOperator
import GapFamily.Analytic.Modular.ModularHilbert

noncomputable section
namespace GapFamily.Analytic.SpatialPoint

open MeasureTheory

/-- The actual constant Hilbert vector is an eigenvector with the exact
unnormalized spatial mass. -/
theorem spatialOrbitIntegralOperator_constant (s : ℝ) (hs : 1 < s) :
    spatialOrbitIntegralOperator s hs modularConstant =
      (((Real.pi / (s - 1) : ℝ)) : ℂ) • modularConstant := by
  apply Lp.ext
  filter_upwards [spatialOrbitIntegralOperator_ae s hs modularConstant,
    Lp.coeFn_smul (((Real.pi / (s - 1) : ℝ)) : ℂ) modularConstant,
    modularConstant_ae] with z hA hsmul hconst
  rw [hA, hsmul, Pi.smul_apply, hconst, smul_eq_mul, mul_one]
  calc
    (∫ w : UpperHalfPlane,
        spatialOrbitKernel (s : ℂ) z w * modularConstant w ∂modularMeasure) =
        ∫ w : UpperHalfPlane, spatialOrbitKernel (s : ℂ) z w ∂modularMeasure := by
      apply integral_congr_ae
      filter_upwards [modularConstant_ae] with w hw
      simp only [hw, mul_one]
    _ = (((Real.pi / (s - 1) : ℝ)) : ℂ) := by
      simpa only [spatialOrbitKernel_symm (s : ℂ) z] using
        integral_spatialOrbitKernel s hs z

/-- Applying the spatial operator after projection keeps precisely its constant eigenvalue. -/
theorem spatialOrbitIntegralOperator_comp_constantProjection (s : ℝ) (hs : 1 < s) :
    (spatialOrbitIntegralOperator s hs).comp modularConstantProjection =
      (((Real.pi / (s - 1) : ℝ)) : ℂ) • modularConstantProjection := by
  apply ContinuousLinearMap.ext
  intro f
  change spatialOrbitIntegralOperator s hs (modularConstantProjection f) =
    (((Real.pi / (s - 1) : ℝ)) : ℂ) • modularConstantProjection f
  simp only [modularConstantProjection_apply, map_smul,
    spatialOrbitIntegralOperator_constant, smul_smul]
  rw [mul_comm]

/-- Selfadjointness transfers the proved constant eigenvector identity to the
ordinary modular average of every actual Hilbert vector. -/
theorem modularAverage_spatialOrbitIntegralOperator (s : ℝ) (hs : 1 < s)
    (f : ModularHilbert) :
    modularAverage (spatialOrbitIntegralOperator s hs f) =
      (((Real.pi / (s - 1) : ℝ)) : ℂ) * modularAverage f := by
  have h := (isSelfAdjoint_spatialOrbitIntegralOperator s hs).isSymmetric modularConstant f
  change inner ℂ (spatialOrbitIntegralOperator s hs modularConstant) f =
    inner ℂ modularConstant (spatialOrbitIntegralOperator s hs f) at h
  rw [spatialOrbitIntegralOperator_constant, inner_smul_left] at h
  change (modularMeasure.real Set.univ : ℂ)⁻¹ *
      inner ℂ modularConstant (spatialOrbitIntegralOperator s hs f) =
    (((Real.pi / (s - 1) : ℝ)) : ℂ) *
      ((modularMeasure.real Set.univ : ℂ)⁻¹ * inner ℂ modularConstant f)
  rw [← h]
  simp only [Complex.conj_ofReal]
  ring

/-- Projection after the spatial operator follows from actual selfadjointness,
without a commutation assumption. -/
theorem constantProjection_comp_spatialOrbitIntegralOperator (s : ℝ) (hs : 1 < s) :
    modularConstantProjection.comp (spatialOrbitIntegralOperator s hs) =
      (((Real.pi / (s - 1) : ℝ)) : ℂ) • modularConstantProjection := by
  apply ContinuousLinearMap.ext
  intro f
  change modularConstantProjection (spatialOrbitIntegralOperator s hs f) =
    (((Real.pi / (s - 1) : ℝ)) : ℂ) • modularConstantProjection f
  simp only [modularConstantProjection_apply, modularAverage_spatialOrbitIntegralOperator,
    smul_smul]

end GapFamily.Analytic.SpatialPoint
