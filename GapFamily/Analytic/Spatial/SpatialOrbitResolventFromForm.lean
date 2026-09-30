import GapFamily.Analytic.Spatial.SpatialOrbitLaplacianFromForm
import GapFamily.Analytic.Modular.ModularPositiveResolventBasic
import GapFamily.Analytic.Spatial.SpatialOrbitBoundedBridge

/-! Exact resolvent recurrence algebra after the genuine completed form witness.
The actual spatial witness is instantiated in the final application leaf. -/

noncomputable section
namespace GapFamily.Analytic.SpatialPoint
open ModularGradient ModularPositiveResolvent

theorem spatialOrbit_resolvent_recurrence_of_form (s : ℝ) (hs : 1 < s) (F : ModularHilbert)
    (u : FormDomain) (hu : formEmbedding u = spatialOrbitIntegralOperator s hs F) :
    spatialOrbitIntegralOperator s hs F = (s : ℂ)^2 •
      shiftedResolvent (s * (s - 1)) (spatialOrbitIntegralOperator (s + 1) (by linarith) F) := by
  have hr : 0 < s * (s - 1) := mul_pos (by linarith) (by linarith)
  obtain ⟨hdom, hA⟩ := exists_spatialOrbit_laplacian_of_form s hs F u hu
  have he := shiftedResolvent_leftInverse (s * (s - 1)) hr
    ⟨spatialOrbitIntegralOperator s hs F, hdom⟩
  have hshift : laplacian ⟨spatialOrbitIntegralOperator s hs F, hdom⟩ +
      ((s * (s - 1) : ℝ) : ℂ) • spatialOrbitIntegralOperator s hs F =
      (s : ℂ)^2 • spatialOrbitIntegralOperator (s + 1) (by linarith) F := by
    rw [hA]
    push_cast
    module
  change shiftedResolvent (s * (s - 1))
    (laplacian ⟨spatialOrbitIntegralOperator s hs F, hdom⟩ +
      ((s * (s - 1) : ℝ) : ℂ) • spatialOrbitIntegralOperator s hs F) =
      spatialOrbitIntegralOperator s hs F at he
  rw [hshift, map_smul] at he
  exact he.symm

/-- The exact mass normalization turns s² into r=s(s-1) in the recurrence. -/
theorem normalizedOrbit_resolvent_recurrence_of_form (s : ℝ) (hs : 1 < s) (F : ModularHilbert)
    (u : FormDomain) (hu : formEmbedding u = spatialOrbitIntegralOperator s hs F) :
    normalizedOrbitOperator s hs F = resolventFactor (s * (s - 1))
      (normalizedOrbitOperator (s + 1) (by linarith) F) := by
  change ((((s - 1) / Real.pi : ℝ) : ℂ)) • spatialOrbitIntegralOperator s hs F =
    ((s * (s - 1) : ℝ) : ℂ) • shiftedResolvent (s * (s - 1))
      (((((s + 1) - 1) / Real.pi : ℝ) : ℂ) •
        spatialOrbitIntegralOperator (s + 1) (by linarith) F)
  rw [spatialOrbit_resolvent_recurrence_of_form s hs F u hu, map_smul, smul_smul, smul_smul]
  congr 1
  push_cast
  ring

end GapFamily.Analytic.SpatialPoint
