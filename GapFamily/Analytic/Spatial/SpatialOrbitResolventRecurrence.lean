import GapFamily.Analytic.Spatial.SpatialOrbitResolventFromForm
import GapFamily.Analytic.Spatial.SpatialOrbitLaplacian

/-! Genuine bounded-operator resolvent recurrences for the actual spatial kernel. -/

noncomputable section
namespace GapFamily.Analytic.SpatialPoint
open ModularGradient ModularPositiveResolvent

theorem spatialOrbitIntegralOperator_resolvent_recurrence (s : ℝ) (hs : 1 < s) :
    spatialOrbitIntegralOperator s hs = (s : ℂ)^2 •
      (shiftedResolvent (s * (s - 1))).comp
        (spatialOrbitIntegralOperator (s + 1) (by linarith)) := by
  apply ContinuousLinearMap.ext
  intro F
  exact spatialOrbit_resolvent_recurrence_of_form s hs F (spatialOrbitFormOperator s hs F)
    (formEmbedding_spatialOrbitFormOperator s hs F)

/-- The normalized operator satisfies T_s=r_s(A+r_s)⁻¹ T_(s+1), with r_s=s(s-1). -/
theorem normalizedOrbitOperator_resolvent_recurrence (s : ℝ) (hs : 1 < s) :
    normalizedOrbitOperator s hs = resolventFactor (s * (s - 1)) *
      normalizedOrbitOperator (s + 1) (by linarith) := by
  apply ContinuousLinearMap.ext
  intro F
  exact normalizedOrbit_resolvent_recurrence_of_form s hs F (spatialOrbitFormOperator s hs F)
    (formEmbedding_spatialOrbitFormOperator s hs F)

end GapFamily.Analytic.SpatialPoint
