import GapFamily.Analytic.Spatial.SpatialOrbitLaplacianFromForm
import GapFamily.Analytic.Spatial.SpatialOrbitFormOperator

/-! Actual Laplacian-domain membership and the operator value for every spatial
orbit integral output. The form witness and weak equation are both constructed. -/

noncomputable section
namespace GapFamily.Analytic.SpatialPoint
open ModularGradient

theorem spatialOrbitIntegralOperator_laplacian_data (s : ℝ) (hs : 1 < s) (F : ModularHilbert) :
    ∃ hdom : spatialOrbitIntegralOperator s hs F ∈ laplacian.domain,
      laplacian ⟨spatialOrbitIntegralOperator s hs F, hdom⟩ =
        ((s : ℂ) * (1 - (s : ℂ))) • spatialOrbitIntegralOperator s hs F +
          (s : ℂ)^2 • spatialOrbitIntegralOperator (s + 1) (by linarith) F :=
  exists_spatialOrbit_laplacian_of_form s hs F (spatialOrbitFormOperator s hs F)
    (formEmbedding_spatialOrbitFormOperator s hs F)

theorem spatialOrbitIntegralOperator_mem_laplacian_domain (s : ℝ) (hs : 1 < s)
    (F : ModularHilbert) : spatialOrbitIntegralOperator s hs F ∈ laplacian.domain :=
  (spatialOrbitIntegralOperator_laplacian_data s hs F).choose

/-- The literal unbounded modular Laplacian acts on the actual bounded kernel output. -/
theorem laplacian_spatialOrbitIntegralOperator (s : ℝ) (hs : 1 < s) (F : ModularHilbert) :
    laplacian ⟨spatialOrbitIntegralOperator s hs F,
      spatialOrbitIntegralOperator_mem_laplacian_domain s hs F⟩ =
      ((s : ℂ) * (1 - (s : ℂ))) • spatialOrbitIntegralOperator s hs F +
        (s : ℂ)^2 • spatialOrbitIntegralOperator (s + 1) (by linarith) F :=
  (spatialOrbitIntegralOperator_laplacian_data s hs F).choose_spec

end GapFamily.Analytic.SpatialPoint
