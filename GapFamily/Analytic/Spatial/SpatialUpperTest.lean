import GapFamily.Analytic.Modular.Periodization.ModularPeriodizationIntegrable
import GapFamily.Analytic.Poincare.PoincareLaplacianTest

noncomputable section
namespace GapFamily.Analytic.SpatialPoint
open Set UpperHalfPlane LaplacianCovariance PoincareWeak
open scoped ContDiff

/-- A genuine compact upper-plane test has compact support after restriction to
actual upper-half-plane points. -/
theorem hasCompactSupport_upper_restrict {ψ : ℂ → ℂ}
    (hc : HasCompactSupport ψ) (hs : tsupport ψ ⊆ upperHalfPlaneSet) :
    HasCompactSupport (fun z : UpperHalfPlane => ψ z) := by
  have hK := compact_modular_support_preimage_of_upper_support hc hs
  apply hK.of_isClosed_subset (isClosed_tsupport _)
  apply closure_minimal
  · intro z hz
    exact subset_tsupport ψ hz
  · exact hK.isClosed

/-- The actual hyperbolic test Laplacian also has compact support in the upper
half-plane; there is no assumption on the support of an unknown field. -/
theorem hasCompactSupport_upper_laplacian_test {ψ : ℂ → ℂ}
    (hc : HasCompactSupport ψ) (hs : tsupport ψ ⊆ upperHalfPlaneSet) :
    HasCompactSupport (fun z : UpperHalfPlane => ordinaryHyperbolicLaplacian ψ z) :=
  hasCompactSupport_upper_restrict (ordinaryHyperbolicLaplacian_hasCompactSupport hc)
    ((ordinaryHyperbolicLaplacian_tsupport_subset ψ).trans hs)

end GapFamily.Analytic.SpatialPoint
