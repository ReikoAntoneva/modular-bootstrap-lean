import GapFamily.Analytic.Spatial.SpatialOrbitOperatorFubini
import GapFamily.Analytic.Spatial.SpatialOrbitWeak
import GapFamily.Analytic.Spatial.SpatialOrbitGradientIdentification

noncomputable section
namespace GapFamily.Analytic.SpatialPoint
open Set Filter MeasureTheory UpperHalfPlane LaplacianCovariance PoincareWeak
open scoped ContDiff

/-- All compact-test terms of the operator-output recurrence are ordinary integrable functions. -/
theorem spatialOrbitIntegralFunction_weak_integrable (s : ℝ) (hs : 1 < s)
    (f : ModularHilbert) (ψ : ℂ → ℂ) (hψ : ContDiff ℝ ∞ ψ)
    (hc : HasCompactSupport ψ) (hupper : tsupport ψ ⊆ upperHalfPlaneSet) :
    Integrable (fun z : UpperHalfPlane => star (ordinaryHyperbolicLaplacian ψ z) *
        spatialOrbitIntegralFunction s f z) volume ∧
      Integrable (fun z : UpperHalfPlane => star (ψ z) * spatialOrbitIntegralFunction s f z) volume ∧
      Integrable (fun z : UpperHalfPlane => star (ψ z) * spatialOrbitIntegralFunction (s + 1) f z) volume := by
  have ha := ((ordinaryHyperbolicLaplacian_continuous hψ).comp continuous_coe).star
  have hb := (hψ.continuous.comp continuous_coe).star
  have hca := (hasCompactSupport_upper_laplacian_test hc hupper).comp_left (star_zero ℂ)
  have hcb := (hasCompactSupport_upper_restrict hc hupper).comp_left (star_zero ℂ)
  exact ⟨integrable_spatialOrbitIntegralFunction_test s hs f _ ha hca,
    integrable_spatialOrbitIntegralFunction_test s hs f _ hb hcb,
    integrable_spatialOrbitIntegralFunction_test (s + 1) (by linarith) f _ hb hcb⟩

/-- The genuine bounded integral operator outputs obey the kernel recurrence
against all smooth compact upper tests, using their literal global representatives. -/
theorem integral_spatialOrbitIntegralFunction_weak_recurrence (s : ℝ) (hs : 1 < s)
    (f : ModularHilbert) (ψ : ℂ → ℂ) (hψ : ContDiff ℝ ∞ ψ)
    (hc : HasCompactSupport ψ) (hupper : tsupport ψ ⊆ upperHalfPlaneSet) :
    (∫ z : UpperHalfPlane, star (ordinaryHyperbolicLaplacian ψ z) *
        spatialOrbitIntegralFunction s f z) -
      (s : ℂ) * (1 - (s : ℂ)) *
        (∫ z : UpperHalfPlane, star (ψ z) * spatialOrbitIntegralFunction s f z) =
      (s : ℂ) ^ 2 *
        (∫ z : UpperHalfPlane, star (ψ z) * spatialOrbitIntegralFunction (s + 1) f z) := by
  let a : UpperHalfPlane → ℂ := fun z => star (ordinaryHyperbolicLaplacian ψ z)
  let b : UpperHalfPlane → ℂ := fun z => star (ψ z)
  have ha : Continuous a := ((ordinaryHyperbolicLaplacian_continuous hψ).comp continuous_coe).star
  have hb : Continuous b := (hψ.continuous.comp continuous_coe).star
  have hca : HasCompactSupport a :=
    (hasCompactSupport_upper_laplacian_test hc hupper).comp_left (star_zero ℂ)
  have hcb : HasCompactSupport b :=
    (hasCompactSupport_upper_restrict hc hupper).comp_left (star_zero ℂ)
  have hs' : 1 < s + 1 := by linarith
  change (∫ z : UpperHalfPlane, a z * spatialOrbitIntegralFunction s f z) -
    (s : ℂ) * (1 - (s : ℂ)) * (∫ z : UpperHalfPlane, b z * spatialOrbitIntegralFunction s f z) =
    (s : ℂ)^2 * (∫ z : UpperHalfPlane, b z * spatialOrbitIntegralFunction (s + 1) f z)
  rw [integral_spatialOrbitIntegralFunction_test s hs f a ha hca,
    integral_spatialOrbitIntegralFunction_test s hs f b hb hcb,
    integral_spatialOrbitIntegralFunction_test (s + 1) hs' f b hb hcb]
  have hiA := integrable_spatialOrbitKernel_test_source s hs f a ha hca
  have hiB := integrable_spatialOrbitKernel_test_source s hs f b hb hcb
  rw [← integral_const_mul, ← integral_sub hiA (hiB.const_mul _), ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with w
  have he := integral_spatialOrbitKernel_weak_recurrence (s : ℂ) (by simpa using hs) w ψ hψ hc hupper
  change (∫ z : UpperHalfPlane, a z * spatialOrbitKernel (s : ℂ) z w) -
    (s : ℂ) * (1 - (s : ℂ)) * (∫ z : UpperHalfPlane, b z * spatialOrbitKernel (s : ℂ) z w) =
    (s : ℂ)^2 * (∫ z : UpperHalfPlane, b z * spatialOrbitKernel ((s : ℂ) + 1) z w) at he
  simp only [Complex.ofReal_add, Complex.ofReal_one]
  linear_combination he * f w

/-- Both literal fields in the weak recurrence represent the actual completed
L² operators. No operator-domain membership is assumed or concluded here. -/
theorem spatialOrbitIntegralOperator_weak_representatives (s : ℝ) (hs : 1 < s)
    (f : ModularHilbert) :
    (spatialOrbitIntegralOperator s hs f =ᵐ[modularMeasure]
      fun z : UpperHalfPlane => spatialOrbitIntegralFunction s f z) ∧
    (spatialOrbitIntegralOperator (s + 1) (by linarith) f =ᵐ[modularMeasure]
      fun z : UpperHalfPlane => spatialOrbitIntegralFunction (s + 1) f z) :=
  ⟨spatialOrbitIntegralFunction_ae s hs f,
    spatialOrbitIntegralFunction_ae (s + 1) (by linarith) f⟩

end GapFamily.Analytic.SpatialPoint
