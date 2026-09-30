import GapFamily.Analytic.Spatial.SpatialOrbitGradientOperator
import GapFamily.Analytic.Spatial.SpatialOrbitIntegralDerivative
import GapFamily.Analytic.Elliptic.GradientLocalIBP
import Mathlib.Analysis.Calculus.FDeriv.Star

noncomputable section
namespace GapFamily.Analytic.SpatialPoint
open Set Filter MeasureTheory UpperHalfPlane ModularGradient
open scoped ContDiff MatrixGroups

/-- The actual C1 ordinary integral is a representative of the existing Schur value operator. -/
theorem spatialOrbitIntegralFunction_ae (s : ℝ) (hs : 1 < s) (f : ModularHilbert) :
    spatialOrbitIntegralOperator s hs f =ᵐ[modularMeasure]
      fun z : UpperHalfPlane => spatialOrbitIntegralFunction s f z := by
  simpa only [spatialOrbitIntegralFunction, ofComplex_apply] using spatialOrbitIntegralOperator_ae s hs f

/-- The literal integral representative has the actual modular invariance. -/
theorem spatialOrbitIntegralFunction_modular (s : ℝ) (f : ModularHilbert)
    (z : UpperHalfPlane) (γ : SL(2, ℤ)) :
    spatialOrbitIntegralFunction s f (γ • z : UpperHalfPlane) = spatialOrbitIntegralFunction s f z := by
  simp only [spatialOrbitIntegralFunction, ofComplex_apply, spatialOrbitKernel_modular_left]

/-- Every L² frame output is the actual spatial derivative of the integral representative. -/
theorem spatialOrbitFrameOperator_ae_fderiv (s : ℝ) (hs : 1 < s) (v : ℂ) (f : ModularHilbert) :
    spatialOrbitFrameOperator s hs v f =ᵐ[modularMeasure]
      fun z : UpperHalfPlane => z.im • fderiv ℝ (spatialOrbitIntegralFunction s f) (z : ℂ) v := by
  filter_upwards [spatialOrbitFrameOperator_ae s hs v f] with z hz
  rw [hz, fderiv_spatialOrbitIntegralFunction s hs f z,
    ContinuousLinearMap.integral_apply (integrable_spatialOrbitIntegral_derivative s hs f z),
    ← integral_smul]
  apply integral_congr_ae
  filter_upwards [] with w
  simp only [spatialOrbitFrameKernel, smul_apply, Complex.real_smul, smul_eq_mul]
  ring

/-- Actual finite frame energy for every modular Hilbert source, with no domain premise. -/
theorem memLp_spatialOrbitIntegralFunction_frame (s : ℝ) (hs : 1 < s) (v : ℂ) (f : ModularHilbert) :
    MemLp (fun z : UpperHalfPlane => z.im • fderiv ℝ (spatialOrbitIntegralFunction s f) (z : ℂ) v)
      2 modularMeasure :=
  (memLp_congr_ae (spatialOrbitFrameOperator_ae_fderiv s hs v f)).mp (Lp.memLp (spatialOrbitFrameOperator s hs v f))

/-- The two existing Hilbert gradient components are literal derivatives of one actual representative. -/
theorem spatialOrbitGradientOperator_ae_fderiv (s : ℝ) (hs : 1 < s) (f : ModularHilbert) :
    ((WithLp.ofLp (spatialOrbitGradientOperator s hs f)).1 =ᵐ[modularMeasure]
      fun z : UpperHalfPlane => z.im • fderiv ℝ (spatialOrbitIntegralFunction s f) (z : ℂ) 1) ∧
    ((WithLp.ofLp (spatialOrbitGradientOperator s hs f)).2 =ᵐ[modularMeasure]
      fun z : UpperHalfPlane => z.im • fderiv ℝ (spatialOrbitIntegralFunction s f) (z : ℂ) Complex.I) :=
  ⟨spatialOrbitFrameOperator_ae_fderiv s hs 1 f, spatialOrbitFrameOperator_ae_fderiv s hs Complex.I f⟩

/-- Genuine ordinary-area integrability for both compact-test weak derivative pairings. -/
theorem spatialOrbitIntegralFunction_weakDerivative_integrable (s : ℝ) (hs : 1 < s)
    (f : ModularHilbert) (ψ : ℂ → ℂ) (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    (hupper : tsupport ψ ⊆ upperHalfPlaneSet) (v : ℂ) :
    Integrable (fun z : ℂ => star (ψ z) * fderiv ℝ (spatialOrbitIntegralFunction s f) z v) volume ∧
    Integrable (fun z : ℂ => star (fderiv ℝ ψ z v) * spatialOrbitIntegralFunction s f z) volume := by
  have hf := contDiffOn_spatialOrbitIntegralFunction s hs f
  have hstar : ContDiff ℝ 1 (fun z => star (ψ z)) := Complex.conjCLE.contDiff.comp (hψ.of_le (by simp))
  have hcstar : HasCompactSupport (fun z => star (ψ z)) := hc.comp_left (star_zero ℂ)
  have hsstar : tsupport (fun z => star (ψ z)) ⊆ upperHalfPlaneSet := by
    exact (tsupport_comp_subset (star_zero ℂ) ψ).trans hupper
  have hleft := Dirichlet.local_fderiv_mul_test_integrable isOpen_upperHalfPlaneSet hf
    hstar.continuous hcstar hsstar v
  have hright := Dirichlet.local_mul_fderiv_test_integrable hf.continuousOn hstar hcstar hsstar v
  constructor
  · simpa only [mul_comm] using hleft
  · simpa only [fderiv_star, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, starL'_apply, starAddEquiv_apply, mul_comm] using hright

/-- The proved gradient satisfies actual ordinary compact-test identities across all upper seams. -/
theorem integral_spatialOrbitIntegralFunction_weakDerivative (s : ℝ) (hs : 1 < s)
    (f : ModularHilbert) (ψ : ℂ → ℂ) (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    (hupper : tsupport ψ ⊆ upperHalfPlaneSet) (v : ℂ) :
    (∫ z : ℂ, star (ψ z) * fderiv ℝ (spatialOrbitIntegralFunction s f) z v) =
      -(∫ z : ℂ, star (fderiv ℝ ψ z v) * spatialOrbitIntegralFunction s f z) := by
  have hf := contDiffOn_spatialOrbitIntegralFunction s hs f
  have hstar : ContDiff ℝ 1 (fun z => star (ψ z)) := Complex.conjCLE.contDiff.comp (hψ.of_le (by simp))
  have hcstar : HasCompactSupport (fun z => star (ψ z)) := hc.comp_left (star_zero ℂ)
  have hsstar : tsupport (fun z => star (ψ z)) ⊆ upperHalfPlaneSet := by
    exact (tsupport_comp_subset (star_zero ℂ) ψ).trans hupper
  have h := Dirichlet.local_integral_fderiv_mul_eq_neg isOpen_upperHalfPlaneSet hf hstar hcstar hsstar v
  simpa only [fderiv_star, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, starL'_apply, starAddEquiv_apply, mul_comm] using h

end GapFamily.Analytic.SpatialPoint
