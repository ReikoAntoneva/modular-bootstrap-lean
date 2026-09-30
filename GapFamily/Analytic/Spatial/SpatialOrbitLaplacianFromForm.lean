import GapFamily.Analytic.Modular.ModularContinuousWeakDomain
import GapFamily.Analytic.Spatial.SpatialOrbitOperatorWeak

/-! The genuine compact-test recurrence identifies the actual Laplacian value
as soon as the independently constructed completed form witness is supplied. -/

noncomputable section
namespace GapFamily.Analytic.SpatialPoint
open Set Filter MeasureTheory UpperHalfPlane ModularGradient
open scoped ContDiff MatrixGroups

/-- This bridge requires a completed-form value witness, not an operator-domain
witness. Its weak equation, representatives, and right-hand side are actual. -/
theorem exists_spatialOrbit_laplacian_of_form (s : ℝ) (hs : 1 < s) (F : ModularHilbert)
    (u : FormDomain) (hu : formEmbedding u = spatialOrbitIntegralOperator s hs F) :
    ∃ hdom : spatialOrbitIntegralOperator s hs F ∈ laplacian.domain,
      laplacian ⟨spatialOrbitIntegralOperator s hs F, hdom⟩ =
        ((s : ℂ) * (1 - (s : ℂ))) • spatialOrbitIntegralOperator s hs F +
          (s : ℂ)^2 • spatialOrbitIntegralOperator (s + 1) (by linarith) F := by
  have hs1 : 1 < s + 1 := by linarith
  let c : ℂ := (s : ℂ) * (1 - (s : ℂ))
  let d : ℂ := (s : ℂ)^2
  let G : ModularHilbert := c • spatialOrbitIntegralOperator s hs F +
    d • spatialOrbitIntegralOperator (s + 1) hs1 F
  let g : ℂ → ℂ := fun z => c * spatialOrbitIntegralFunction s F z +
    d * spatialOrbitIntegralFunction (s + 1) F z
  have hf := (contDiffOn_spatialOrbitIntegralFunction s hs F).continuousOn
  have hf1 := (contDiffOn_spatialOrbitIntegralFunction (s + 1) hs1 F).continuousOn
  have hg : ContinuousOn g upperHalfPlaneSet :=
    (continuousOn_const.mul hf).add (continuousOn_const.mul hf1)
  have hgmod : ∀ γ : SL(2, ℤ), ∀ τ : UpperHalfPlane, g (γ • τ : UpperHalfPlane) = g τ := by
    intro γ τ
    simp only [g, spatialOrbitIntegralFunction_modular]
  have huAE : formEmbedding u =ᵐ[modularMeasure]
      (fun τ : UpperHalfPlane => spatialOrbitIntegralFunction s F τ) := by
    rw [hu]
    exact spatialOrbitIntegralFunction_ae s hs F
  have hGAE : G =ᵐ[modularMeasure] (fun τ : UpperHalfPlane => g τ) := by
    filter_upwards [Lp.coeFn_add (c • spatialOrbitIntegralOperator s hs F)
        (d • spatialOrbitIntegralOperator (s + 1) hs1 F),
      Lp.coeFn_smul c (spatialOrbitIntegralOperator s hs F),
      Lp.coeFn_smul d (spatialOrbitIntegralOperator (s + 1) hs1 F),
      spatialOrbitIntegralFunction_ae s hs F,
      spatialOrbitIntegralFunction_ae (s + 1) hs1 F] with τ ha hc hd h0 h1
    change (c • spatialOrbitIntegralOperator s hs F +
      d • spatialOrbitIntegralOperator (s + 1) hs1 F) τ = _
    simp only [ha, Pi.add_apply, hc, hd, Pi.smul_apply, h0, h1, smul_eq_mul, g]
  have hweak : ∀ (ψ : ℂ → ℂ), ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ upperHalfPlaneSet →
      (∫ τ : UpperHalfPlane, star (LaplacianCovariance.ordinaryHyperbolicLaplacian ψ τ) *
        spatialOrbitIntegralFunction s F τ ∂volume) =
        ∫ τ : UpperHalfPlane, star (ψ τ) * g τ ∂volume := by
    intro ψ hψ hc hsupp
    obtain ⟨_, hi0, hi1⟩ := spatialOrbitIntegralFunction_weak_integrable s hs F ψ hψ hc hsupp
    have he := integral_spatialOrbitIntegralFunction_weak_recurrence s hs F ψ hψ hc hsupp
    have hprod : (fun τ : UpperHalfPlane => star (ψ τ) * g τ) =
        fun τ : UpperHalfPlane => c * (star (ψ τ) * spatialOrbitIntegralFunction s F τ) +
          d * (star (ψ τ) * spatialOrbitIntegralFunction (s + 1) F τ) := by
      funext τ
      dsimp [g]
      ring
    rw [hprod, integral_add (hi0.const_mul c) (hi1.const_mul d),
      integral_const_mul, integral_const_mul]
    exact (sub_eq_iff_eq_add.mp he).trans (add_comm _ _)
  obtain ⟨hdom, hvalue⟩ :=
    ModularContinuousWeakDomain.exists_laplacian_value_of_continuous_weak
      u G (spatialOrbitIntegralFunction s F) g hf hg
      (fun γ τ => spatialOrbitIntegralFunction_modular s F τ γ) hgmod huAE hGAE hweak
  exact ⟨hu ▸ hdom, by simpa only [hu, G, c, d] using hvalue⟩

end GapFamily.Analytic.SpatialPoint
