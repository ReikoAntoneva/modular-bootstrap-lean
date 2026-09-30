import GapFamily.Analytic.Spatial.SpatialOrbitPointForm
import GapFamily.Analytic.Spatial.SpatialOrbitWeak
import GapFamily.Analytic.Modular.ModularContinuousWeakDomain

noncomputable section
namespace GapFamily.Analytic.SpatialPoint
open Set Filter MeasureTheory UpperHalfPlane ModularGradient
open scoped ContDiff MatrixGroups

/-- The actual point-source row is in the modular Laplacian domain, with the
literal complex-parameter recurrence as its actual Laplacian value. -/
theorem exists_spatialOrbitPoint_laplacian (s : ℂ) (hs : 1 < s.re) (w : UpperHalfPlane) :
    ∃ hdom : spatialOrbitPointSource s w ∈ laplacian.domain,
      laplacian ⟨spatialOrbitPointSource s w, hdom⟩ =
        (s * (1 - s)) • spatialOrbitPointSource s w +
          s ^ 2 • spatialOrbitPointSource (s + 1) w := by
  have hs1 : 1 < (s + 1).re := by simp only [Complex.add_re, Complex.one_re]; linarith
  obtain ⟨u, hu, _hx, _hy⟩ := exists_spatialOrbitPointForm s hs w
  let f : ℂ → ℂ := fun z => spatialOrbitKernel s (ofComplex z) w
  let g : ℂ → ℂ := fun z => s * (1 - s) * spatialOrbitKernel s (ofComplex z) w +
    s ^ 2 * spatialOrbitKernel (s + 1) (ofComplex z) w
  let G : ModularHilbert := (s * (1 - s)) • spatialOrbitPointSource s w +
    s ^ 2 • spatialOrbitPointSource (s + 1) w
  have hf : ContinuousOn f upperHalfPlaneSet := (contDiffOn_spatialOrbitKernel_left s hs w).continuousOn
  have hg : ContinuousOn g upperHalfPlaneSet :=
    (continuousOn_const.mul hf).add
      (continuousOn_const.mul (contDiffOn_spatialOrbitKernel_left (s + 1) hs1 w).continuousOn)
  have hfmod : ∀ γ : SL(2, ℤ), ∀ τ : UpperHalfPlane, f (γ • τ : UpperHalfPlane) = f τ := by
    intro γ τ
    simp only [f, ofComplex_apply, spatialOrbitKernel_modular_left]
  have hgmod : ∀ γ : SL(2, ℤ), ∀ τ : UpperHalfPlane, g (γ • τ : UpperHalfPlane) = g τ := by
    intro γ τ
    simp only [g, ofComplex_apply, spatialOrbitKernel_modular_left]
  have huAE : formEmbedding u =ᵐ[modularMeasure] (fun τ : UpperHalfPlane => f τ) := by
    rw [hu]
    simpa only [f, ofComplex_apply] using spatialOrbitPointSource_ae s hs w
  have hGAE : G =ᵐ[modularMeasure] (fun τ : UpperHalfPlane => g τ) := by
    filter_upwards [Lp.coeFn_add ((s * (1 - s)) • spatialOrbitPointSource s w)
        (s ^ 2 • spatialOrbitPointSource (s + 1) w),
      Lp.coeFn_smul (s * (1 - s)) (spatialOrbitPointSource s w),
      Lp.coeFn_smul (s ^ 2) (spatialOrbitPointSource (s + 1) w),
      spatialOrbitPointSource_ae s hs w, spatialOrbitPointSource_ae (s + 1) hs1 w]
      with τ ha hc hd h0 h1
    change ((s * (1 - s)) • spatialOrbitPointSource s w +
      s ^ 2 • spatialOrbitPointSource (s + 1) w) τ = _
    simp only [ha, Pi.add_apply, hc, hd, Pi.smul_apply, h0, h1, smul_eq_mul, g, ofComplex_apply]
  have hweak : ∀ (ψ : ℂ → ℂ), ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ upperHalfPlaneSet →
      (∫ τ : UpperHalfPlane, star (LaplacianCovariance.ordinaryHyperbolicLaplacian ψ τ) * f τ ∂volume) =
        ∫ τ : UpperHalfPlane, star (ψ τ) * g τ ∂volume := by
    intro ψ hψ hc hsupp
    obtain ⟨_, hi0, hi1⟩ := spatialOrbitKernel_weak_integrable s hs w ψ hψ hc hsupp
    have he := integral_spatialOrbitKernel_weak_recurrence s hs w ψ hψ hc hsupp
    have hprod : (fun τ : UpperHalfPlane => star (ψ τ) * g τ) =
        fun τ : UpperHalfPlane => (s * (1 - s)) * (star (ψ τ) * spatialOrbitKernel s τ w) +
          s ^ 2 * (star (ψ τ) * spatialOrbitKernel (s + 1) τ w) := by
      funext τ
      simp only [g, ofComplex_apply]
      ring
    rw [hprod, integral_add (hi0.const_mul _) (hi1.const_mul _),
      integral_const_mul, integral_const_mul]
    simpa only [f, ofComplex_apply] using (sub_eq_iff_eq_add.mp he).trans (add_comm _ _)
  obtain ⟨hdom, hvalue⟩ :=
    ModularContinuousWeakDomain.exists_laplacian_value_of_continuous_weak
      u G f g hf hg hfmod hgmod huAE hGAE hweak
  exact ⟨hu ▸ hdom, by simpa only [hu, G] using hvalue⟩

end GapFamily.Analytic.SpatialPoint
