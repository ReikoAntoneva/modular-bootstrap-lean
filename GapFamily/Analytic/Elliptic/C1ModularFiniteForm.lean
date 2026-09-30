import GapFamily.Analytic.Elliptic.C1ModularSeed
import GapFamily.Analytic.Elliptic.C1PeriodizationGraph

noncomputable section
namespace GapFamily.Analytic.C1ModularForm
open Set Filter MeasureTheory UpperHalfPlane ModularGradient
open scoped ContDiff MatrixGroups Topology

/-- Finite-height modular C1 fields have their literal value and frame gradient in the closed form. -/
theorem exists_form_of_C1_finite_height (F : ℂ → ℂ)
    (hF : ContDiffOn ℝ 1 F upperHalfPlaneSet)
    (hinv : ∀ γ : SL(2, ℤ), ∀ τ : UpperHalfPlane, F (γ • τ : UpperHalfPlane) = F τ)
    (H : ℝ) (hzero : ∀ τ : UpperHalfPlane, τ ∈ ModularGroup.fd → H < τ.im → F τ = 0) :
    ∃ u : FormDomain,
      formEmbedding u =ᵐ[modularMeasure] (fun τ : UpperHalfPlane => F τ) ∧
      (WithLp.ofLp (formGradient u)).1 =ᵐ[modularMeasure] directional F 1 ∧
      (WithLp.ofLp (formGradient u)).2 =ᵐ[modularMeasure] directional F Complex.I := by
  obtain ⟨ψ, hψ, hc, hs, heq⟩ := exists_compact_upper_C1_seed F hF hinv H hzero
  obtain ⟨u, hu, hx, hy⟩ := C1Periodization.exists_form_periodization_of_C1 ψ hψ hc hs
  have hd (v : ℂ) : directional (modularPeriodization ψ) v = directional F v := by
    funext τ
    have hg : modularPeriodization ψ =ᶠ[𝓝 (τ : ℂ)] F := by
      filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds τ.im_pos] with z hz
      exact heq ⟨z, hz⟩
    simp only [directional, hg.fderiv_eq (𝕜 := ℝ)]
  refine ⟨u, hu.trans (Filter.Eventually.of_forall heq), ?_, ?_⟩
  · simpa only [hd] using hx
  · simpa only [hd] using hy

end GapFamily.Analytic.C1ModularForm
