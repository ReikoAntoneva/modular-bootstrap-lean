import GapFamily.Analytic.Elliptic.C1PeriodizationGraphBasic

noncomputable section
namespace GapFamily.Analytic.C1Periodization
open Set Filter MeasureTheory UpperHalfPlane ModularGradient
open scoped ContDiff MatrixGroups Topology

/-- Pointwise convergence of seeds supported in one compact upper set passes
to actual periodizations, because one finite orbit sum suffices at each point. -/
theorem tendsto_periodization {K : Set ℂ} (hK : IsCompact K)
    (hKH : K ⊆ upperHalfPlaneSet) {ψ : ℂ → ℂ} {ψn : ℕ → ℂ → ℂ}
    (hψK : tsupport ψ ⊆ K) (hψnK : ∀ n, tsupport (ψn n) ⊆ K)
    (hlim : ∀ z : ℂ, Tendsto (fun n => ψn n z) atTop (𝓝 (ψ z)))
    (τ : UpperHalfPlane) :
    Tendsto (fun n => modularPeriodization (ψn n) τ) atTop
      (𝓝 (modularPeriodization ψ τ)) := by
  obtain ⟨s, hgerm⟩ := exists_finset_common_support_germ hK hKH τ
  have heq (φ : ℂ → ℂ) (hφK : tsupport φ ⊆ K) :
      modularPeriodization φ τ =
        (1 / 2 : ℂ) * ∑ γ ∈ s, φ (rawModularAction γ τ) :=
    (hgerm.self_of_nhds φ hφK).1
  have heqn (n : ℕ) := heq (ψn n) (hψnK n)
  simp only [heqn, heq ψ hψK]
  exact (tendsto_finsetSum s (fun γ _ => hlim (rawModularAction γ τ))).const_mul _

/-- Pointwise convergence of actual seed derivative operators passes to every
actual directional derivative of their periodizations. -/
theorem tendsto_directional_periodization {K : Set ℂ} (hK : IsCompact K)
    (hKH : K ⊆ upperHalfPlaneSet) {ψ : ℂ → ℂ} {ψn : ℕ → ℂ → ℂ}
    (hψ : ContDiff ℝ 1 ψ) (hψn : ∀ n, ContDiff ℝ 1 (ψn n))
    (hψK : tsupport ψ ⊆ K) (hψnK : ∀ n, tsupport (ψn n) ⊆ K)
    (hlim : ∀ z : ℂ, Tendsto (fun n => fderiv ℝ (ψn n) z) atTop
      (𝓝 (fderiv ℝ ψ z))) (τ : UpperHalfPlane) (v : ℂ) :
    Tendsto (fun n => directional (modularPeriodization (ψn n)) v τ) atTop
      (𝓝 (directional (modularPeriodization ψ) v τ)) := by
  obtain ⟨s, hs⟩ := exists_finset_common_support_fderiv hK hKH τ
  have heq (φ : ℂ → ℂ) (hφ : ContDiff ℝ 1 φ) (hφK : tsupport φ ⊆ K) :
      fderiv ℝ (modularPeriodization φ) τ v =
        (1 / 2 : ℂ) * ∑ γ ∈ s, fderiv ℝ (φ ∘ rawModularAction γ) τ v :=
    (hs φ hφ hφK).1 v
  have heqn (n : ℕ) := heq (ψn n) (hψn n) (hψnK n)
  have hterm (γ : SL(2, ℤ)) :
      Tendsto (fun n => fderiv ℝ (ψn n ∘ rawModularAction γ) τ v) atTop
        (𝓝 (fderiv ℝ (ψ ∘ rawModularAction γ) τ v)) := by
    have hchain (φ : ℂ → ℂ) (hφ : ContDiff ℝ 1 φ) :
        fderiv ℝ (φ ∘ rawModularAction γ) τ v =
          fderiv ℝ φ (γ • τ : UpperHalfPlane)
            ((1 / UpperHalfPlane.denom γ τ ^ 2) * v) :=
      fderiv_comp_rawModularAction γ τ (hφ.differentiable (by simp)).differentiableAt v
    have hchainn (n : ℕ) := hchain (ψn n) (hψn n)
    simp only [hchainn, hchain ψ hψ]
    exact (ContinuousLinearMap.apply ℝ ℂ ((1 / UpperHalfPlane.denom γ τ ^ 2) * v)).continuous.continuousAt.tendsto.comp (hlim (γ • τ : UpperHalfPlane))
  simp only [directional, heqn, heq ψ hψ hψK]
  exact ((tendsto_finsetSum s (fun γ _ => hterm γ)).const_mul _).const_mul _

end GapFamily.Analytic.C1Periodization
