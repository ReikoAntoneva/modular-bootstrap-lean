import GapFamily.Analytic.Modular.Periodization.ModularPeriodizationPairing
import GapFamily.Analytic.Modular.ModularMixedGradientCovariance

/-!
# Actual mixed gradient periodization at each upper-half-plane point

The orbit family is locally finite near the observation point. Thus its
actual derivative reduces to a finite sum, including the vanishing derivative
germs outside that sum, before mixed conformal covariance is applied.
-/

noncomputable section
namespace GapFamily.Analytic
open Set Filter MeasureTheory UpperHalfPlane ModularGradient
open scoped ContDiff MatrixGroups Topology ComplexConjugate

/-- A genuine finite derivative germ, with all excluded derivative germs zero. -/
theorem exists_finset_fderiv_modularPeriodization {ψ : ℂ → ℂ}
    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    (hs : tsupport ψ ⊆ upperHalfPlaneSet) (τ : UpperHalfPlane) :
    ∃ s : Finset SL(2, ℤ),
      (∀ v : ℂ, fderiv ℝ (modularPeriodization ψ) τ v =
        (1 / 2 : ℂ) * ∑ γ ∈ s, fderiv ℝ (ψ ∘ rawModularAction γ) τ v) ∧
      (∀ γ ∉ s, fderiv ℝ (ψ ∘ rawModularAction γ) τ = 0) := by
  classical
  obtain ⟨s, hsfin⟩ :=
    (locallyFinite_modular_orbit_support_of_upper_support hc hs).exists_finset_support τ
  obtain ⟨V, hVsub, hVopen, hVτ⟩ := mem_nhds_iff.mp hsfin
  have hW : UpperHalfPlane.coe '' V ∈ 𝓝 (τ : ℂ) :=
    (UpperHalfPlane.isOpenEmbedding_coe.isOpenMap V hVopen).mem_nhds ⟨τ, hVτ, rfl⟩
  have hout (γ : SL(2, ℤ)) (hγ : γ ∉ s) :
      (ψ ∘ rawModularAction γ) =ᶠ[𝓝 (τ : ℂ)] fun _ => (0 : ℂ) := by
    filter_upwards [hW] with w hw
    obtain ⟨τ', hτ', rfl⟩ := hw
    change ψ (rawModularAction γ (τ' : ℂ)) = 0
    rw [rawModularAction_coe]
    by_contra hne
    exact hγ (hVsub hτ' hne)
  have heq : modularPeriodization ψ =ᶠ[𝓝 (τ : ℂ)]
      fun w => (1 / 2 : ℂ) * ∑ γ ∈ s, ψ (rawModularAction γ w) := by
    filter_upwards [hW] with w hw
    obtain ⟨τ', hτ', rfl⟩ := hw
    simp only [modularPeriodization, rawModularAction_coe]
    congr 1
    apply tsum_eq_sum
    intro γ hγ
    by_contra hne
    exact hγ (hVsub hτ' hne)
  have hterm (γ : SL(2, ℤ)) : DifferentiableAt ℝ (ψ ∘ rawModularAction γ) τ :=
    (hψ.differentiable (by simp)).differentiableAt.comp (τ : ℂ)
      (hasFDerivAt_rawModularAction γ τ).differentiableAt
  refine ⟨s, ?_, ?_⟩
  · intro v
    rw [heq.fderiv_eq]
    have hsum := (HasFDerivAt.fun_sum (u := s)
      (fun γ _ => (hterm γ).hasFDerivAt)).const_mul (1 / 2 : ℂ)
    simpa only [Function.comp_def, smul_apply,
      sum_apply, smul_eq_mul] using
      congrArg (fun L : ℂ →L[ℝ] ℂ => L v) hsum.fderiv
  · intro γ hγ
    simpa only [fderiv_const_apply] using (hout γ hγ).fderiv_eq (𝕜 := ℝ)

private theorem directionalMixedGradient_modularPeriodization_of_finset
    (F : smoothCore) {ψ : ℂ → ℂ} (hψ : ContDiff ℝ ∞ ψ) (τ : UpperHalfPlane)
    (s : Finset SL(2, ℤ))
    (hd : ∀ v : ℂ, fderiv ℝ (modularPeriodization ψ) τ v =
      (1 / 2 : ℂ) * ∑ γ ∈ s, fderiv ℝ (ψ ∘ rawModularAction γ) τ v)
    (hzero : ∀ γ ∉ s, fderiv ℝ (ψ ∘ rawModularAction γ) τ = 0) :
    conj (directional F.val 1 τ) * directional (modularPeriodization ψ) 1 τ +
      conj (directional F.val Complex.I τ) * directional (modularPeriodization ψ) Complex.I τ =
      (1 / 2 : ℂ) * ∑' γ : SL(2, ℤ),
        (conj (directional F.val 1 (γ • τ)) * directional ψ 1 (γ • τ) +
          conj (directional F.val Complex.I (γ • τ)) * directional ψ Complex.I (γ • τ)) := by
  classical
  have hdir (v : ℂ) : directional (modularPeriodization ψ) v τ =
      (1 / 2 : ℂ) * ∑ γ ∈ s, directional (ψ ∘ rawModularAction γ) v τ := by
    simp only [directional, hd]
    rw [← Finset.mul_sum]
    ring
  have hcov (γ : SL(2, ℤ)) := directionalMixedGradient_modularAction F γ τ
    ((hψ.differentiable (by simp)) (γ • τ : UpperHalfPlane))
  rw [hdir 1, hdir Complex.I]
  calc
    _ = (1 / 2 : ℂ) * ∑ γ ∈ s,
        (conj (directional F.val 1 τ) * directional (ψ ∘ rawModularAction γ) 1 τ +
          conj (directional F.val Complex.I τ) *
            directional (ψ ∘ rawModularAction γ) Complex.I τ) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      ring
    _ = (1 / 2 : ℂ) * ∑ γ ∈ s,
        (conj (directional F.val 1 (γ • τ)) * directional ψ 1 (γ • τ) +
          conj (directional F.val Complex.I (γ • τ)) * directional ψ Complex.I (γ • τ)) := by
      congr 1
      exact Finset.sum_congr rfl fun γ _ => hcov γ
    _ = _ := by
      congr 1
      symm
      apply tsum_eq_sum
      intro γ hγ
      rw [← hcov γ]
      simp only [directional, hzero γ hγ, zero_apply, mul_zero, add_zero]

/-- At every upper-half-plane point the actual mixed gradient of the
half-normalized periodization is its translated mixed-gradient orbit sum. -/
theorem directionalMixedGradient_modularPeriodization (F : smoothCore) {ψ : ℂ → ℂ}
    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    (hs : tsupport ψ ⊆ upperHalfPlaneSet) (τ : UpperHalfPlane) :
    conj (directional F.val 1 τ) * directional (modularPeriodization ψ) 1 τ +
      conj (directional F.val Complex.I τ) * directional (modularPeriodization ψ) Complex.I τ =
      (1 / 2 : ℂ) * ∑' γ : SL(2, ℤ),
        (conj (directional F.val 1 (γ • τ)) * directional ψ 1 (γ • τ) +
          conj (directional F.val Complex.I (γ • τ)) * directional ψ Complex.I (γ • τ)) := by
  obtain ⟨s, hd, hzero⟩ := exists_finset_fderiv_modularPeriodization hψ hc hs τ
  exact directionalMixedGradient_modularPeriodization_of_finset F hψ τ s hd hzero

end GapFamily.Analytic
