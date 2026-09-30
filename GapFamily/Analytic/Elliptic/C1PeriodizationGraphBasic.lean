import GapFamily.Analytic.Modular.Periodization.ModularPeriodizationGradientSum

noncomputable section
namespace GapFamily.Analytic.C1Periodization
open Set Filter MeasureTheory UpperHalfPlane ModularGradient
open scoped ContDiff MatrixGroups Topology ComplexConjugate

theorem contDiffOn_periodization {φ : ℂ → ℂ}
    (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ upperHalfPlaneSet) :
    ContDiffOn ℝ 1 (modularPeriodization φ) upperHalfPlaneSet := by
  intro z hz
  obtain ⟨s, heq⟩ := modularPeriodization_eventually_finset_of_upper_support hc hs hz
  have hsum : ContDiffOn ℝ 1
      (fun w => (1 / 2 : ℂ) * ∑ γ ∈ s, φ (rawModularAction γ w)) upperHalfPlaneSet :=
    contDiffOn_const.mul (ContDiffOn.sum fun γ _ =>
      hφ.contDiffOn.comp ((contDiffOn_rawModularAction γ).of_le (by simp))
        (fun _ _ => Set.mem_univ _))
  exact ((hsum z hz).contDiffAt (isOpen_upperHalfPlaneSet.mem_nhds hz)).congr_of_eventuallyEq
    heq |>.contDiffWithinAt

theorem exists_finset_fderiv_periodization {ψ : ℂ → ℂ}
    (hψ : ContDiff ℝ 1 ψ) (hc : HasCompactSupport ψ)
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


/-- A common compact support admits a finite orbit neighborhood independently
of any particular function or regularity. -/
theorem exists_finset_avoid_compact {K : Set ℂ} (hK : IsCompact K)
    (hKH : K ⊆ upperHalfPlaneSet) (τ : UpperHalfPlane) :
    ∃ s : Finset SL(2, ℤ), ∀ᶠ z in 𝓝 (τ : ℂ),
      ∀ γ ∉ s, rawModularAction γ z ∉ K := by
  classical
  have hKU : IsCompact (UpperHalfPlane.coe ⁻¹' K) := by
    apply UpperHalfPlane.isEmbedding_coe.isCompact_iff.mpr
    rw [Set.image_preimage_eq_inter_range, UpperHalfPlane.range_coe,
      Set.inter_eq_left.mpr hKH]
    exact hK
  obtain ⟨V, hV, hfin⟩ := locallyFinite_modular_preimage hKU τ
  obtain ⟨W, hWV, hWopen, hWτ⟩ := mem_nhds_iff.mp hV
  refine ⟨hfin.toFinset, ?_⟩
  have hW : UpperHalfPlane.coe '' W ∈ 𝓝 (τ : ℂ) :=
    (UpperHalfPlane.isOpenEmbedding_coe.isOpenMap W hWopen).mem_nhds ⟨τ, hWτ, rfl⟩
  filter_upwards [hW] with z hz
  obtain ⟨τ', hτ', rfl⟩ := hz
  intro γ hγ hγK
  apply hγ
  apply hfin.mem_toFinset.mpr
  refine ⟨τ', ?_, hWV hτ'⟩
  change (↑(γ • τ' : UpperHalfPlane) : ℂ) ∈ K
  simpa only [rawModularAction_coe] using hγK

/-- One finite sum and one neighborhood work simultaneously for every seed
whose support lies in a fixed compact upper-half-plane set. -/
theorem exists_finset_common_support_germ {K : Set ℂ} (hK : IsCompact K)
    (hKH : K ⊆ upperHalfPlaneSet) (τ : UpperHalfPlane) :
    ∃ s : Finset SL(2, ℤ), ∀ᶠ z in 𝓝 (τ : ℂ),
      ∀ ψ : ℂ → ℂ, tsupport ψ ⊆ K →
        modularPeriodization ψ z =
          (1 / 2 : ℂ) * ∑ γ ∈ s, ψ (rawModularAction γ z) ∧
        ∀ γ ∉ s, ψ (rawModularAction γ z) = 0 := by
  obtain ⟨s, hs⟩ := exists_finset_avoid_compact hK hKH τ
  refine ⟨s, hs.mono ?_⟩
  intro z hz ψ hψ
  have hout (γ : SL(2, ℤ)) (hγ : γ ∉ s) : ψ (rawModularAction γ z) = 0 := by
    by_contra hne
    exact hz γ hγ (hψ (subset_tsupport ψ hne))
  refine ⟨?_, hout⟩
  unfold modularPeriodization
  congr 1
  exact tsum_eq_sum hout


/-- The same finite derivative sum works for every C1 seed supported in the
common compact set, and all excluded derivative germs vanish. -/
theorem exists_finset_common_support_fderiv {K : Set ℂ} (hK : IsCompact K)
    (hKH : K ⊆ upperHalfPlaneSet) (τ : UpperHalfPlane) :
    ∃ s : Finset SL(2, ℤ), ∀ ψ : ℂ → ℂ,
      ContDiff ℝ 1 ψ → tsupport ψ ⊆ K →
        (∀ v : ℂ, fderiv ℝ (modularPeriodization ψ) τ v =
          (1 / 2 : ℂ) * ∑ γ ∈ s, fderiv ℝ (ψ ∘ rawModularAction γ) τ v) ∧
        (∀ γ ∉ s, fderiv ℝ (ψ ∘ rawModularAction γ) τ = 0) := by
  classical
  obtain ⟨s, hgerm⟩ := exists_finset_common_support_germ hK hKH τ
  refine ⟨s, ?_⟩
  intro ψ hψ hψK
  have heq : modularPeriodization ψ =ᶠ[𝓝 (τ : ℂ)]
      fun z => (1 / 2 : ℂ) * ∑ γ ∈ s, ψ (rawModularAction γ z) :=
    hgerm.mono (fun z hz => (hz ψ hψK).1)
  have hterm (γ : SL(2, ℤ)) : DifferentiableAt ℝ (ψ ∘ rawModularAction γ) τ :=
    (hψ.differentiable (by simp)).differentiableAt.comp (τ : ℂ)
      (hasFDerivAt_rawModularAction γ τ).differentiableAt
  refine ⟨?_, ?_⟩
  · intro v
    rw [heq.fderiv_eq]
    have hsum := (HasFDerivAt.fun_sum (u := s)
      (fun γ _ => (hterm γ).hasFDerivAt)).const_mul (1 / 2 : ℂ)
    simpa only [Function.comp_def, smul_apply, sum_apply, smul_eq_mul] using
      congrArg (fun L : ℂ →L[ℝ] ℂ => L v) hsum.fderiv
  · intro γ hγ
    have hout : (ψ ∘ rawModularAction γ) =ᶠ[𝓝 (τ : ℂ)] fun _ => (0 : ℂ) :=
      hgerm.mono (fun z hz => (hz ψ hψK).2 γ hγ)
    simpa only [fderiv_const_apply] using hout.fderiv_eq (𝕜 := ℝ)

end GapFamily.Analytic.C1Periodization
