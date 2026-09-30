import GapFamily.Analytic.Modular.Periodization.ModularPeriodization
import GapFamily.Analytic.Modular.Geometry.ModularSeamCover
import GapFamily.Analytic.Modular.Geometry.ModularTruncatedCutoff
import GapFamily.Analytic.Modular.Geometry.ModularTruncatedTransportBasic
import GapFamily.Analytic.Modular.Periodization.ModularPeriodizationDensity

/-! Smooth periodization of compact seeds supported anywhere in the upper half-plane. -/
noncomputable section
namespace GapFamily.Analytic
open Set Filter UpperHalfPlane
open scoped ContDiff MatrixGroups Topology

theorem compact_modular_support_preimage_of_upper_support {φ : ℂ → ℂ}
    (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ upperHalfPlaneSet) :
    IsCompact (UpperHalfPlane.coe ⁻¹' tsupport φ) := by
  apply UpperHalfPlane.isEmbedding_coe.isCompact_iff.mpr
  rw [Set.image_preimage_eq_inter_range, UpperHalfPlane.range_coe,
    Set.inter_eq_left.mpr hs]
  exact hc

theorem locallyFinite_modular_orbit_support_of_upper_support {φ : ℂ → ℂ}
    (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ upperHalfPlaneSet) :
    LocallyFinite (fun γ : SL(2, ℤ) =>
      Function.support (fun τ : UpperHalfPlane => φ (↑(γ • τ : UpperHalfPlane) : ℂ))) := by
  apply (locallyFinite_modular_preimage
    (compact_modular_support_preimage_of_upper_support hc hs)).subset
  intro γ τ hτ
  exact subset_tsupport _ hτ

theorem modularPeriodization_eventually_finset_of_upper_support {φ : ℂ → ℂ}
    (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ upperHalfPlaneSet)
    {z : ℂ} (hz : z ∈ upperHalfPlaneSet) :
    ∃ s : Finset SL(2, ℤ), modularPeriodization φ =ᶠ[𝓝 z]
      fun w => (1 / 2 : ℂ) * ∑ γ ∈ s, φ (rawModularAction γ w) := by
  classical
  let τ : UpperHalfPlane := ⟨z, hz⟩
  obtain ⟨s, hsfin⟩ :=
    (locallyFinite_modular_orbit_support_of_upper_support hc hs).exists_finset_support τ
  obtain ⟨V, hVsub, hVopen, hVτ⟩ := mem_nhds_iff.mp hsfin
  refine ⟨s, ?_⟩
  have hW : UpperHalfPlane.coe '' V ∈ 𝓝 z :=
    (UpperHalfPlane.isOpenEmbedding_coe.isOpenMap V hVopen).mem_nhds ⟨τ, hVτ, rfl⟩
  filter_upwards [hW] with w hw
  obtain ⟨τ', hτ', rfl⟩ := hw
  simp only [modularPeriodization, rawModularAction_coe]
  congr 1
  apply tsum_eq_sum
  intro γ hγ
  by_contra hne
  exact hγ (hVsub hτ' hne)

theorem contDiffOn_modularPeriodization_of_upper_support {φ : ℂ → ℂ}
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ upperHalfPlaneSet) :
    ContDiffOn ℝ ∞ (modularPeriodization φ) upperHalfPlaneSet := by
  intro z hz
  obtain ⟨s, heq⟩ := modularPeriodization_eventually_finset_of_upper_support hc hs hz
  have hsum : ContDiffOn ℝ ∞
      (fun w => (1 / 2 : ℂ) * ∑ γ ∈ s, φ (rawModularAction γ w)) upperHalfPlaneSet :=
    contDiffOn_const.mul (ContDiffOn.sum fun γ _ =>
      hφ.contDiffOn.comp (contDiffOn_rawModularAction γ)
        (fun _ _ => Set.mem_univ _))
  exact ((hsum z hz).contDiffAt (isOpen_upperHalfPlaneSet.mem_nhds hz)).congr_of_eventuallyEq
    heq |>.contDiffWithinAt


/-- A compact seed has one uniform height bound on its entire modular orbit. -/
theorem modularPeriodization_exists_cusp_zero_of_upper_support {φ : ℂ → ℂ}
    (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ upperHalfPlaneSet) :
    ∃ H : ℝ, ∀ τ : UpperHalfPlane, H < τ.im → modularPeriodization φ τ = 0 := by
  obtain ⟨H, hH⟩ := exists_bound_modular_smul_im_of_isCompact
    (compact_modular_support_preimage_of_upper_support hc hs)
  refine ⟨H, fun τ hτ => ?_⟩
  have hz : ∀ γ : SL(2, ℤ), φ (↑(γ • τ : UpperHalfPlane) : ℂ) = 0 := by
    intro γ
    by_contra hne
    have hbound := hH (γ • τ) (subset_tsupport φ hne) γ⁻¹
    simp only [inv_smul_smul] at hbound
    exact (not_le_of_gt hτ) hbound
  simp only [modularPeriodization_coe, hz, tsum_zero, mul_zero]

open MeasureTheory ModularGradient in
/-- Compact smooth upper-half-plane seeds give actual smooth-core elements,
including seeds crossing the fundamental-domain seams. -/
theorem modularPeriodization_mem_smoothCore_of_upper_support {φ : ℂ → ℂ}
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ upperHalfPlaneSet) : modularPeriodization φ ∈ smoothCore := by
  have hF := contDiffOn_modularPeriodization_of_upper_support hφ hc hs
  obtain ⟨H, hH⟩ := modularPeriodization_exists_cusp_zero_of_upper_support hc hs
  obtain ⟨χ, hχ, hχc, hχs, hχone⟩ := exists_upperCutoff_eq_one
    (isCompact_modularTruncatedTarget H) (modularTruncatedTarget_subset_upperHalfPlane H)
  let g : ℂ → ℂ := fun z => χ z * modularPeriodization φ z
  have hg : ContDiff ℝ ∞ g := by
    rw [contDiff_iff_contDiffAt]
    intro z
    by_cases hz : z ∈ tsupport χ
    · exact hχ.contDiffAt.mul (hF.contDiffAt
        (isOpen_upperHalfPlaneSet.mem_nhds (hχs hz)))
    · apply (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hz] with w hw
      simp [g, hw]
  have hgc : HasCompactSupport g := hχc.mul_right
  have hae : (fun τ : UpperHalfPlane => modularPeriodization φ τ) =ᵐ[modularMeasure]
      (fun τ : UpperHalfPlane => g τ) := by
    filter_upwards [ae_mem_fdo] with τ hτ
    by_cases hh : τ.im ≤ H
    · have hone : χ τ = 1 := hχone ((coe_mem_modularTruncatedTarget_iff H τ).mpr
        ⟨ModularGroup.fdo_subset_fd hτ, hh⟩)
      simp only [g, hone, one_mul]
    · simp only [g, hH τ (lt_of_not_ge hh), mul_zero]
  have hdir (v : ℂ) : directional (modularPeriodization φ) v =ᵐ[modularMeasure]
      directional g v := modularDirectional_ae_eq
    (hF.continuousOn.mono (fun _ hz => im_pos_of_mem_modularInterior hz))
    hg.continuous.continuousOn hae v
  refine ⟨hF, modularPeriodization_invariant φ, ?_, ?_, ?_⟩
  · exact (memLp_congr_ae hae).mpr (memLp_test_value g hg.continuous hgc)
  · exact (memLp_congr_ae (hdir 1)).mpr (memLp_test_directional g hg hgc 1)
  · exact (memLp_congr_ae (hdir Complex.I)).mpr
      (memLp_test_directional g hg hgc Complex.I)


end GapFamily.Analytic
