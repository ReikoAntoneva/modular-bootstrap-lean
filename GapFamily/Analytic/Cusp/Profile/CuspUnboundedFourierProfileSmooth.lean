import GapFamily.Analytic.Cusp.Fourier.CuspFourierProfileCore
import GapFamily.Analytic.Modular.Periodization.ModularPeriodizationUpper

/-!
Local smoothness of the actual periodized integer Fourier cusp profile.
The vertical profile may have noncompact support.
-/

noncomputable section
namespace GapFamily.Analytic.CuspFourierUnbounded

open Set Filter UpperHalfPlane ModularGradient
open scoped ContDiff MatrixGroups Topology ComplexOrder

/-- Horizontal compact support and the uniform orbit-height bound on each
compact neighborhood reduce the actual Fourier seed to a compact seed locally.
No compact-support assumption on the vertical profile is required. -/
theorem contDiffOn_modularPeriodization_cuspFourierProfileSeed (J : ℤ) {b : ℝ → ℂ}
    (hb : ContDiff ℝ ∞ b) (hs : tsupport b ⊆ Ioi (1 : ℝ)) :
    ContDiffOn ℝ ∞ (modularPeriodization (cuspFourierProfileSeed J b))
      upperHalfPlaneSet := by
  intro z hz
  let τ : UpperHalfPlane := ⟨z, hz⟩
  obtain ⟨K, hK, hKτ⟩ := exists_compact_mem_nhds τ
  obtain ⟨H, hH⟩ := exists_bound_modular_smul_im_of_isCompact hK
  let D : Set ℂ := (Icc (-1 / 2 : ℝ) (3 / 2)) ×ℂ Icc (1 : ℝ) H
  have hD : IsCompact D := isCompact_Icc.reProdIm isCompact_Icc
  have hDU : D ⊆ upperHalfPlaneSet := by
    intro w hw
    exact lt_of_lt_of_le zero_lt_one hw.2.1
  obtain ⟨χ, hχ, hcχ, hsχ, hχone⟩ := exists_upperCutoff_eq_one hD hDU
  let φ : ℂ → ℂ := fun w => χ w * cuspFourierProfileSeed J b w
  have hφ : ContDiff ℝ ∞ φ := hχ.mul (contDiff_cuspFourierProfileSeed J hb)
  have hcφ : HasCompactSupport φ := hcχ.mul_right
  have hsφ : tsupport φ ⊆ upperHalfPlaneSet := tsupport_mul_subset_left.trans hsχ
  have heqK (σ : UpperHalfPlane) (hσ : σ ∈ K) :
      modularPeriodization (cuspFourierProfileSeed J b) σ =
        modularPeriodization φ σ := by
    simp only [modularPeriodization_coe]
    congr 1
    apply tsum_congr
    intro γ
    by_cases hseed : cuspFourierProfileSeed J b (↑(γ • σ : UpperHalfPlane) : ℂ) = 0
    · simp only [φ, hseed, mul_zero]
    · have hbase : cuspProfileSeed b (↑(γ • σ : UpperHalfPlane) : ℂ) ≠ 0 := by
        intro h
        exact hseed (by simp only [cuspFourierProfileSeed, h, zero_mul])
      have hmul : (cuspTranslationWeight (γ • σ : UpperHalfPlane).re : ℂ) *
          b (γ • σ : UpperHalfPlane).im ≠ 0 := hbase
      have hp := mul_ne_zero_iff.mp hmul
      have hx : (γ • σ : UpperHalfPlane).re ∈ Icc (-1 / 2 : ℝ) (3 / 2) := by
        apply cuspTranslationWeight_tsupport_subset
        apply subset_tsupport cuspTranslationWeight
        exact fun h => hp.1 (by simp only [h, Complex.ofReal_zero])
      have hy : 1 < (γ • σ : UpperHalfPlane).im := hs (subset_tsupport b hp.2)
      have hmem : (↑(γ • σ : UpperHalfPlane) : ℂ) ∈ D := ⟨hx, hy.le, hH σ hσ γ⟩
      simp only [φ, hχone hmem, Pi.one_apply, one_mul]
  obtain ⟨V, hVK, hVopen, hVτ⟩ := mem_nhds_iff.mp hKτ
  have hW : UpperHalfPlane.coe '' V ∈ 𝓝 z :=
    (UpperHalfPlane.isOpenEmbedding_coe.isOpenMap V hVopen).mem_nhds ⟨τ, hVτ, rfl⟩
  have heq : modularPeriodization (cuspFourierProfileSeed J b) =ᶠ[𝓝 z]
      modularPeriodization φ := by
    filter_upwards [hW] with w hw
    obtain ⟨σ, hσ, rfl⟩ := hw
    exact heqK σ (hVK hσ)
  exact ((contDiffOn_modularPeriodization_of_upper_support hφ hcφ hsφ z hz).contDiffAt
    (isOpen_upperHalfPlaneSet.mem_nhds hz)).congr_of_eventuallyEq heq |>.contDiffWithinAt

end GapFamily.Analytic.CuspFourierUnbounded
