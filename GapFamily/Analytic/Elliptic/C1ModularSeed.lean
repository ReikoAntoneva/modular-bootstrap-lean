import GapFamily.Analytic.Modular.ModularCompactCorePeriodization

noncomputable section
namespace GapFamily.Analytic.C1ModularForm
open Set Filter UpperHalfPlane MeasureTheory ModularGradient
open scoped ContDiff MatrixGroups Topology

/-- The same actual positive-orbit normalization, now applied to a C1 field. -/
def normalizedC1Seed (χ F : ℂ → ℂ) (z : ℂ) : ℂ :=
  normSquareSeed χ z * (F z / periodizationNormalizer (modularPeriodization (normSquareSeed χ)) z)

theorem contDiff_normalizedC1Seed {χ F : ℂ → ℂ}
    (hF : ContDiffOn ℝ 1 F upperHalfPlaneSet)
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ upperHalfPlaneSet) : ContDiff ℝ 1 (normalizedC1Seed χ F) := by
  have hρ := normSquareSeed_contDiff hχ
  have hρc := hasCompactSupport_normSquareSeed hc
  have hρs := (tsupport_normSquareSeed χ).subset.trans hs
  have hP := contDiffOn_modularPeriodization_of_upper_support hρ hρc hρs
  have hD := contDiffOn_periodizationNormalizer hP
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z ∈ tsupport (normSquareSeed χ)
  · have hn := isOpen_upperHalfPlaneSet.mem_nhds (hρs hz)
    have hne := periodizationNormalizer_ne_zero
      (modularPeriodization_normSquareSeed_re_nonneg χ ⟨z, hρs hz⟩)
    simpa only [normalizedC1Seed, div_eq_mul_inv] using!
      (hρ.of_le (by simp)).contDiffAt.mul ((hF.contDiffAt hn).mul
        (((hD.of_le (by simp)).contDiffAt hn).inv hne))
  · apply (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hz] with w hw
    simp only [normalizedC1Seed, hw, Pi.zero_apply, zero_mul]

theorem modularPeriodization_normalizedC1Seed (χ F : ℂ → ℂ)
    (hinv : ∀ γ : SL(2, ℤ), ∀ τ : UpperHalfPlane, F (γ • τ : UpperHalfPlane) = F τ)
    (τ : UpperHalfPlane) :
    modularPeriodization (normalizedC1Seed χ F) τ =
      modularPeriodization (normSquareSeed χ) τ *
        (F τ / periodizationNormalizer (modularPeriodization (normSquareSeed χ)) τ) := by
  simp only [modularPeriodization_coe, normalizedC1Seed, hinv, periodizationNormalizer_invariant]
  rw [tsum_mul_right]
  ring

theorem normalizedC1Seed_periodization_eq (F : ℂ → ℂ)
    (hinv : ∀ γ : SL(2, ℤ), ∀ τ : UpperHalfPlane, F (γ • τ : UpperHalfPlane) = F τ)
    (H : ℝ) (hzero : ∀ τ : UpperHalfPlane, τ ∈ ModularGroup.fd → H < τ.im → F τ = 0)
    {χ : ℂ → ℂ} (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ upperHalfPlaneSet)
    (hone : EqOn χ 1 (modularTruncatedTarget H)) (τ : UpperHalfPlane) :
    modularPeriodization (normalizedC1Seed χ F) τ = F τ := by
  rw [modularPeriodization_normalizedC1Seed χ F hinv]
  by_cases hF : F τ = 0
  · simp [hF]
  · obtain ⟨γ, hγ⟩ := ModularGroup.exists_smul_mem_fd τ
    have hne : F (γ • τ : UpperHalfPlane) ≠ 0 := by rw [hinv]; exact hF
    have hheight : (γ • τ : UpperHalfPlane).im ≤ H := by
      by_contra hh
      exact hne (hzero (γ • τ) hγ (lt_of_not_ge hh))
    have hχone : χ (γ • τ : UpperHalfPlane) = 1 :=
      hone ((coe_mem_modularTruncatedTarget_iff H (γ • τ)).mpr ⟨hγ, hheight⟩)
    have hbound := modularPeriodization_normSquareSeed_re_ge_half hc hs (γ • τ) hχone
    rw [modularPeriodization_invariant] at hbound
    have hP : modularPeriodization (normSquareSeed χ) τ ≠ 0 := by
      intro hz
      norm_num [hz] at hbound
    rw [periodizationNormalizer_eq hbound]
    field_simp

/-- Every finite-height modular C1 field is reconstructed by a genuine compact C1 upper seed. -/
theorem exists_compact_upper_C1_seed (F : ℂ → ℂ)
    (hF : ContDiffOn ℝ 1 F upperHalfPlaneSet)
    (hinv : ∀ γ : SL(2, ℤ), ∀ τ : UpperHalfPlane, F (γ • τ : UpperHalfPlane) = F τ)
    (H : ℝ) (hzero : ∀ τ : UpperHalfPlane, τ ∈ ModularGroup.fd → H < τ.im → F τ = 0) :
    ∃ ψ : ℂ → ℂ, ContDiff ℝ 1 ψ ∧ HasCompactSupport ψ ∧ tsupport ψ ⊆ upperHalfPlaneSet ∧
      ∀ τ : UpperHalfPlane, modularPeriodization ψ τ = F τ := by
  obtain ⟨χ, hχ, hc, hs, hone⟩ := exists_upperCutoff_eq_one
    (isCompact_modularTruncatedTarget H) (modularTruncatedTarget_subset_upperHalfPlane H)
  refine ⟨normalizedC1Seed χ F, contDiff_normalizedC1Seed hF hχ hc hs,
    (hasCompactSupport_normSquareSeed hc).mul_right, ?_, ?_⟩
  · exact tsupport_mul_subset_left.trans ((tsupport_normSquareSeed χ).subset.trans hs)
  · exact normalizedC1Seed_periodization_eq F hinv H hzero hc hs hone

end GapFamily.Analytic.C1ModularForm
