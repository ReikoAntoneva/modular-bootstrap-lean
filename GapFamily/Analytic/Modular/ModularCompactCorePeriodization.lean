import GapFamily.Analytic.Modular.ModularPositivePeriodization
import GapFamily.Analytic.Modular.Periodization.ModularPeriodizationNormalizer
import GapFamily.Analytic.Modular.Periodization.ModularPeriodizationPairing
import GapFamily.Analytic.Modular.Elliptic.ModularInteriorCompactCore

noncomputable section
namespace GapFamily.Analytic
open Set Filter UpperHalfPlane ModularGradient MeasureTheory
open scoped ContDiff MatrixGroups Topology

/-- The normalized compact seed uses the genuine positive orbit sum. -/
def normalizedCompactCoreSeed (χ : ℂ → ℂ) (F : smoothCore) (z : ℂ) : ℂ :=
  normSquareSeed χ z * (F.val z /
    periodizationNormalizer (modularPeriodization (normSquareSeed χ)) z)

/-- The normalized seed's entire topological support stays inside the cutoff support. -/
theorem tsupport_normalizedCompactCoreSeed_subset (χ : ℂ → ℂ) (F : smoothCore) :
    tsupport (normalizedCompactCoreSeed χ F) ⊆ tsupport (normSquareSeed χ) :=
  tsupport_mul_subset_left

/-- Global seed smoothness uses upper-half-plane smoothness only where the compact factor lives. -/
theorem contDiff_normalizedCompactCoreSeed {χ : ℂ → ℂ} (F : smoothCore)
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ upperHalfPlaneSet) :
    ContDiff ℝ ∞ (normalizedCompactCoreSeed χ F) := by
  have hρ := normSquareSeed_contDiff hχ
  have hρc := hasCompactSupport_normSquareSeed hc
  have hρs := (tsupport_normSquareSeed χ).subset.trans hs
  have hP := contDiffOn_modularPeriodization_of_upper_support hρ hρc hρs
  have hD := contDiffOn_periodizationNormalizer hP
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z ∈ tsupport (normSquareSeed χ)
  · have hzU := hρs hz
    have hn := isOpen_upperHalfPlaneSet.mem_nhds hzU
    have hne : periodizationNormalizer (modularPeriodization (normSquareSeed χ)) z ≠ 0 :=
      periodizationNormalizer_ne_zero
        (modularPeriodization_normSquareSeed_re_nonneg χ ⟨z, hzU⟩)
    simpa only [normalizedCompactCoreSeed, div_eq_mul_inv] using!
      hρ.contDiffAt.mul ((F.property.1.contDiffAt hn).mul ((hD.contDiffAt hn).inv hne))
  · apply (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hz] with w hw
    simp only [normalizedCompactCoreSeed, hw, Pi.zero_apply, zero_mul]

/-- Automorphy extracts the entire normalization factor from the genuine orbit sum. -/
theorem modularPeriodization_normalizedCompactCoreSeed (χ : ℂ → ℂ)
    (F : smoothCore) (τ : UpperHalfPlane) :
    modularPeriodization (normalizedCompactCoreSeed χ F) τ =
      modularPeriodization (normSquareSeed χ) τ *
        (F.val τ / periodizationNormalizer (modularPeriodization (normSquareSeed χ)) τ) := by
  simp only [modularPeriodization_coe, normalizedCompactCoreSeed,
    F.property.2.1, periodizationNormalizer_invariant]
  rw [tsum_mul_right]
  ring

/-- A cutoff covering the truncated closed fundamental domain reconstructs the
actual automorphic core on the entire upper half-plane, including every seam. -/
theorem normalizedCompactCoreSeed_periodization_eq (F : smoothCore) (H : ℝ)
    (hzero : ∀ τ : UpperHalfPlane, τ ∈ ModularGroup.fd → H < τ.im → F.val τ = 0)
    {χ : ℂ → ℂ} (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ upperHalfPlaneSet)
    (hone : EqOn χ 1 (modularTruncatedTarget H)) (τ : UpperHalfPlane) :
    modularPeriodization (normalizedCompactCoreSeed χ F) τ = F.val τ := by
  rw [modularPeriodization_normalizedCompactCoreSeed]
  by_cases hF : F.val τ = 0
  · simp [hF]
  · obtain ⟨γ, hγ⟩ := ModularGroup.exists_smul_mem_fd τ
    have hne : F.val (↑(γ • τ) : ℂ) ≠ 0 := by
      rw [F.property.2.1]
      exact hF
    have hheight : (γ • τ : UpperHalfPlane).im ≤ H := by
      by_contra hh
      exact hne (hzero (γ • τ) hγ (lt_of_not_ge hh))
    have hχone : χ (↑(γ • τ) : ℂ) = 1 :=
      hone ((coe_mem_modularTruncatedTarget_iff H (γ • τ)).mpr ⟨hγ, hheight⟩)
    have hbound := modularPeriodization_normSquareSeed_re_ge_half hc hs (γ • τ) hχone
    rw [modularPeriodization_invariant] at hbound
    have hP : modularPeriodization (normSquareSeed χ) τ ≠ 0 := by
      intro hz
      norm_num [hz] at hbound
    rw [periodizationNormalizer_eq hbound]
    field_simp

/-- Every actual smooth core function vanishing above a finite cusp height is
the periodization of one genuine compact smooth upper-half-plane seed. -/
theorem exists_compact_upperSeed_periodization_of_cusp_zero (F : smoothCore) (H : ℝ)
    (hzero : ∀ τ : UpperHalfPlane, τ ∈ ModularGroup.fd → H < τ.im → F.val τ = 0) :
    ∃ ψ : ℂ → ℂ, ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧
      tsupport ψ ⊆ upperHalfPlaneSet ∧
      ∀ τ : UpperHalfPlane, modularPeriodization ψ τ = F.val τ := by
  obtain ⟨χ, hχ, hc, hs, hone⟩ := exists_upperCutoff_eq_one
    (isCompact_modularTruncatedTarget H) (modularTruncatedTarget_subset_upperHalfPlane H)
  refine ⟨normalizedCompactCoreSeed χ F, contDiff_normalizedCompactCoreSeed F hχ hc hs,
    (hasCompactSupport_normSquareSeed hc).mul_right, ?_, ?_⟩
  · exact (tsupport_normalizedCompactCoreSeed_subset χ F).trans
      ((tsupport_normSquareSeed χ).subset.trans hs)
  · exact normalizedCompactCoreSeed_periodization_eq F H hzero hc hs hone

/-- The reconstructed seed represents exactly the original completed core-form vector. -/
theorem exists_periodizedUpperCore_coreForm_eq_of_cusp_zero (F : smoothCore) (H : ℝ)
    (hzero : ∀ τ : UpperHalfPlane, τ ∈ ModularGroup.fd → H < τ.im → F.val τ = 0) :
    ∃ (ψ : ℂ → ℂ) (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
      (hs : tsupport ψ ⊆ upperHalfPlaneSet),
      coreForm (periodizedUpperCore ψ hψ hc hs) = coreForm F := by
  obtain ⟨ψ, hψ, hc, hs, heq⟩ := exists_compact_upperSeed_periodization_of_cusp_zero F H hzero
  refine ⟨ψ, hψ, hc, hs, ?_⟩
  apply formEmbedding_injective
  change value (periodizedUpperCore ψ hψ hc hs) = value F
  apply Lp.ext
  filter_upwards [value_ae (periodizedUpperCore ψ hψ hc hs), value_ae F] with τ hP hF
  rw [hP, hF]
  exact heq τ

end GapFamily.Analytic
