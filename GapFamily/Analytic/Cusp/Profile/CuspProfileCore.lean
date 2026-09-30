import GapFamily.Analytic.Modular.Periodization.ModularPeriodizationUpper
import GapFamily.Analytic.Cusp.Profile.CuspProfileSeed
import GapFamily.Analytic.Modular.Geometry.ModularParabolicTranslation
import GapFamily.Analytic.Cusp.CuspOrbitHeight

/-!
# Actual compact scalar profiles in the modular smooth core

The full SL₂(ℤ) periodization recovers a compact vertical profile on the entire
closed fundamental domain, including its seams. Its actual value and gradient
classes satisfy the literal profile and derivative formulas.
-/

namespace GapFamily.Analytic
open Set UpperHalfPlane ModularGroup
open scoped MatrixGroups

/-- Exact full-group sum for a seed with no nonparabolic contribution. -/
theorem modularPeriodization_cuspProfileSeed_of_zero_nonparabolic (b : ℝ → ℂ)
    (τ : UpperHalfPlane) (hτ : τ.re ∈ Icc (-1/2 : ℝ) (1/2))
    (hz : ∀ γ : SL(2, ℤ), γ 1 0 ≠ 0 → b (γ • τ).im = 0) :
    modularPeriodization (cuspProfileSeed b) τ = b τ.im := by
  classical
  have h1 : (1 : SL(2, ℤ)) ≠ -1 := by decide
  have h2 : (1 : SL(2, ℤ)) ≠ T := by decide
  have h3 : (1 : SL(2, ℤ)) ≠ -T := by decide
  have h4 : (-1 : SL(2, ℤ)) ≠ T := by decide
  have h5 : (-1 : SL(2, ℤ)) ≠ -T := by decide
  have h6 : (T : SL(2, ℤ)) ≠ -T := by decide
  have hzero : ∀ γ : SL(2, ℤ), γ ∉ ({1, -1, T, -T} : Finset SL(2, ℤ)) →
      cuspProfileSeed b (↑(γ • τ : UpperHalfPlane) : ℂ) = 0 := by
    intro γ hγ
    by_cases hc : γ 1 0 = 0
    · obtain ⟨n, hn | hn⟩ := parabolic_eq_T_zpow_or_neg hc
      · subst γ
        have hn0 : n ≠ 0 := by
          intro h; subst n; exact hγ (by simp)
        have hn1 : n ≠ 1 := by
          intro h; subst n; exact hγ (by simp)
        simp only [cuspProfileSeed, UpperHalfPlane.coe_re, re_T_zpow_smul,
          cuspTranslationWeight_translate_zero hτ hn0 hn1, Complex.ofReal_zero, zero_mul]
      · subst γ
        have hn0 : n ≠ 0 := by
          intro h; subst n; exact hγ (by simp)
        have hn1 : n ≠ 1 := by
          intro h; subst n; exact hγ (by simp)
        simp only [SL_neg_smul, cuspProfileSeed, UpperHalfPlane.coe_re, re_T_zpow_smul,
          cuspTranslationWeight_translate_zero hτ hn0 hn1, Complex.ofReal_zero, zero_mul]
    · simp only [cuspProfileSeed, UpperHalfPlane.coe_im, hz γ hc, mul_zero]
  rw [modularPeriodization_coe, tsum_eq_sum (s := {1, -1, T, -T}) hzero]
  have hpart : cuspProfileSeed b (τ : ℂ) +
      cuspProfileSeed b (↑(T • τ : UpperHalfPlane) : ℂ) = b τ.im := by
    simpa only [modular_T_smul, UpperHalfPlane.coe_vadd, Int.cast_one,
      Complex.ofReal_one, UpperHalfPlane.coe_im, add_comm]
      using cuspProfileSeed_partition b hτ
  simp only [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton,
    h1, h2, h3, h4, h5, h6, not_false_eq_true, or_self, Finset.sum_singleton,
    one_smul, SL_neg_smul]
  linear_combination hpart

end GapFamily.Analytic

noncomputable section
namespace GapFamily.Analytic
open Set UpperHalfPlane ModularGroup MeasureTheory ModularGradient
open scoped MatrixGroups ContDiff

/-- Compact profiles above height one are recovered exactly on the closed domain. -/
theorem modularPeriodization_cuspProfileSeed_eq_on_fd {b : ℝ → ℂ}
    (hs : tsupport b ⊆ Ioi (1 : ℝ)) {τ : UpperHalfPlane} (hτ : τ ∈ fd) :
    modularPeriodization (cuspProfileSeed b) τ = b τ.im := by
  apply modularPeriodization_cuspProfileSeed_of_zero_nonparabolic b τ
    (by simpa only [neg_div, Set.mem_Icc] using abs_le.mp hτ.2)
  intro γ hγ
  by_contra hn
  have hh : 1 < (γ • τ).im := hs (subset_tsupport b hn)
  exact (not_le_of_gt hh)
    (modular_smul_im_le_one_of_mem_fd_of_lowerLeft_ne_zero γ hτ hγ)

/-- A genuine scalar cusp lift in the original smooth automorphic core. -/
def cuspProfileCore (b : ℝ → ℂ) (hb : ContDiff ℝ ∞ b) (hc : HasCompactSupport b)
    (hs : tsupport b ⊆ Ioi (1 : ℝ)) : smoothCore :=
  ⟨modularPeriodization (cuspProfileSeed b),
    modularPeriodization_mem_smoothCore_of_upper_support
      (contDiff_cuspProfileSeed hb) (cuspProfileSeed_hasCompactSupport hc)
      (cuspProfileSeed_upper_support hc hs)⟩

theorem cuspProfileCore_eq_on_fd (b : ℝ → ℂ) (hb : ContDiff ℝ ∞ b)
    (hc : HasCompactSupport b) (hs : tsupport b ⊆ Ioi (1 : ℝ))
    {τ : UpperHalfPlane} (hτ : τ ∈ fd) :
    (cuspProfileCore b hb hc hs).val τ = b τ.im :=
  modularPeriodization_cuspProfileSeed_eq_on_fd hs hτ

theorem cuspProfileCore_value_ae (b : ℝ → ℂ) (hb : ContDiff ℝ ∞ b)
    (hc : HasCompactSupport b) (hs : tsupport b ⊆ Ioi (1 : ℝ)) :
    value (cuspProfileCore b hb hc hs) =ᵐ[modularMeasure]
      (fun τ : UpperHalfPlane => b τ.im) := by
  apply (value_ae (cuspProfileCore b hb hc hs)).trans
  filter_upwards [ae_mem_fdo] with τ hτ
  exact cuspProfileCore_eq_on_fd b hb hc hs (fdo_subset_fd hτ)

end GapFamily.Analytic

namespace GapFamily.Analytic
open Set UpperHalfPlane MeasureTheory ModularGradient
open scoped ContDiff

theorem cuspProfileCore_directional_ae (b : ℝ → ℂ) (hb : ContDiff ℝ ∞ b)
    (hc : HasCompactSupport b) (hs : tsupport b ⊆ Ioi (1 : ℝ)) (v : ℂ) :
    directional (cuspProfileCore b hb hc hs).val v =ᵐ[modularMeasure]
      (fun τ : UpperHalfPlane => (τ.im : ℂ) * (v.im • deriv b τ.im)) := by
  have hg : ContDiff ℝ ∞ (fun z : ℂ => b z.im) := hb.comp Complex.imCLM.contDiff
  have heq : (fun τ : UpperHalfPlane => (cuspProfileCore b hb hc hs).val τ)
      =ᵐ[modularMeasure] (fun τ : UpperHalfPlane => b τ.im) := by
    filter_upwards [ae_mem_fdo] with τ hτ
    exact cuspProfileCore_eq_on_fd b hb hc hs (ModularGroup.fdo_subset_fd hτ)
  have hdir := modularDirectional_ae_eq
    ((cuspProfileCore b hb hc hs).property.1.continuousOn.mono
      (fun _ hz => im_pos_of_mem_modularInterior hz)) hg.continuous.continuousOn heq v
  apply hdir.trans
  apply Filter.Eventually.of_forall
  intro τ
  have hd := ((hb.differentiable (by simp)) τ.im).hasFDerivAt.comp
    (τ : ℂ) Complex.imCLM.hasFDerivAt
  change (τ.im : ℂ) * fderiv ℝ (b ∘ Complex.im) τ v = _
  rw [hd.fderiv]
  change (τ.im : ℂ) * fderiv ℝ b τ.im v.im = _
  rw [fderiv_eq_smul_deriv]

end GapFamily.Analytic
