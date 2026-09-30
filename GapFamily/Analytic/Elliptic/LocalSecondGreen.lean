import GapFamily.Analytic.Elliptic.GradientLocalIBP
import Mathlib.Analysis.Calculus.FDeriv.Star

/-!
# Local second directional integration by parts

The first factor is smooth only on the open test region. The test is globally
smooth and compactly supported in that region. Both ordinary integrals converge.
-/

noncomputable section

namespace GapFamily.Analytic.PoincareGreen

open Set MeasureTheory
open scoped ContDiff

def secondDirectional (f : ℂ → ℂ) (z v : ℂ) : ℂ :=
  fderiv ℝ (fun w => fderiv ℝ f w v) z v

variable {U : Set ℂ} {f g : ℂ → ℂ}

theorem contDiffOn_directional (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) (v : ℂ) :
    ContDiffOn ℝ ∞ (fun z => fderiv ℝ f z v) U :=
  (hf.fderiv_of_isOpen hU (by simp)).clm_apply contDiffOn_const

theorem contDiff_directional (hg : ContDiff ℝ ∞ g) (v : ℂ) :
    ContDiff ℝ ∞ (fun z => fderiv ℝ g z v) :=
  (hg.fderiv_right (by simp)).clm_apply contDiff_const

/-- The two second-order pairings are genuine ordinary integrals. -/
theorem local_secondDirectional_integrable (hU : IsOpen U)
    (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiff ℝ ∞ g)
    (hc : HasCompactSupport g) (hs : tsupport g ⊆ U) (v : ℂ) :
    Integrable (fun z => f z * secondDirectional g z v) ∧
      Integrable (fun z => secondDirectional f z v * g z) := by
  have hf₂ := contDiffOn_directional hU (contDiffOn_directional hU hf v) v
  have hg₂ := contDiff_directional (contDiff_directional hg v) v
  constructor
  · exact Dirichlet.local_mul_test_integrable hf.continuousOn hg₂.continuous
      ((hc.fderiv_apply ℝ v).fderiv_apply ℝ v)
      ((tsupport_fderiv_apply_subset ℝ v).trans
        ((tsupport_fderiv_apply_subset ℝ v).trans hs))
  · exact Dirichlet.local_mul_test_integrable hf₂.continuousOn hg.continuous hc hs

/-- Two local first integration-by-parts identities move both derivatives. -/
theorem local_integral_mul_secondDirectional_eq (hU : IsOpen U)
    (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiff ℝ ∞ g)
    (hc : HasCompactSupport g) (hs : tsupport g ⊆ U) (v : ℂ) :
    (∫ z, f z * secondDirectional g z v) =
      ∫ z, secondDirectional f z v * g z := by
  have h₁ := Dirichlet.local_integral_mul_fderiv_eq_neg hU
    (hf.of_le (by simp)) ((contDiff_directional hg v).of_le (by simp))
    (hc.fderiv_apply ℝ v) ((tsupport_fderiv_apply_subset ℝ v).trans hs) v
  have h₂ := Dirichlet.local_integral_mul_fderiv_eq_neg hU
    ((contDiffOn_directional hU hf v).of_le (by simp)) (hg.of_le (by simp)) hc hs v
  change (∫ z, f z * secondDirectional g z v) =
    -(∫ z, fderiv ℝ f z v * fderiv ℝ g z v) at h₁
  change (∫ z, fderiv ℝ f z v * fderiv ℝ g z v) =
    -(∫ z, secondDirectional f z v * g z) at h₂
  rw [h₂, neg_neg] at h₁
  exact h₁

/-- Real directional second derivatives commute with complex conjugation. -/
@[simp] theorem secondDirectional_star (ψ : ℂ → ℂ) (z v : ℂ) :
    secondDirectional (fun w => star (ψ w)) z v = star (secondDirectional ψ z v) := by
  simp only [secondDirectional, fderiv_star, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, starL'_apply]

theorem contDiff_star (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (fun z => star (g z)) := by
  simpa only [Function.comp_def, starL'_apply] using
    (starL' ℝ : ℂ ≃L[ℝ] ℂ).contDiff.comp hg

/-- Conjugated second-order test pairings are ordinary integrable functions. -/
theorem local_star_secondDirectional_integrable (hU : IsOpen U)
    (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiff ℝ ∞ g)
    (hc : HasCompactSupport g) (hs : tsupport g ⊆ U) (v : ℂ) :
    Integrable (fun z => star (secondDirectional g z v) * f z) ∧
      Integrable (fun z => star (g z) * secondDirectional f z v) := by
  have hcstar : HasCompactSupport (fun z => star (g z)) :=
    hc.comp_left (star_zero ℂ)
  have hsstar : tsupport (fun z => star (g z)) ⊆ U :=
    (tsupport_comp_subset (star_zero ℂ) g).trans hs
  simpa only [secondDirectional_star, mul_comm] using
    local_secondDirectional_integrable hU hf (contDiff_star hg) hcstar hsstar v

/-- Conjugated local second integration by parts, with the test factor first. -/
theorem local_integral_star_secondDirectional_eq (hU : IsOpen U)
    (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiff ℝ ∞ g)
    (hc : HasCompactSupport g) (hs : tsupport g ⊆ U) (v : ℂ) :
    (∫ z, star (secondDirectional g z v) * f z) =
      ∫ z, star (g z) * secondDirectional f z v := by
  have hcstar : HasCompactSupport (fun z => star (g z)) :=
    hc.comp_left (star_zero ℂ)
  have hsstar : tsupport (fun z => star (g z)) ⊆ U :=
    (tsupport_comp_subset (star_zero ℂ) g).trans hs
  simpa only [secondDirectional_star, mul_comm] using
    local_integral_mul_secondDirectional_eq hU hf (contDiff_star hg) hcstar hsstar v

end GapFamily.Analytic.PoincareGreen
