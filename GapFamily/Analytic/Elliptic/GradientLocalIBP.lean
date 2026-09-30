import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

/-!
# Local integration by parts for the complex plane

The differentiated function only needs to be continuously differentiable on
an open set. A globally continuously differentiable compactly supported test
whose support lies in that set gives the ordinary real-direction integration
by parts identity. All three product integrability obligations are proved
from continuity on the compact test support.
-/

namespace GapFamily.Analytic.Dirichlet

open MeasureTheory Set

noncomputable section

variable {U : Set ℂ} {f g : ℂ → ℂ}

/-- Local continuity of the first factor suffices to integrate a product
with a compactly supported continuous test. -/
theorem local_mul_test_integrable (hf : ContinuousOn f U) (hg : Continuous g)
    (hc : HasCompactSupport g) (hs : tsupport g ⊆ U) :
    Integrable (fun z ↦ f z * g z) := by
  apply ((hf.mono hs).mul hg.continuousOn).integrableOn_compact hc
    |>.integrable_of_forall_notMem_eq_zero
  intro z hz
  simp [image_eq_zero_of_notMem_tsupport hz]

/-- A real-direction derivative paired with a compactly supported test is
integrable, despite no global regularity hypothesis on the first factor. -/
theorem local_fderiv_mul_test_integrable (hU : IsOpen U)
    (hf : ContDiffOn ℝ 1 f U) (hg : Continuous g)
    (hc : HasCompactSupport g) (hs : tsupport g ⊆ U) (v : ℂ) :
    Integrable (fun z ↦ fderiv ℝ f z v * g z) :=
  local_mul_test_integrable
    ((hf.continuousOn_fderiv_of_isOpen hU le_rfl).clm_apply continuousOn_const)
    hg hc hs

/-- A locally continuous function paired with a derivative of a smooth
compactly supported test is integrable. -/
theorem local_mul_fderiv_test_integrable (hf : ContinuousOn f U)
    (hg : ContDiff ℝ 1 g) (hc : HasCompactSupport g)
    (hs : tsupport g ⊆ U) (v : ℂ) :
    Integrable (fun z ↦ f z * fderiv ℝ g z v) :=
  local_mul_test_integrable hf
    ((hg.continuous_fderiv (by norm_num)).clm_apply continuous_const)
    (hc.fderiv_apply ℝ v) ((tsupport_fderiv_apply_subset ℝ v).trans hs)

/-- Local integration by parts, with the derivative initially on the test. -/
theorem local_integral_mul_fderiv_eq_neg (hU : IsOpen U)
    (hf : ContDiffOn ℝ 1 f U) (hg : ContDiff ℝ 1 g)
    (hc : HasCompactSupport g) (hs : tsupport g ⊆ U) (v : ℂ) :
    ∫ z, f z * fderiv ℝ g z v = -∫ z, fderiv ℝ f z v * g z := by
  apply integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (local_fderiv_mul_test_integrable hU hf hg.continuous hc hs v)
    (local_mul_fderiv_test_integrable hf.continuousOn hg hc hs v)
    (local_mul_test_integrable hf.continuousOn hg.continuous hc hs)
  · intro z hz
    exact (hf.differentiableOn (by norm_num) z (hs hz)).differentiableAt
      (hU.mem_nhds (hs hz))
  · intro z _
    exact hg.differentiable (by norm_num) z

/-- Local integration by parts, with the derivative initially on the
locally smooth function. -/
theorem local_integral_fderiv_mul_eq_neg (hU : IsOpen U)
    (hf : ContDiffOn ℝ 1 f U) (hg : ContDiff ℝ 1 g)
    (hc : HasCompactSupport g) (hs : tsupport g ⊆ U) (v : ℂ) :
    ∫ z, fderiv ℝ f z v * g z = -∫ z, f z * fderiv ℝ g z v := by
  simpa only [neg_neg] using
    congrArg Neg.neg (local_integral_mul_fderiv_eq_neg hU hf hg hc hs v).symm

/-- Restricting the pairing to the open set gives the same identity;
the test and its derivative both vanish outside that set. -/
theorem local_setIntegral_fderiv_mul_eq_neg (hU : IsOpen U)
    (hf : ContDiffOn ℝ 1 f U) (hg : ContDiff ℝ 1 g)
    (hc : HasCompactSupport g) (hs : tsupport g ⊆ U) (v : ℂ) :
    ∫ z in U, fderiv ℝ f z v * g z = -∫ z in U, f z * fderiv ℝ g z v := by
  have h₁ : ∫ z in U, fderiv ℝ f z v * g z = ∫ z, fderiv ℝ f z v * g z := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro z hz
    have hzg : z ∉ tsupport g := fun hzg ↦ hz (hs hzg)
    simp [image_eq_zero_of_notMem_tsupport hzg]
  have h₂ : ∫ z in U, f z * fderiv ℝ g z v = ∫ z, f z * fderiv ℝ g z v := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro z hz
    have hzg : z ∉ tsupport g := fun hzg ↦ hz (hs hzg)
    simp [fderiv_of_notMem_tsupport ℝ hzg]
  rw [h₁, h₂]
  exact local_integral_fderiv_mul_eq_neg hU hf hg hc hs v

end

end GapFamily.Analytic.Dirichlet
