import GapFamily.Analytic.Modular.Periodization.ModularPeriodizationUpper
import Mathlib.Analysis.InnerProductSpace.Calculus

noncomputable section
namespace GapFamily.Analytic
open Set UpperHalfPlane
open scoped ContDiff MatrixGroups

/-- The actual nonnegative real norm square, regarded as a complex seed. -/
def normSquareSeed (χ : ℂ → ℂ) (z : ℂ) : ℂ := (Complex.normSq (χ z) : ℂ)

@[simp] theorem normSquareSeed_re (χ : ℂ → ℂ) (z : ℂ) :
    (normSquareSeed χ z).re = Complex.normSq (χ z) := rfl

@[simp] theorem normSquareSeed_im (χ : ℂ → ℂ) (z : ℂ) :
    (normSquareSeed χ z).im = 0 := rfl

@[simp] theorem tsupport_normSquareSeed (χ : ℂ → ℂ) :
    tsupport (normSquareSeed χ) = tsupport χ := by
  unfold tsupport
  congr 1
  ext z
  simp [Function.mem_support, normSquareSeed]

theorem hasCompactSupport_normSquareSeed {χ : ℂ → ℂ} (hc : HasCompactSupport χ) :
    HasCompactSupport (normSquareSeed χ) := by
  simpa only [HasCompactSupport, tsupport_normSquareSeed] using hc

theorem normSquareSeed_contDiff {χ : ℂ → ℂ} (hχ : ContDiff ℝ ∞ χ) :
    ContDiff ℝ ∞ (normSquareSeed χ) := by
  change ContDiff ℝ ∞ (fun z => (Complex.normSq (χ z) : ℂ))
  simpa only [Complex.normSq_eq_norm_sq, Function.comp_def,
    Complex.ofRealCLM_apply] using Complex.ofRealCLM.contDiff.comp (hχ.norm_sq ℂ)

/-- Compact upper support gives a genuinely summable orbit sum of the real squares. -/
theorem summable_normSquareSeed_orbit {χ : ℂ → ℂ} (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ upperHalfPlaneSet) (τ : UpperHalfPlane) :
    Summable (fun γ : SL(2, ℤ) => Complex.normSq (χ (↑(γ • τ : UpperHalfPlane) : ℂ))) := by
  apply summable_of_hasFiniteSupport
  have hf := (locallyFinite_modular_orbit_support_of_upper_support hc hs).point_finite τ
  simpa [Function.HasFiniteSupport, Function.support] using hf

/-- The normalization is exactly one half of the real orbit sum. -/
theorem modularPeriodization_normSquareSeed_re (χ : ℂ → ℂ) (τ : UpperHalfPlane) :
    (modularPeriodization (normSquareSeed χ) τ).re =
      (1 / 2 : ℝ) * ∑' γ : SL(2, ℤ),
        Complex.normSq (χ (↑(γ • τ : UpperHalfPlane) : ℂ)) := by
  rw [modularPeriodization_coe]
  simp only [normSquareSeed]
  rw [← Complex.ofReal_tsum]
  simp

theorem modularPeriodization_normSquareSeed_re_nonneg (χ : ℂ → ℂ)
    (τ : UpperHalfPlane) : 0 ≤ (modularPeriodization (normSquareSeed χ) τ).re := by
  rw [modularPeriodization_normSquareSeed_re]
  exact mul_nonneg (by norm_num) (tsum_nonneg fun _ => Complex.normSq_nonneg _)

/-- The identity orbit term alone gives the required lower bound. -/
theorem modularPeriodization_normSquareSeed_re_ge_half {χ : ℂ → ℂ}
    (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ upperHalfPlaneSet)
    (τ : UpperHalfPlane) (hχ : χ τ = 1) :
    (1 / 2 : ℝ) ≤ (modularPeriodization (normSquareSeed χ) τ).re := by
  rw [modularPeriodization_normSquareSeed_re]
  have hsum := (summable_normSquareSeed_orbit hc hs τ).le_tsum
    (1 : SL(2, ℤ)) (fun γ _ => Complex.normSq_nonneg _)
  simp only [one_smul, hχ, Complex.normSq_one] at hsum
  linarith

end GapFamily.Analytic
