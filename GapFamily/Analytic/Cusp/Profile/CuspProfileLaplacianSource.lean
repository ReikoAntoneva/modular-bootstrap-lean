import GapFamily.Analytic.Cusp.Profile.CuspProfileLaplacianPairing
import GapFamily.Analytic.Cusp.Profile.CuspProfileLaplacianIBP

/-!
# The literal second-order value of a compact scalar profile

The function -y² b'' is itself a smooth compact scalar cusp profile. Its actual
modular L² class and pairing retain the exact hyperbolic Laplacian normalization.
-/

noncomputable section

namespace GapFamily.Analytic

open Set MeasureTheory UpperHalfPlane ModularGradient
open scoped ContDiff

def cuspProfileSecondOrder (b : ℝ → ℂ) (y : ℝ) : ℂ :=
  -((y : ℂ) ^ 2) * deriv (deriv b) y

theorem contDiff_cuspProfileSecondOrder {b : ℝ → ℂ} (hb : ContDiff ℝ ∞ b) :
    ContDiff ℝ ∞ (cuspProfileSecondOrder b) := by
  have hb' : ContDiff ℝ ∞ (deriv b) := (contDiff_infty_iff_deriv.mp hb).2
  have hb'' : ContDiff ℝ ∞ (deriv (deriv b)) := (contDiff_infty_iff_deriv.mp hb').2
  exact (Complex.ofRealCLM.contDiff.pow 2).neg.mul hb''

theorem cuspProfileSecondOrder_hasCompactSupport {b : ℝ → ℂ} (hc : HasCompactSupport b) :
    HasCompactSupport (cuspProfileSecondOrder b) := hc.deriv.deriv.mul_left

theorem cuspProfileSecondOrder_tsupport_subset (b : ℝ → ℂ) :
    tsupport (cuspProfileSecondOrder b) ⊆ tsupport b :=
  tsupport_mul_subset_right.trans (tsupport_deriv_subset.trans tsupport_deriv_subset)

/-- Actual modular Hilbert value with representative -y² b''(y). -/
def cuspProfileLaplacianValue (b : ℝ → ℂ) (hb : ContDiff ℝ ∞ b)
    (hc : HasCompactSupport b) (hs : tsupport b ⊆ Ioi (1 : ℝ)) : ModularHilbert :=
  value (cuspProfileCore (cuspProfileSecondOrder b) (contDiff_cuspProfileSecondOrder hb)
    (cuspProfileSecondOrder_hasCompactSupport hc)
    ((cuspProfileSecondOrder_tsupport_subset b).trans hs))

theorem cuspProfileLaplacianValue_ae (b : ℝ → ℂ) (hb : ContDiff ℝ ∞ b)
    (hc : HasCompactSupport b) (hs : tsupport b ⊆ Ioi (1 : ℝ)) :
    cuspProfileLaplacianValue b hb hc hs =ᵐ[modularMeasure]
      fun τ : UpperHalfPlane => -((τ.im : ℂ) ^ 2) * deriv (deriv b) τ.im :=
  cuspProfileCore_value_ae _ _ _ _

/-- Exact cancellation of the inverse-square cusp density in the Laplacian pairing. -/
theorem cuspProfileLaplacianValue_pairing (b : ℝ → ℂ) (hb : ContDiff ℝ ∞ b)
    (hc : HasCompactSupport b) (hs : tsupport b ⊆ Ioi (1 : ℝ)) (F : smoothCore) :
    inner ℂ (cuspProfileLaplacianValue b hb hc hs) (value F) =
      -(∫ y : ℝ in Ioi 1, star (deriv (deriv b) y) * cuspHorizontalAverage F.val y) := by
  rw [cuspProfileLaplacianValue, cuspProfileCore_value_pairing, ← integral_neg]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro y hy
  have hy0 : (y : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (zero_lt_one.trans hy))
  dsimp only
  simp only [cuspProfileSecondOrder, map_mul, map_neg, map_pow,
    Complex.real_smul, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_pow,
    starRingEnd_apply]
  field_simp
  simp

end GapFamily.Analytic
