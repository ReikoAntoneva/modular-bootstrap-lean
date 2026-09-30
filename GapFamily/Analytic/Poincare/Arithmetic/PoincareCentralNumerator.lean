import GapFamily.Analytic.Poincare.Fourier.PoincareFourierContinuation
import GapFamily.Analytic.Poincare.Fourier.PoincareFourierCentralSplit

/-! The actual central numerator obtained by removing the direct term and analytic remainder. -/
noncomputable section
namespace GapFamily.Analytic.PoincareCentralZeta
open Set MeasureTheory CuspFourierCutoff
open PoincareCanonical PoincareEnergyContinuation
open PoincareFourier PoincareFourierRemainder
open PoincareFourierContinuation

/-- The numerator is the actual continued Fourier coefficient minus its explicit
identity-coset contribution and its convergent denominator remainder. -/
def centralNumerator (y : ℝ) (hy : 0 < y) (j J : ℤ) (κ : ℂ) : ℂ :=
  continuedFourierCoefficient y hy j J κ -
    (if j = J then (y : ℂ) ^ (exponent κ) else 0) -
      fourierRemainder y j J (exponent κ)

/-- A positive real base gives an entire direct term in the continuation parameter. -/
theorem analyticAt_directFourierTerm (y : ℝ) (hy : 0 < y) (j J : ℤ) (κ : ℂ) :
    AnalyticAt ℂ (fun w => if j = J then (y : ℂ) ^ (exponent w) else 0) κ := by
  by_cases h : j = J
  · simp only [h, ite_true]
    have he : (fun w : ℂ => (y : ℂ) ^ (exponent w)) =
        (fun w : ℂ => Complex.exp (Complex.log (y : ℂ) * exponent w)) := by
      funext w
      exact Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hy.ne') _
    rw [he]
    unfold exponent
    fun_prop
  · simp only [h, ite_false]
    exact analyticAt_const

/-- Every parameter in the actual horizontal continuation domain lies in the
remainder's proved open convergence half-plane after the shift by one half. -/
theorem re_exponent_pos_of_mem_horizontalFourierDomain (y : ℝ) (hy : 0 < y)
    {κ : ℂ} (hκ : κ ∈ horizontalFourierDomain y hy) : 0 < (exponent κ).re := by
  have h := re_gt_neg_half_of_mem_continuation (horizontalContinuation y hy) hκ
  norm_num [exponent, Complex.add_re]
  linarith

/-- The actual central numerator is norm analytic on the full horizontal domain,
including the threshold disk and the punctured physical half-plane. -/
theorem analyticOnNhd_centralNumerator (y : ℝ) (hy : 0 < y) (j J : ℤ) :
    AnalyticOnNhd ℂ (centralNumerator y hy j J) (horizontalFourierDomain y hy) := by
  intro κ hκ
  have hr : AnalyticAt ℂ (fun w => fourierRemainder y j J (exponent w)) κ :=
    (analyticAt_fourierRemainder hy j J
      (re_exponent_pos_of_mem_horizontalFourierDomain y hy hκ)).comp_of_eq
        (show AnalyticAt ℂ exponent κ by unfold exponent; fun_prop) rfl
  exact ((analyticOnNhd_continuedFourierCoefficient y hy j J κ hκ).sub
    (analyticAt_directFourierTerm y hy j J κ)).sub hr

/-- In particular, the actual numerator is analytic at the threshold parameter. -/
theorem analyticAt_centralNumerator_zero (y : ℝ) (hy : 0 < y) (j J : ℤ) :
    AnalyticAt ℂ (centralNumerator y hy j J) 0 :=
  analyticOnNhd_centralNumerator y hy j J 0 (zero_mem_horizontalFourierDomain y hy)

/-- The numerator factors by the actual Kloosterman Dirichlet series on the
complete original convergence half-plane. -/
theorem centralNumerator_eq_dirichlet_common (y : ℝ) (hy : 0 < y) (j J : ℤ)
    {κ : ℂ} (hκ : (1 / 2 : ℝ) < κ.re) :
    centralNumerator y hy j J κ =
      (∫ t : ℝ, centralFourierKernel y j (exponent κ) t) *
        kloostermanDirichlet j J (exponent κ) := by
  have hs : 1 < (exponent κ).re := by
    norm_num [exponent, Complex.add_re]
    linarith
  rw [centralNumerator, continuedFourierCoefficient_eq_series y hy j J hκ,
    complexPoincareSeries_fourier_eq_central_add_remainder hy j J hs]
  ring

/-- At threshold the numerator is exactly the canonical global threshold
coefficient minus the direct term and the actual convergent remainder at one half. -/
theorem centralNumerator_zero (y : ℝ) (hy : 0 < y) (j J : ℤ) :
    centralNumerator y hy j J 0 = thresholdFourierCoefficient y hy j J -
      (if j = J then (y : ℂ) ^ (1 / 2 : ℂ) else 0) -
        fourierRemainder y j J (1 / 2 : ℂ) := by
  simp only [centralNumerator, continuedFourierCoefficient_zero, exponent, add_zero]

end GapFamily.Analytic.PoincareCentralZeta
