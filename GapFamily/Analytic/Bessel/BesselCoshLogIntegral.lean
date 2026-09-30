import GapFamily.Analytic.Bessel.BesselCoshOrder
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

/-! The ordinary full-line exponential kernel for the complex-order cosh integral. -/
noncomputable section
namespace GapFamily.Analytic.BesselCoshOrder
open Set Filter MeasureTheory
open scoped Topology

/-- The literal logarithmic kernel before the positive and negative halves are combined. -/
def logKernel (κ : ℂ) (T u : ℝ) : ℂ :=
  Complex.exp (-(T : ℂ) * (Real.cosh u : ℂ)) * Complex.exp (κ * (u : ℂ))

/-- The actual full-line kernel is bounded by the same integrable Gaussian. -/
theorem norm_logKernel_le_majorant (κ : ℂ) {T : ℝ} (hT : 0 < T) (u : ℝ) :
    ‖logKernel κ T u‖ ≤ majorant T ‖κ‖ u := by
  have hexp : ‖Complex.exp (-(T : ℂ) * (Real.cosh u : ℂ))‖ =
      Real.exp (-T * Real.cosh u) := by simp [Complex.norm_exp]
  have hphase : ‖Complex.exp (κ * (u : ℂ))‖ ≤ Real.exp (‖κ‖ * |u|) := by
    simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs] using
      Complex.norm_exp_le_exp_norm (κ * (u : ℂ))
  have hcosh : u ^ 2 / 2 ≤ Real.cosh u := by
    simpa only [sq_abs, Real.cosh_abs] using sq_half_le_cosh (abs_nonneg u)
  have hquad := mul_le_mul_of_nonneg_left hcosh hT.le
  have hcomplete := quadratic_exponent_bound (a := T) (R := ‖κ‖) (u := |u|) hT
  simp only [sq_abs] at hcomplete
  calc
    _ ≤ Real.exp (-T * Real.cosh u) * Real.exp (‖κ‖ * |u|) := by
      rw [logKernel, norm_mul, hexp]
      exact mul_le_mul_of_nonneg_left hphase (Real.exp_pos _).le
    _ = Real.exp (-T * Real.cosh u + ‖κ‖ * |u|) := (Real.exp_add _ _).symm
    _ ≤ Real.exp (‖κ‖ ^ 2 / T - (T / 4) * u ^ 2) := by
      apply Real.exp_le_exp.mpr
      exact (show -T * Real.cosh u + ‖κ‖ * |u| ≤
        -(T / 2) * u ^ 2 + ‖κ‖ * |u| by nlinarith).trans hcomplete
    _ = majorant T ‖κ‖ u := by
      unfold majorant
      rw [← Real.exp_add]
      congr 1
      ring

/-- Ordinary absolute convergence holds on the whole real line at every complex order. -/
theorem logKernel_integrable (κ : ℂ) {T : ℝ} (hT : 0 < T) :
    Integrable (logKernel κ T) := by
  have hc : Continuous (logKernel κ T) := by unfold logKernel; fun_prop
  exact (majorant_integrable_global (R := ‖κ‖) hT).mono'
    hc.aestronglyMeasurable (Eventually.of_forall (norm_logKernel_le_majorant κ hT))

/-- Splitting the genuine integral at zero produces exactly twice the cosh integral. -/
theorem integral_logKernel (κ : ℂ) {T : ℝ} (hT : 0 < T) :
    (∫ u : ℝ, logKernel κ T u) = 2 * besselK κ T := by
  have hi := logKernel_integrable κ hT
  have hneg (u : ℝ) : logKernel κ T (-u) = logKernel (-κ) T u := by
    simp only [logKernel, Real.cosh_neg, Complex.ofReal_neg, mul_neg, neg_mul]
  have hni : IntegrableOn (fun u : ℝ => logKernel κ T (-u)) (Ioi 0) := by
    simpa only [hneg] using (logKernel_integrable (-κ) hT).integrableOn (s := Ioi 0)
  have hreflect : (∫ u : ℝ in Iic 0, logKernel κ T u) =
      ∫ u : ℝ in Ioi 0, logKernel κ T (-u) := by
    simpa only [neg_zero] using (integral_comp_neg_Ioi 0 (logKernel κ T)).symm
  have hsum (u : ℝ) : logKernel κ T u + logKernel κ T (-u) =
      2 * integrand κ T u := by
    simp only [logKernel, Real.cosh_neg, Complex.ofReal_neg, mul_neg]
    rw [← mul_add, ← Complex.two_cosh]
    unfold integrand
    ring
  calc
    _ = (∫ u : ℝ in Ioi 0, logKernel κ T u) +
        ∫ u : ℝ in Iic 0, logKernel κ T u := by
      simpa only [compl_Ioi] using (integral_add_compl measurableSet_Ioi hi).symm
    _ = ∫ u : ℝ in Ioi 0, logKernel κ T u + logKernel κ T (-u) := by
      rw [hreflect, integral_add hi.integrableOn hni]
    _ = ∫ u : ℝ in Ioi 0, 2 * integrand κ T u := by simp only [hsum]
    _ = 2 * besselK κ T := by rw [integral_const_mul, besselK]

end GapFamily.Analytic.BesselCoshOrder
