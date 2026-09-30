import GapFamily.Analytic.Cusp.CuspCoordinateDeriv

/-!
# Actual logarithmic transport of scalar derivative energy

The exact exponential change of variables identifies physical derivative
energy with the shifted derivative energy of the logarithmic channel.
Integrability is transported in both directions, independently of compactness.
-/

noncomputable section

namespace GapFamily.Analytic

open Set MeasureTheory

theorem cuspLift_deriv_norm_sq_exp {v : ℝ → ℂ} (hv : Differentiable ℝ v) (t : ℝ) :
    Real.exp t * ‖deriv (cuspLift v) (Real.exp t)‖ ^ 2 =
      ‖deriv v t + (1 / 2 : ℝ) • v t‖ ^ 2 := by
  rw [deriv_cuspLift hv (Real.exp_pos t), Real.log_exp, norm_smul,
    Real.norm_eq_abs, abs_inv, abs_of_nonneg (Real.sqrt_nonneg _), mul_pow,
    inv_pow, Real.sq_sqrt (Real.exp_pos t).le]
  rw [← mul_assoc, mul_inv_cancel₀ (Real.exp_ne_zero t), one_mul]

/-- The ordinary physical energy exists exactly when the actual shifted
logarithmic derivative has integrable squared norm. -/
theorem integrableOn_deriv_cuspLift_norm_sq_iff {v : ℝ → ℂ}
    (hv : Differentiable ℝ v) :
    IntegrableOn (fun y => ‖deriv (cuspLift v) y‖ ^ 2) (Ioi 1) ↔
      IntegrableOn (fun t => ‖deriv v t + (1 / 2 : ℝ) • v t‖ ^ 2) (Ioi 0) := by
  have h := integrableOn_comp_exp_Ioi (fun y => ‖deriv (cuspLift v) y‖ ^ 2) 0
  simpa only [Real.exp_zero, smul_eq_mul, cuspLift_deriv_norm_sq_exp hv] using h.symm

/-- Exact change of variables for derivative energy. The companion equivalence
certifies genuine integrability whenever either physical or logarithmic energy is finite. -/
theorem integral_deriv_cuspLift_norm_sq {v : ℝ → ℂ} (hv : Differentiable ℝ v) :
    (∫ y in Ioi 1, ‖deriv (cuspLift v) y‖ ^ 2) =
      ∫ t in Ioi 0, ‖deriv v t + (1 / 2 : ℝ) • v t‖ ^ 2 := by
  have h := integral_comp_exp_Ioi (fun y => ‖deriv (cuspLift v) y‖ ^ 2) 0
  simpa only [Real.exp_zero, smul_eq_mul, cuspLift_deriv_norm_sq_exp hv] using h.symm

end GapFamily.Analytic
