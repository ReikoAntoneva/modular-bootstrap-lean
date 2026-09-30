import GapFamily.Analytic.Spatial.SpatialPointKernelBasic
import GapFamily.Analytic.Spatial.SpatialPointPeriodization
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Ordinary energy density for the point Fourier transform

The complex power uses a strictly positive real base on the physical cone.
For `Re s > 1` its edge and infinite tail are dominated by an ordinary
Gamma–Laplace density. The point transform normalization has the same
complex parameter as the spatial kernel.
-/

noncomputable section

namespace GapFamily.Analytic.SpatialPoint

open Set MeasureTheory PoincareFourier

/-- Same-parameter complex Fourier–Laplace normalization. -/
def spatialLaplaceConstantComplex (s : ℂ) : ℂ :=
  (2 : ℂ) ^ (2 * s - 1) * (Real.pi : ℂ) ^ (2 * s) / Complex.Gamma s ^ 2

theorem spatialLaplaceConstantComplex_ofReal (s : ℝ) :
    spatialLaplaceConstantComplex s =
      ((2 ^ (2 * s - 1) * Real.pi ^ (2 * s) / Real.Gamma s ^ 2 : ℝ) : ℂ) := by
  unfold spatialLaplaceConstantComplex
  rw [show 2 * (s : ℂ) - 1 = ((2 * s - 1 : ℝ) : ℂ) by push_cast; rfl,
    show 2 * (s : ℂ) = ((2 * s : ℝ) : ℂ) by push_cast; rfl,
    ← Complex.ofReal_ofNat 2, ← Complex.ofReal_cpow (by norm_num),
    ← Complex.ofReal_cpow Real.pi_pos.le, Complex.Gamma_ofReal]
  push_cast
  rfl

theorem spatialLaplaceConstantComplex_one_half :
    spatialLaplaceConstantComplex (1 / 2) = 1 := by
  have h := spatialLaplaceConstantComplex_ofReal (1 / 2)
  norm_num [Real.Gamma_one_half_eq, Real.sq_sqrt Real.pi_pos.le, Real.pi_ne_zero] at h
  exact h

/-- Reciprocal Gamma makes the exact normalization entire, including at the
zeros where the totalized Gamma function itself is not differentiable. -/
theorem analyticAt_spatialLaplaceConstantComplex (s : ℂ) :
    AnalyticAt ℂ spatialLaplaceConstantComplex s := by
  have ha : Differentiable ℂ (fun t : ℂ => 2 * t) :=
    (differentiable_const 2).mul differentiable_id
  have htwo : Differentiable ℂ (fun t : ℂ => (2 : ℂ) ^ (2 * t - 1)) :=
    (ha.sub_const 1).const_cpow (Or.inl (by norm_num))
  have hpi : Differentiable ℂ (fun t : ℂ => (Real.pi : ℂ) ^ (2 * t)) :=
    ha.const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
  have h := ((htwo.mul hpi).mul (Complex.differentiable_one_div_Gamma.pow 2)).analyticAt s
  convert h using 1
  ext t
  simp only [spatialLaplaceConstantComplex, div_eq_mul_inv, inv_pow, Pi.mul_apply, Pi.pow_apply]

/-- The ordinary energy density in a fixed real-frequency cone slice. -/
def pointFourierLaplaceDensity (s : ℂ) (Y J E : ℝ) : ℂ :=
  ((E ^ 2 - J ^ 2 : ℝ) : ℂ) ^ (s - 1) *
    Complex.exp ((-2 * Real.pi * Y * E : ℝ) : ℂ)

private theorem cone_base_pos {E J : ℝ} (hE : |J| < E) :
    0 < E ^ 2 - J ^ 2 := by
  have he0 := (abs_nonneg J).trans_lt hE
  nlinarith [sq_abs J, (sq_lt_sq₀ (abs_nonneg J) he0.le).mpr hE]

theorem continuousOn_pointFourierLaplaceDensity (s : ℂ) (Y J : ℝ) :
    ContinuousOn (pointFourierLaplaceDensity s Y J) (Ioi |J|) := by
  have hp : ContinuousOn (fun E : ℝ => ((E ^ 2 - J ^ 2 : ℝ) : ℂ) ^ (s - 1))
      (Ioi |J|) :=
    (by fun_prop : Continuous (fun E : ℝ => ((E ^ 2 - J ^ 2 : ℝ) : ℂ))).continuousOn.cpow_const
      (fun E hE => Or.inl (cone_base_pos hE))
  exact hp.mul (by fun_prop)

theorem norm_pointFourierLaplaceDensity (s : ℂ) (Y J E : ℝ) (hE : |J| < E) :
    ‖pointFourierLaplaceDensity s Y J E‖ =
      (E ^ 2 - J ^ 2) ^ (s.re - 1) * Real.exp (-2 * Real.pi * Y * E) := by
  rw [pointFourierLaplaceDensity, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos (cone_base_pos hE)]
  simp only [Complex.sub_re, Complex.one_re, Complex.norm_exp, Complex.ofReal_re]

/-- Ordinary absolute integrability at the cone edge and at infinity.
No totalized integral is used as a convergence substitute. -/
theorem integrableOn_pointFourierLaplaceDensity {s : ℂ} (hs : 1 < s.re)
    {Y : ℝ} (hY : 0 < Y) (J : ℝ) :
    IntegrableOn (pointFourierLaplaceDensity s Y J) (Ioi |J|) := by
  have hi : IntegrableOn
      (fun E : ℝ => E ^ (2 * (s.re - 1)) * Real.exp (-2 * Real.pi * Y * E)) (Ioi 0) := by
    simpa only [Real.rpow_one, neg_mul] using
      (integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := 2 * (s.re - 1))
        (b := 2 * Real.pi * Y) (by linarith) zero_lt_one (by positivity))
  apply (hi.mono_set (fun E hE => (abs_nonneg J).trans_lt hE)).mono'
  · exact (continuousOn_pointFourierLaplaceDensity s Y J).aestronglyMeasurable measurableSet_Ioi
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with E hE
    have hE0 : 0 < E := (abs_nonneg J).trans_lt hE
    rw [norm_pointFourierLaplaceDensity s Y J E hE]
    apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
    calc
      (E ^ 2 - J ^ 2) ^ (s.re - 1) ≤ (E ^ 2) ^ (s.re - 1) :=
        Real.rpow_le_rpow (cone_base_pos hE).le (by nlinarith [sq_nonneg J]) (by linarith)
      _ = E ^ (2 * (s.re - 1)) := by
        rw [← Real.rpow_two, ← Real.rpow_mul hE0.le]

/-- Every real Fourier character preserves ordinary horizontal integrability. -/
theorem integrable_pointKernel_fourier (s : ℂ) (hs : 1 < s.re)
    (y : ℝ) (hy : 0 < y) (w : UpperHalfPlane) (J : ℝ) :
    Integrable (fun x : ℝ =>
      Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * (J : ℂ) * (x : ℂ)) *
        pointKernel s (rowPoint y hy x) w) := by
  apply (integrable_pointHorizontalKernel s hs y hy w).bdd_mul (c := 1)
  · exact (by fun_prop : Continuous (fun x : ℝ =>
      Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * (J : ℂ) * (x : ℂ)))).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun x => by
      simp [Complex.norm_exp, Complex.mul_re, Complex.mul_im]

end GapFamily.Analytic.SpatialPoint
