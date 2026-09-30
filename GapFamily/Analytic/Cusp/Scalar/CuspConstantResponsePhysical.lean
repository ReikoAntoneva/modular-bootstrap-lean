import GapFamily.Analytic.Cusp.Scalar.CuspConstantResponsePairing
import GapFamily.Analytic.Cusp.CuspCoordinateDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# The constant-source response in the physical cusp coordinate

This is the actual square-root lift of the continued logarithmic response.
Its removable value at `κ = 1/2` is `log y`. The first and second physical
height derivatives prove the inhomogeneous scalar equation above height zero.
-/

noncomputable section

open Filter Set MeasureTheory
open scoped Topology

namespace GapFamily.Analytic

/-- Actual physical-coordinate lift of the scalar constant-source response. -/
def cuspConstantPhysicalResponse (κ : ℂ) : ℝ → ℂ :=
  cuspLift (cuspConstantLogResponse κ)

private theorem sqrt_mul_exp_log {y : ℝ} (hy : 0 < y) (κ : ℂ) :
    (Real.sqrt y : ℂ) * Complex.exp (-κ * (Real.log y : ℂ)) =
      (y : ℂ) ^ ((1 / 2 : ℂ) - κ) := by
  rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hy, Complex.ofReal_exp,
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hy.ne'),
    ← Complex.ofReal_log hy.le, ← Complex.exp_add]
  congr 1
  push_cast
  ring

private theorem sqrt_mul_exp_half_log {y : ℝ} (hy : 0 < y) :
    (Real.sqrt y : ℂ) * Complex.exp (-(1 / 2 : ℂ) * (Real.log y : ℂ)) = 1 := by
  simpa using sqrt_mul_exp_log hy (1 / 2 : ℂ)

/-- Away from the two roots of the spectral parameter, the lifted response
is the usual power quotient. -/
theorem cuspConstantPhysicalResponse_eq_quotient {κ : ℂ}
    (hκ : κ ≠ -(1 / 2 : ℂ)) (hκ' : κ ≠ (1 / 2 : ℂ))
    {y : ℝ} (hy : 0 < y) :
    cuspConstantPhysicalResponse κ y =
      ((y : ℂ) ^ ((1 / 2 : ℂ) - κ) - 1) / (1 / 4 - κ ^ 2) := by
  rw [cuspConstantPhysicalResponse, cuspLift, Complex.real_smul,
    cuspConstantLogResponse_eq_quotient hκ' hκ]
  rw [show -(Real.log y : ℂ) / 2 = -(1 / 2 : ℂ) * (Real.log y : ℂ) by ring]
  rw [← mul_div_assoc, mul_sub, sqrt_mul_exp_log hy, sqrt_mul_exp_half_log hy]

/-- The removable physical response is the genuine logarithm. -/
theorem cuspConstantPhysicalResponse_half {y : ℝ} (hy : 0 < y) :
    cuspConstantPhysicalResponse (1 / 2 : ℂ) y = (Real.log y : ℂ) := by
  rw [cuspConstantPhysicalResponse, cuspLift, Complex.real_smul,
    cuspConstantLogResponse_half]
  rw [show -(Real.log y : ℂ) / 2 = -(1 / 2 : ℂ) * (Real.log y : ℂ) by ring]
  calc
    _ = (Real.log y : ℂ) *
        ((Real.sqrt y : ℂ) * Complex.exp (-(1 / 2 : ℂ) * (Real.log y : ℂ))) := by ring
    _ = _ := by rw [sqrt_mul_exp_half_log hy, mul_one]

@[simp] theorem cuspConstantPhysicalResponse_one (κ : ℂ) :
    cuspConstantPhysicalResponse κ 1 = 0 := by
  simp [cuspConstantPhysicalResponse, cuspLift]

private theorem hasDerivAt_power_quotient {κ : ℂ}
    (hκ' : κ ≠ (1 / 2 : ℂ))
    {y : ℝ} (hy : 0 < y) :
    HasDerivAt (fun y : ℝ => ((y : ℂ) ^ ((1 / 2 : ℂ) - κ) - 1) / (1 / 4 - κ ^ 2))
      ((y : ℂ) ^ (-(1 / 2 : ℂ) - κ) / (κ + 1 / 2)) y := by
  have hp : (1 / 2 : ℂ) - κ ≠ 0 := sub_ne_zero.mpr (Ne.symm hκ')
  apply ((hasDerivAt_ofReal_cpow_const hy.ne' hp).sub_const 1 |>.div_const _).congr_deriv
  rw [show (1 / 2 : ℂ) - κ - 1 = -(1 / 2 : ℂ) - κ by ring]
  rw [show (1 / 4 : ℂ) - κ ^ 2 = ((1 / 2 : ℂ) - κ) * (κ + 1 / 2) by ring]
  rw [mul_div_mul_left _ _ hp]

/-- The actual height derivative, also valid at the removable parameter. -/
theorem hasDerivAt_cuspConstantPhysicalResponse {κ : ℂ}
    (hκ : κ ≠ -(1 / 2 : ℂ)) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (cuspConstantPhysicalResponse κ)
      ((y : ℂ) ^ (-(1 / 2 : ℂ) - κ) / (κ + 1 / 2)) y := by
  by_cases hκ' : κ = (1 / 2 : ℂ)
  · subst κ
    have hlog : HasDerivAt (fun t : ℝ => (Real.log t : ℂ)) ((y⁻¹ : ℝ) : ℂ) y :=
      Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt y (Real.hasDerivAt_log hy.ne')
    have hd : HasDerivAt (fun t : ℝ => (Real.log t : ℂ))
        ((y : ℂ) ^ (-(1 / 2 : ℂ) - 1 / 2) / (1 / 2 + 1 / 2)) y := by
      convert hlog using 1
      norm_num [Complex.cpow_neg_one]
    apply hd.congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds hy] with v hv
    exact cuspConstantPhysicalResponse_half hv
  · apply (hasDerivAt_power_quotient hκ' hy).congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds hy] with v hv
    exact cuspConstantPhysicalResponse_eq_quotient hκ hκ' hv

theorem deriv_cuspConstantPhysicalResponse {κ : ℂ}
    (hκ : κ ≠ -(1 / 2 : ℂ)) {y : ℝ} (hy : 0 < y) :
    deriv (cuspConstantPhysicalResponse κ) y =
      (y : ℂ) ^ (-(1 / 2 : ℂ) - κ) / (κ + 1 / 2) :=
  (hasDerivAt_cuspConstantPhysicalResponse hκ hy).deriv

/-- The second derivative comes from an identity on the open positive half-line. -/
theorem hasDerivAt_deriv_cuspConstantPhysicalResponse {κ : ℂ}
    (hκ : κ ≠ -(1 / 2 : ℂ)) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (deriv (cuspConstantPhysicalResponse κ))
      (-(y : ℂ) ^ (-(3 / 2 : ℂ) - κ)) y := by
  have hp : -(1 / 2 : ℂ) - κ ≠ 0 := by
    intro h
    apply hκ
    linear_combination -h
  have ha : κ + 1 / 2 ≠ 0 := by intro h; apply hκ; linear_combination h
  have hd : HasDerivAt (fun y : ℝ => (y : ℂ) ^ (-(1 / 2 : ℂ) - κ) / (κ + 1 / 2))
      (-(y : ℂ) ^ (-(3 / 2 : ℂ) - κ)) y := by
    apply ((hasDerivAt_ofReal_cpow_const hy.ne' hp).div_const _).congr_deriv
    rw [show -(1 / 2 : ℂ) - κ - 1 = -(3 / 2 : ℂ) - κ by ring]
    rw [show -(1 / 2 : ℂ) - κ = -(κ + 1 / 2) by ring,
      neg_mul, neg_div, mul_div_cancel_left₀ _ ha]
  apply hd.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hy] with v hv
  exact deriv_cuspConstantPhysicalResponse hκ hv

/-- The actual continued physical response solves the constant-source equation. -/
theorem cuspConstantPhysicalResponse_forcedODE {κ : ℂ}
    (hκ : κ ≠ -(1 / 2 : ℂ)) {y : ℝ} (hy : 0 < y) :
    -(y : ℂ) ^ 2 * deriv (deriv (cuspConstantPhysicalResponse κ)) y -
      (1 / 4 - κ ^ 2) * cuspConstantPhysicalResponse κ y = 1 := by
  rw [(hasDerivAt_deriv_cuspConstantPhysicalResponse hκ hy).deriv, neg_mul_neg]
  have hpow : (y : ℂ) ^ 2 * (y : ℂ) ^ (-(3 / 2 : ℂ) - κ) =
      (y : ℂ) ^ ((1 / 2 : ℂ) - κ) := by
    rw [← Complex.cpow_natCast, ← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hy.ne')]
    congr 1
    norm_num
    ring
  rw [hpow]
  by_cases hκ' : κ = (1 / 2 : ℂ)
  · subst κ
    norm_num
  · have ha : κ + 1 / 2 ≠ 0 := by intro h; apply hκ; linear_combination h
    have hp : (1 / 2 : ℂ) - κ ≠ 0 := sub_ne_zero.mpr (Ne.symm hκ')
    have hz : (1 / 4 : ℂ) - κ ^ 2 ≠ 0 := by
      rw [show (1 / 4 : ℂ) - κ ^ 2 = ((1 / 2 : ℂ) - κ) * (κ + 1 / 2) by ring]
      exact mul_ne_zero hp ha
    rw [cuspConstantPhysicalResponse_eq_quotient hκ hκ' hy, mul_div_cancel₀ _ hz]
    ring

/-- Pointwise energy density of the genuine physical height derivative. -/
theorem cuspConstantPhysicalResponse_deriv_norm_sq {κ : ℂ}
    (hκ : κ ≠ -(1 / 2 : ℂ)) {y : ℝ} (hy : 0 < y) :
    ‖deriv (cuspConstantPhysicalResponse κ) y‖ ^ 2 =
      y ^ (-1 - 2 * κ.re) / ‖κ + 1 / 2‖ ^ 2 := by
  rw [deriv_cuspConstantPhysicalResponse hκ hy, norm_div, div_pow,
    Complex.norm_cpow_eq_rpow_re_of_pos hy]
  congr 1
  rw [← Real.rpow_natCast, ← Real.rpow_mul hy.le]
  congr 1
  norm_num
  ring

/-- Finite ordinary vertical energy on the physical parameter half-plane. -/
theorem cuspConstantPhysicalResponse_deriv_sq_integrable {κ : ℂ} (hκ : 0 < κ.re) :
    IntegrableOn (fun y => ‖deriv (cuspConstantPhysicalResponse κ) y‖ ^ 2) (Ici 1) := by
  have hm : κ ≠ -(1 / 2 : ℂ) := by intro h; subst κ; norm_num at hκ
  have hi : IntegrableOn
      (fun y : ℝ => y ^ (-1 - 2 * κ.re) / ‖κ + 1 / 2‖ ^ 2) (Ici 1) := by
    rw [integrableOn_Ici_iff_integrableOn_Ioi]
    exact (integrableOn_Ioi_rpow_of_lt
      (by linarith : -1 - 2 * κ.re < -1) zero_lt_one).div_const _
  refine hi.congr_fun (fun y hy => ?_) measurableSet_Ici
  exact (cuspConstantPhysicalResponse_deriv_norm_sq hm (zero_lt_one.trans_le hy)).symm

/-- Exact ordinary vertical energy, accompanied by the preceding integrability theorem. -/
theorem integral_cuspConstantPhysicalResponse_deriv_sq {κ : ℂ} (hκ : 0 < κ.re) :
    (∫ y in Ici 1, ‖deriv (cuspConstantPhysicalResponse κ) y‖ ^ 2) =
      1 / (2 * κ.re * ‖κ + 1 / 2‖ ^ 2) := by
  have hm : κ ≠ -(1 / 2 : ℂ) := by intro h; subst κ; norm_num at hκ
  calc
    _ = ∫ y : ℝ in Ici 1, y ^ (-1 - 2 * κ.re) / ‖κ + 1 / 2‖ ^ 2 := by
      apply setIntegral_congr_fun measurableSet_Ici
      intro y hy
      exact cuspConstantPhysicalResponse_deriv_norm_sq hm (zero_lt_one.trans_le hy)
    _ = _ := by
      rw [integral_Ici_eq_integral_Ioi, integral_div,
        integral_Ioi_rpow_of_lt (by linarith : -1 - 2 * κ.re < -1) zero_lt_one]
      rw [Real.one_rpow]
      have hn : -1 - 2 * κ.re + 1 = -(2 * κ.re) := by ring
      rw [hn, neg_div_neg_eq, div_div]

/-- Genuine weighted L² membership of the actual physical response. -/
theorem cuspConstantPhysicalResponse_memLp {κ : ℂ} (hκ : 0 < κ.re) :
    MemLp (cuspConstantPhysicalResponse κ) 2 (cuspMeasure 1) := by
  have hm : κ ≠ -(1 / 2 : ℂ) := by intro h; subst κ; norm_num at hκ
  have hc : Continuous (cuspConstantLogResponse κ) := continuous_iff_continuousAt.mpr
    (fun t => (hasDerivAt_cuspConstantLogResponse hm t).continuousAt)
  unfold cuspConstantPhysicalResponse
  rw [memLp_two_cuspLift_iff hc.measurable zero_lt_one, Real.log_one,
    ← restrict_Ioi_eq_restrict_Ici]
  exact cuspConstantLogResponse_memLp hκ

/-- The actual finite weighted mass agrees with its logarithmic-coordinate mass. -/
theorem integral_cuspConstantPhysicalResponse_norm_sq {κ : ℂ} (hκ : 0 < κ.re) :
    (∫ y, ‖cuspConstantPhysicalResponse κ y‖ ^ 2 ∂cuspMeasure 1) =
      ∫ t : ℝ in Ioi 0, ‖cuspConstantLogResponse κ t‖ ^ 2 := by
  have hi : IntegrableOn (fun t => ‖cuspConstantLogResponse κ t‖ ^ 2) (Ici 0) := by
    rw [IntegrableOn, ← restrict_Ioi_eq_restrict_Ici]
    exact (cuspConstantLogResponse_memLp hκ).norm.integrable_sq
  unfold cuspConstantPhysicalResponse
  rw [integral_cuspMeasure_cuspLift_norm_sq _ zero_lt_one (by simpa using hi),
    Real.log_one, integral_Ici_eq_integral_Ioi]

/-- At the removable parameter the logarithmic physical response has mass squared two. -/
theorem cuspConstantPhysicalResponse_half_mass :
    (∫ y, ‖cuspConstantPhysicalResponse (1 / 2 : ℂ) y‖ ^ 2 ∂cuspMeasure 1) = 2 := by
  rw [integral_cuspConstantPhysicalResponse_norm_sq (by norm_num : (0 : ℝ) < (1 / 2 : ℂ).re)]
  exact cuspConstantLogResponse_half_mass

/-- Its ordinary vertical energy at the removable parameter is one. -/
theorem cuspConstantPhysicalResponse_half_energy :
    (∫ y in Ici 1, ‖deriv (cuspConstantPhysicalResponse (1 / 2 : ℂ)) y‖ ^ 2) = 1 := by
  have h := integral_cuspConstantPhysicalResponse_deriv_sq
    (by norm_num : (0 : ℝ) < (1 / 2 : ℂ).re)
  norm_num at h ⊢
  exact h

end GapFamily.Analytic
