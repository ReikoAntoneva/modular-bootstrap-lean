import GapFamily.Analytic.Cusp.Scalar.CuspConstantResponsePhysical
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! Analytic dependence and ordinary outgoing decay of the actual constant-source response. -/
noncomputable section
namespace GapFamily.Analytic
open Set Filter
open scoped Topology

/-- The physical removable value is holomorphic; only the opposite root is excluded. -/
theorem cuspConstantLogResponse_analyticAt (t : ℝ) {κ : ℂ}
    (hκ : κ ≠ -(1 / 2 : ℂ)) :
    AnalyticAt ℂ (fun z => cuspConstantLogResponse z t) κ := by
  have hf : Differentiable ℂ (fun z : ℂ => Complex.exp (-z * (t : ℂ))) := by fun_prop
  have hs : Differentiable ℂ (dslope (fun z : ℂ => Complex.exp (-z * (t : ℂ))) (1 / 2)) :=
    differentiableOn_univ.mp ((Complex.differentiableOn_dslope (c := (1 / 2 : ℂ))
      univ_mem).mpr hf.differentiableOn)
  exact (hs.analyticAt κ).neg.div (by fun_prop) (cuspConstant_add_half_ne_zero hκ)

/-- The continued response tends to its exponential-polynomial value at the physical root. -/
theorem cuspConstantLogResponse_tendsto_half (t : ℝ) :
    Tendsto (fun κ => cuspConstantLogResponse κ t) (𝓝 (1 / 2 : ℂ))
      (𝓝 ((t : ℂ) * Complex.exp (-(t : ℂ) / 2))) := by
  simpa only [cuspConstantLogResponse_half] using (cuspConstantLogResponse_analyticAt t
    (show (1 / 2 : ℂ) ≠ -(1 / 2 : ℂ) by norm_num)).continuousAt.tendsto

/-- The literal quotient has the same actual punctured limit. -/
theorem cuspConstantLogResponse_quotient_tendsto_half (t : ℝ) :
    Tendsto (fun κ : ℂ => (Complex.exp (-κ * (t : ℂ)) - Complex.exp (-(t : ℂ) / 2)) /
      ((1 / 4 : ℂ) - κ ^ 2)) (𝓝[≠] (1 / 2 : ℂ))
      (𝓝 ((t : ℂ) * Complex.exp (-(t : ℂ) / 2))) := by
  apply ((cuspConstantLogResponse_tendsto_half t).mono_left nhdsWithin_le_nhds).congr'
  filter_upwards [self_mem_nhdsWithin,
    (eventually_ne_nhds (show (1 / 2 : ℂ) ≠ -(1 / 2 : ℂ) by norm_num)).filter_mono
      nhdsWithin_le_nhds] with κ hp hm
  exact cuspConstantLogResponse_eq_quotient hp hm t

/-- Smoothness in the ordinary real logarithmic coordinate includes the removable root. -/
theorem cuspConstantLogResponse_contDiff {κ : ℂ} (hκ : κ ≠ -(1 / 2 : ℂ)) :
    ContDiff ℝ ⊤ (cuspConstantLogResponse κ) := by
  have hc : ContDiff ℝ ⊤ (fun t : ℝ => (t : ℂ)) := Complex.ofRealCLM.contDiff
  by_cases hp : κ = (1 / 2 : ℂ)
  · subst κ
    have heq : cuspConstantLogResponse (1 / 2 : ℂ) =
        (fun t : ℝ => (t : ℂ) * Complex.exp (-(t : ℂ) / 2)) :=
      funext cuspConstantLogResponse_half
    rw [heq]
    fun_prop
  · have heq : cuspConstantLogResponse κ = (fun t : ℝ =>
        (Complex.exp (-κ * (t : ℂ)) - Complex.exp (-(t : ℂ) / 2)) /
          ((1 / 4 : ℂ) - κ ^ 2)) := funext (cuspConstantLogResponse_eq_quotient hp hκ)
    rw [heq]
    fun_prop

/-- The elementary complex outgoing exponential really tends to zero. -/
theorem cuspConstantExp_tendsto_zero {κ : ℂ} (hκ : 0 < κ.re) :
    Tendsto (fun t : ℝ => Complex.exp (-κ * (t : ℂ))) atTop (𝓝 0) := by
  simpa [Complex.tendsto_exp_nhds_zero_iff] using
    tendsto_const_nhds.neg_mul_atTop (show (-κ).re < 0 by simpa using hκ) tendsto_id

/-- The actual noncompact profile decays in the positive spectral half-plane. -/
theorem cuspConstantLogResponse_tendsto_zero {κ : ℂ} (hκ : 0 < κ.re) :
    Tendsto (cuspConstantLogResponse κ) atTop (𝓝 0) := by
  have hm : κ ≠ -(1 / 2 : ℂ) := by
    intro h; subst κ; norm_num at hκ
  by_cases hp : κ = (1 / 2 : ℂ)
  · subst κ
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    have h := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 (1 / 2) (by norm_num)
    apply h.congr'
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    simp only [cuspConstantLogResponse_half, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg ht, Complex.norm_exp, Real.rpow_one]
    have he : (-(t : ℂ) / 2).re = -t / 2 := by norm_num
    rw [he]
    congr 1
    congr 1
    ring
  · have heq : cuspConstantLogResponse κ = (fun t : ℝ =>
        (Complex.exp (-κ * (t : ℂ)) - Complex.exp (-(t : ℂ) / 2)) /
          ((1 / 4 : ℂ) - κ ^ 2)) := funext (cuspConstantLogResponse_eq_quotient hp hm)
    rw [heq]
    have hh : Tendsto (fun t : ℝ => Complex.exp (-(t : ℂ) / 2)) atTop (𝓝 0) := by
      convert cuspConstantExp_tendsto_zero (κ := (1 / 2 : ℂ)) (by norm_num) using 1
      ext t
      congr 1
      ring
    simpa using ((cuspConstantExp_tendsto_zero hκ).sub hh).div_const ((1 / 4 : ℂ) - κ ^ 2)

/-- The actual lifted physical response is also holomorphic away from the opposite root. -/
theorem cuspConstantPhysicalResponse_analyticAt (y : ℝ) {κ : ℂ}
    (hκ : κ ≠ -(1 / 2 : ℂ)) :
    AnalyticAt ℂ (fun z => cuspConstantPhysicalResponse z y) κ := by
  simp only [cuspConstantPhysicalResponse, cuspLift, Complex.real_smul]
  exact analyticAt_const.mul (cuspConstantLogResponse_analyticAt (Real.log y) hκ)

/-- The removable physical parameter limit is the ordinary real logarithm. -/
theorem cuspConstantPhysicalResponse_tendsto_half {y : ℝ} (hy : 0 < y) :
    Tendsto (fun κ => cuspConstantPhysicalResponse κ y) (𝓝 (1 / 2 : ℂ))
      (𝓝 (Real.log y : ℂ)) := by
  simpa only [cuspConstantPhysicalResponse_half hy] using
    (cuspConstantPhysicalResponse_analyticAt y
      (show (1 / 2 : ℂ) ≠ -(1 / 2 : ℂ) by norm_num)).continuousAt.tendsto

/-- The literal physical power quotient has the asserted punctured logarithm limit. -/
theorem cuspConstantPhysicalResponse_quotient_tendsto_half {y : ℝ} (hy : 0 < y) :
    Tendsto (fun κ : ℂ => ((y : ℂ) ^ ((1 / 2 : ℂ) - κ) - 1) / (1 / 4 - κ ^ 2))
      (𝓝[≠] (1 / 2 : ℂ)) (𝓝 (Real.log y : ℂ)) := by
  apply ((cuspConstantPhysicalResponse_tendsto_half hy).mono_left nhdsWithin_le_nhds).congr'
  filter_upwards [self_mem_nhdsWithin,
    (eventually_ne_nhds (show (1 / 2 : ℂ) ≠ -(1 / 2 : ℂ) by norm_num)).filter_mono
      nhdsWithin_le_nhds] with κ hp hm
  exact cuspConstantPhysicalResponse_eq_quotient hm hp hy

end GapFamily.Analytic
