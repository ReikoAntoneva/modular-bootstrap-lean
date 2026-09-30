import BTZEntropy.Analytic.ReferenceInversionMeasure
import BTZEntropy.Analytic.ReferenceInversionMoment
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.CauchyIntegral

/-! Holomorphy of the actual weighted Laplace integral. Nonnegative energy
and all positive thermal moments supply an integrable derivative bound in a
neighborhood of every point of the right half-plane. -/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

namespace BTZEntropy

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

omit [MeasurableSpace α] in
/-- The norm of the weighted complex Laplace integrand is its absolute real
thermal integrand at the real part of the parameter. -/
theorem norm_weightedComplexLaplace_integrand (energy weight : α → ℝ) (z : ℂ) (q : α) :
    ‖(weight q : ℂ) * Complex.exp (-z * energy q)‖ =
      ‖weight q * Real.exp (-z.re * energy q)‖ := by
  rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_exp, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  congr 1
  simp [Complex.mul_re]

/-- A single real thermal moment gives integrability on its vertical line. -/
theorem integrable_weightedComplexLaplace_integrand
    {energy weight : α → ℝ} (he : Measurable energy) (hw : Measurable weight)
    {z : ℂ} (hthermal : Integrable (fun q => weight q * Real.exp (-z.re * energy q)) μ) :
    Integrable (fun q => (weight q : ℂ) * Complex.exp (-z * energy q)) μ := by
  apply hthermal.norm.mono'
  · apply Measurable.aestronglyMeasurable
    fun_prop
  · exact Eventually.of_forall fun q => (norm_weightedComplexLaplace_integrand energy weight z q).le

/-- The first derivative is the genuine integral of the energy-weighted
Laplace kernel. All domination comes from a smaller positive thermal exponent. -/
theorem hasDerivAt_weightedComplexLaplace
    {energy weight : α → ℝ} (he : Measurable energy) (hw : Measurable weight)
    (henergy : ∀ᵐ q ∂μ, 0 ≤ energy q)
    (hthermal : ∀ β : ℝ, 0 < β →
      Integrable (fun q => weight q * Real.exp (-β * energy q)) μ)
    {z : ℂ} (hz : 0 < z.re) :
    HasDerivAt (weightedComplexLaplace μ energy weight)
      (∫ q, (weight q : ℂ) * (-energy q : ℂ) * Complex.exp (-z * energy q) ∂μ) z := by
  let β : ℝ := z.re / 2
  have hβ : 0 < β := by dsimp [β]; positivity
  let F : ℂ → α → ℂ := fun w q => (weight q : ℂ) * Complex.exp (-w * energy q)
  let F' : ℂ → α → ℂ := fun w q =>
    (weight q : ℂ) * (-energy q : ℂ) * Complex.exp (-w * energy q)
  let majorant : α → ℝ := fun q => |weight q| * energy q * Real.exp (-β * energy q)
  have hs : {w : ℂ | β < w.re} ∈ 𝓝 z :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by dsimp [β]; linarith)
  have hmeas : ∀ᶠ w : ℂ in 𝓝 z, AEStronglyMeasurable (F w) μ := by
    apply Eventually.of_forall
    intro w
    apply Measurable.aestronglyMeasurable
    dsimp [F]
    fun_prop
  have hint : Integrable (F z) μ :=
    integrable_weightedComplexLaplace_integrand he hw (hthermal z.re hz)
  have hdmeas : AEStronglyMeasurable (F' z) μ := by
    apply Measurable.aestronglyMeasurable
    dsimp [F']
    fun_prop
  have hmajorant : Integrable majorant μ := by
    simpa [majorant] using integrable_abs_weight_thermalMoment he hw henergy hβ
      (hthermal (β / 2) (by positivity)) 1
  have hbound : ∀ᵐ q ∂μ, ∀ w ∈ {w : ℂ | β < w.re}, ‖F' w q‖ ≤ majorant q := by
    filter_upwards [henergy] with q hq
    intro w hwβ
    dsimp [F', majorant]
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      norm_neg, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hq, Complex.norm_exp]
    have hre : (-w * (energy q : ℂ)).re = -w.re * energy q := by simp [Complex.mul_re]
    rw [hre]
    apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
    exact mul_le_mul_of_nonneg_right (neg_le_neg hwβ.le) hq
  have hdiff : ∀ᵐ q ∂μ, ∀ w ∈ {w : ℂ | β < w.re},
      HasDerivAt (fun s => F s q) (F' w q) w := by
    apply Eventually.of_forall
    intro q w hwβ
    dsimp [F, F']
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      ((((hasDerivAt_id w).neg).mul_const (energy q : ℂ)).cexp).const_mul (weight q : ℂ)
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le hs hmeas hint hdmeas
    hbound hmajorant hdiff).2

/-- The literal weighted Laplace transform is complex differentiable on the
right half-plane. -/
theorem differentiableOn_weightedComplexLaplace
    {energy weight : α → ℝ} (he : Measurable energy) (hw : Measurable weight)
    (henergy : ∀ᵐ q ∂μ, 0 ≤ energy q)
    (hthermal : ∀ β : ℝ, 0 < β →
      Integrable (fun q => weight q * Real.exp (-β * energy q)) μ) :
    DifferentiableOn ℂ (weightedComplexLaplace μ energy weight) {z : ℂ | 0 < z.re} := by
  intro z hz
  exact (hasDerivAt_weightedComplexLaplace he hw henergy hthermal hz).differentiableAt.differentiableWithinAt

/-- Analytic continuation may be applied to this same measure integral;
analyticity is a proved consequence of thermal moments. -/
theorem analyticOnNhd_weightedComplexLaplace
    {energy weight : α → ℝ} (he : Measurable energy) (hw : Measurable weight)
    (henergy : ∀ᵐ q ∂μ, 0 ≤ energy q)
    (hthermal : ∀ β : ℝ, 0 < β →
      Integrable (fun q => weight q * Real.exp (-β * energy q)) μ) :
    AnalyticOnNhd ℂ (weightedComplexLaplace μ energy weight) {z : ℂ | 0 < z.re} :=
  (differentiableOn_weightedComplexLaplace he hw henergy hthermal).analyticOnNhd
    (isOpen_lt continuous_const Complex.continuous_re)

end BTZEntropy
