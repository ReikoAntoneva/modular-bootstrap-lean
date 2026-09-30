import GapFamily.Analytic.Cusp.Green.CuspGreenSolutionBasic

/-!
# Outgoing decay for the actual scalar Green solution
-/

noncomputable section

namespace GapFamily.Analytic

open Filter MeasureTheory Set
open scoped Topology

/-- The kernel is an outgoing exponential beyond its source position. -/
theorem cuspGreen_eq_outgoing (t₀ t u : ℝ) {κ : ℂ} (hκ : κ ≠ 0) (htu : u ≤ t) :
    cuspGreen t₀ t u κ = Complex.exp (-κ * t) *
      ((Complex.exp (κ * u) - Complex.exp (-κ * (u - 2*t₀))) / (2 * κ)) := by
  rw [cuspGreen_eq_quotient t₀ t u hκ, abs_of_nonneg (sub_nonneg.mpr htu)]
  push_cast
  rw [show -κ * ((t : ℂ) - u) = -κ * t + κ * u by ring,
    show -κ * ((t : ℂ) + u - 2 * t₀) = -κ * t + -κ * (u - 2 * t₀) by ring,
    Complex.exp_add, Complex.exp_add]
  ring

/-- The whole compact-source solution becomes one outgoing exponential above the support. -/
theorem cuspGreenSolution_eq_outgoing (t₀ T t : ℝ) (hT : t₀ ≤ T) (ht : T ≤ t)
    {κ : ℂ} (hκ : κ ≠ 0) {f : ℝ → ℂ} (hfT : ∀ u, T < u → f u = 0) :
    cuspGreenSolution t₀ κ f t = Complex.exp (-κ * t) *
      (∫ u : ℝ in t₀..T,
        ((Complex.exp (κ * u) - Complex.exp (-κ * (u - 2*t₀))) / (2 * κ)) * f u) := by
  rw [cuspGreenSolution_eq_interval t₀ T t hT κ hfT,
    ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro u hu
  rw [uIcc_of_le hT] at hu
  dsimp only
  rw [cuspGreen_eq_outgoing t₀ t u hκ (hu.2.trans ht)]
  ring

/-- A complex outgoing exponential decays when its spectral parameter has positive real part. -/
theorem cusp_outgoing_exp_tendsto_zero {κ : ℂ} (hκ : 0 < κ.re) :
    Tendsto (fun t : ℝ => Complex.exp (-κ * t)) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  simp only [Complex.norm_exp, Complex.neg_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero]
  exact Real.tendsto_exp_atBot.comp
    (tendsto_id.const_mul_atTop_of_neg (by linarith : -κ.re < 0))

/-- The actual compact-source integral has outgoing decay in the positive-real-part region. -/
theorem cuspGreenSolution_tendsto_zero {f : ℝ → ℂ} (hfc : HasCompactSupport f)
    (t₀ : ℝ) {κ : ℂ} (hκ : 0 < κ.re) :
    Tendsto (cuspGreenSolution t₀ κ f) atTop (𝓝 0) := by
  have hk : κ ≠ 0 := by intro hz; simp [hz] at hκ
  obtain ⟨T, hT, hfT⟩ := exists_cuspSource_cutoff hfc t₀
  have h := (cusp_outgoing_exp_tendsto_zero hκ).mul_const
    (∫ u : ℝ in t₀..T,
      ((Complex.exp (κ * u) - Complex.exp (-κ * (u - 2*t₀))) / (2 * κ)) * f u)
  simp only [zero_mul] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop T] with t ht
  exact (cuspGreenSolution_eq_outgoing t₀ T t hT.le ht hk hfT).symm

end GapFamily.Analytic
