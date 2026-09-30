import GapFamily.Analytic.Cusp.Green.CuspGreenSolutionBasic

/-! Explicit compact-position bounds for the actual half-line Green integral. -/

noncomputable section
namespace GapFamily.Analytic
open MeasureTheory Set

/-- The finite integral gives a bound uniform through the removable threshold. -/
theorem norm_cuspGreen_le (t₀ t u : ℝ) (ht : t₀ ≤ t) (hu : t₀ ≤ u) (κ : ℂ) :
    ‖cuspGreen t₀ t u κ‖ ≤
      (min t u - t₀) * Real.exp (‖κ‖ * (t + u - 2 * t₀)) := by
  have hab : |t - u| ≤ t + u - 2 * t₀ := by
    apply abs_le.mpr
    constructor <;> linarith
  have hlen : t + u - 2 * t₀ - |t - u| = 2 * (min t u - t₀) := by
    rcases le_total t u with h | h
    · rw [min_eq_left h, abs_of_nonpos (sub_nonpos.mpr h)]; ring
    · rw [min_eq_right h, abs_of_nonneg (sub_nonneg.mpr h)]; ring
  have hi : ‖∫ v : ℝ in |t - u|..(t + u - 2 * t₀), Complex.exp (-κ * v)‖ ≤
      Real.exp (‖κ‖ * (t + u - 2 * t₀)) * |t + u - 2 * t₀ - abs (t - u)| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro v hv
    rw [uIoc_of_le hab] at hv
    have hv0 : 0 ≤ v := (abs_nonneg _).trans hv.1.le
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    calc
      (-κ * (v : ℂ)).re ≤ ‖-κ * (v : ℂ)‖ := Complex.re_le_norm _
      _ = ‖κ‖ * v := by simp [abs_of_nonneg hv0]
      _ ≤ ‖κ‖ * (t + u - 2 * t₀) := mul_le_mul_of_nonneg_left hv.2 (norm_nonneg _)
  unfold cuspGreen
  rw [norm_div, Complex.norm_ofNat]
  rw [abs_of_nonneg (sub_nonneg.mpr hab), hlen] at hi
  nlinarith

/-- Uniform scalar-kernel control on a finite observation/source collar and a parameter disk. -/
theorem norm_cuspGreen_on_collar_le (t₀ T U R t u : ℝ) (κ : ℂ)
    (ht : t₀ ≤ t) (htT : t ≤ T) (hu : t₀ ≤ u) (huU : u ≤ U) (hκ : ‖κ‖ ≤ R) :
    ‖cuspGreen t₀ t u κ‖ ≤
      (T - t₀) * Real.exp (R * (T + U - 2 * t₀)) := by
  have hR : 0 ≤ R := (norm_nonneg _).trans hκ
  have hlen : 0 ≤ t + u - 2 * t₀ := by linarith
  have hmin : 0 ≤ min t u - t₀ := sub_nonneg.mpr (le_min ht hu)
  calc
    _ ≤ (min t u - t₀) * Real.exp (‖κ‖ * (t + u - 2 * t₀)) :=
      norm_cuspGreen_le t₀ t u ht hu κ
    _ ≤ (T - t₀) * Real.exp (R * (T + U - 2 * t₀)) := by
      apply mul_le_mul
      · exact sub_le_sub_right ((min_le_left _ _).trans htT) _
      · apply Real.exp_le_exp.mpr
        exact (mul_le_mul_of_nonneg_right hκ hlen).trans
          (mul_le_mul_of_nonneg_left (by linarith) hR)
      · positivity
      · linarith

/-- An explicit uniform bound for a compact-source response on an observation collar.
The source norm is its genuine ordinary half-line L¹ integral. -/
theorem norm_cuspGreenSolution_on_collar_le (t₀ T U R t : ℝ) (κ : ℂ)
    (ht : t₀ ≤ t) (htT : t ≤ T) (hκ : ‖κ‖ ≤ R)
    {f : ℝ → ℂ} (hf : Continuous f) (hfc : HasCompactSupport f)
    (hfU : ∀ u : ℝ, U < u → f u = 0) :
    ‖cuspGreenSolution t₀ κ f t‖ ≤
      ((T - t₀) * Real.exp (R * (T + U - 2 * t₀))) *
        ∫ u : ℝ in Ioi t₀, ‖f u‖ := by
  unfold cuspGreenSolution
  calc
    _ ≤ ∫ u : ℝ in Ioi t₀,
        ((T - t₀) * Real.exp (R * (T + U - 2 * t₀))) * ‖f u‖ := by
      apply norm_integral_le_of_norm_le
        (((hf.integrable_of_hasCompactSupport hfc).norm.integrableOn).const_mul _)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      by_cases huU : u ≤ U
      · rw [norm_mul]
        exact mul_le_mul_of_nonneg_right
          (norm_cuspGreen_on_collar_le t₀ T U R t u κ ht htT hu.le huU hκ)
          (norm_nonneg _)
      · simp [hfU u (lt_of_not_ge huU)]
    _ = _ := integral_const_mul _ _

end GapFamily.Analytic
