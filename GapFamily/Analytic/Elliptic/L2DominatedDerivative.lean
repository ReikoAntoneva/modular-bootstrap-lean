import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.DominatedConvergence

noncomputable section
namespace GapFamily.Analytic.DominatedL2
open Set Filter MeasureTheory Metric
open scoped Topology
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-- Ordinary squared norm of an actual complex L2 vector. -/
theorem norm_L2_sq_integral (u : Lp ℂ 2 μ) : ‖u‖ ^ 2 = ∫ x, ‖u x‖ ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards with x
  exact real_inner_self_eq_norm_sq (u x)

/-- A common L2 bound on actual pointwise derivatives gives genuine norm differentiability
of the represented L2 family. The derivative vector is the ordinary MemLp quotient class. -/
theorem hasDerivAt_L2_of_dominated_deriv
    {u : ℂ → Lp ℂ 2 μ} {F F' : ℂ → X → ℂ} {z₀ : ℂ} {r : ℝ} {B : X → ℝ}
    (hr : 0 < r)
    (hrep : ∀ z ∈ ball z₀ r, u z =ᵐ[μ] F z)
    (hderiv : ∀ᵐ x ∂μ, ∀ z ∈ ball z₀ r, HasDerivAt (fun w => F w x) (F' z x) z)
    (hbound : ∀ᵐ x ∂μ, ∀ z ∈ ball z₀ r, ‖F' z x‖ ≤ B x)
    (hB : MemLp B 2 μ) (hF' : MemLp (F' z₀) 2 μ) :
    HasDerivAt u (hF'.toLp (F' z₀)) z₀ := by
  let D : Lp ℂ 2 μ := hF'.toLp (F' z₀)
  let Q : ℂ → X → ℂ := fun z x => (z - z₀)⁻¹ * (F z x - F z₀ x) - F' z₀ x
  have hz₀ : z₀ ∈ ball z₀ r := mem_ball_self hr
  have hm (z : ℂ) (hz : z ∈ ball z₀ r) : AEStronglyMeasurable (F z) μ :=
    (Lp.aestronglyMeasurable (u z)).congr (hrep z hz)
  have hball : ∀ᶠ z in 𝓝[≠] z₀, z ∈ ball z₀ r :=
    nhdsWithin_le_nhds (ball_mem_nhds z₀ hr)
  have hi : Tendsto (fun z => ∫ x, ‖Q z x‖ ^ 2 ∂μ) (𝓝[≠] z₀) (𝓝 (0 : ℝ)) := by
    have h := tendsto_integral_filter_of_dominated_convergence (μ := μ) (l := 𝓝[≠] z₀)
      (F := fun z x => ‖Q z x‖ ^ 2) (f := fun _ => (0 : ℝ))
      (fun x => 4 * (B x) ^ 2) ?_ ?_ (hB.integrable_sq.const_mul 4) ?_
    · simpa only [integral_zero] using h
    · filter_upwards [hball] with z hz
      exact ((((hm z hz).sub (hm z₀ hz₀)).const_mul ((z - z₀)⁻¹)).sub
        hF'.aestronglyMeasurable).norm.pow 2
    · filter_upwards [hball, self_mem_nhdsWithin] with z hz hzne
      filter_upwards [hderiv, hbound] with x hd hb
      have hdiff : ‖F z x - F z₀ x‖ ≤ B x * ‖z - z₀‖ :=
        (convex_ball z₀ r).norm_image_sub_le_of_norm_hasDerivWithin_le
          (fun w hw => (hd w hw).hasDerivWithinAt) hb hz₀ hz
      have hn : ‖z - z₀‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hzne)
      have hq : ‖(z - z₀)⁻¹ * (F z x - F z₀ x)‖ ≤ B x := by
        rw [norm_mul, norm_inv]
        calc
          _ ≤ ‖z - z₀‖⁻¹ * (B x * ‖z - z₀‖) :=
            mul_le_mul_of_nonneg_left hdiff (inv_nonneg.mpr (norm_nonneg _))
          _ = B x := by field_simp
      have hb0 : 0 ≤ B x := (norm_nonneg (F' z₀ x)).trans (hb z₀ hz₀)
      have herr : ‖Q z x‖ ≤ 2 * B x :=
        (norm_sub_le _ _).trans (by dsimp [Q] at *; linarith [hb z₀ hz₀])
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      nlinarith [norm_nonneg (Q z x)]
    · filter_upwards [hderiv] with x hx
      have h := (((hx z₀ hz₀).tendsto_slope.sub_const (F' z₀ x)).norm.pow 2)
      simpa only [Q, slope_def_module, smul_eq_mul, sub_self, norm_zero,
        zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using h
  have he (z : ℂ) (hz : z ∈ ball z₀ r) :
      ‖slope u z₀ z - D‖ ^ 2 = ∫ x, ‖Q z x‖ ^ 2 ∂μ := by
    rw [norm_L2_sq_integral]
    apply integral_congr_ae
    rw [slope_def_module]
    filter_upwards [Lp.coeFn_sub ((z - z₀)⁻¹ • (u z - u z₀)) D,
      Lp.coeFn_smul ((z - z₀)⁻¹) (u z - u z₀), Lp.coeFn_sub (u z) (u z₀),
      hrep z hz, hrep z₀ hz₀, hF'.coeFn_toLp] with x hsub hsmul hdiff hzrep hz₀rep hD
    simp only [hsub, hsmul, hdiff, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      hzrep, hz₀rep, hD, D, Q]
  have hsq : Tendsto (fun z => ‖slope u z₀ z - D‖ ^ 2) (𝓝[≠] z₀) (𝓝 (0 : ℝ)) :=
    hi.congr' (hball.mono (fun z hz => (he z hz).symm))
  apply hasDerivAt_iff_tendsto_slope.mpr
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have h := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using h

end GapFamily.Analytic.DominatedL2
