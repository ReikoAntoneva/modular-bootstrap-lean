import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.MeasureTheory.Integral.DominatedConvergence

noncomputable section
namespace GapFamily.Analytic.DominatedL1
open Set Filter MeasureTheory Metric
open scoped Topology
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-- A common integrable bound on actual pointwise derivatives gives norm differentiability
of the represented L1 family. The derivative is the ordinary MemLp quotient class. -/
theorem hasDerivAt_L1_of_dominated_deriv
    {u : ℂ → Lp ℂ 1 μ} {F F' : ℂ → X → ℂ} {z₀ : ℂ} {r : ℝ} {B : X → ℝ}
    (hr : 0 < r)
    (hrep : ∀ z ∈ ball z₀ r, u z =ᵐ[μ] F z)
    (hderiv : ∀ᵐ x ∂μ, ∀ z ∈ ball z₀ r, HasDerivAt (fun w => F w x) (F' z x) z)
    (hbound : ∀ᵐ x ∂μ, ∀ z ∈ ball z₀ r, ‖F' z x‖ ≤ B x)
    (hB : MemLp B 1 μ) (hF' : MemLp (F' z₀) 1 μ) :
    HasDerivAt u (hF'.toLp (F' z₀)) z₀ := by
  let D : Lp ℂ 1 μ := hF'.toLp (F' z₀)
  let Q : ℂ → X → ℂ := fun z x => (z - z₀)⁻¹ * (F z x - F z₀ x) - F' z₀ x
  have hz₀ : z₀ ∈ ball z₀ r := mem_ball_self hr
  have hm (z : ℂ) (hz : z ∈ ball z₀ r) : AEStronglyMeasurable (F z) μ :=
    (Lp.aestronglyMeasurable (u z)).congr (hrep z hz)
  have hball : ∀ᶠ z in 𝓝[≠] z₀, z ∈ ball z₀ r :=
    nhdsWithin_le_nhds (ball_mem_nhds z₀ hr)
  have hi : Tendsto (fun z => ∫ x, ‖Q z x‖ ∂μ) (𝓝[≠] z₀) (𝓝 (0 : ℝ)) := by
    have h := tendsto_integral_filter_of_dominated_convergence (μ := μ) (l := 𝓝[≠] z₀)
      (F := fun z x => ‖Q z x‖) (f := fun _ => (0 : ℝ))
      (fun x => 2 * B x) ?_ ?_ ((memLp_one_iff_integrable.mp hB).const_mul 2) ?_
    · simpa only [integral_zero] using h
    · filter_upwards [hball] with z hz
      exact ((((hm z hz).sub (hm z₀ hz₀)).const_mul ((z - z₀)⁻¹)).sub
        hF'.aestronglyMeasurable).norm
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
      rw [norm_norm]
      exact (norm_sub_le _ _).trans (by dsimp [Q] at *; linarith [hb z₀ hz₀])
    · filter_upwards [hderiv] with x hx
      have h := ((hx z₀ hz₀).tendsto_slope.sub_const (F' z₀ x)).norm
      simpa only [Q, slope_def_module, smul_eq_mul, sub_self, norm_zero] using h
  have he (z : ℂ) (hz : z ∈ ball z₀ r) :
      ‖slope u z₀ z - D‖ = ∫ x, ‖Q z x‖ ∂μ := by
    rw [L1.norm_eq_integral_norm]
    apply integral_congr_ae
    rw [slope_def_module]
    filter_upwards [Lp.coeFn_sub ((z - z₀)⁻¹ • (u z - u z₀)) D,
      Lp.coeFn_smul ((z - z₀)⁻¹) (u z - u z₀), Lp.coeFn_sub (u z) (u z₀),
      hrep z hz, hrep z₀ hz₀, hF'.coeFn_toLp] with x hsub hsmul hdiff hzrep hz₀rep hD
    simp only [hsub, hsmul, hdiff, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      hzrep, hz₀rep, hD, D, Q]
  apply hasDerivAt_iff_tendsto_slope.mpr
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  exact hi.congr' (hball.mono (fun z hz => (he z hz).symm))

end GapFamily.Analytic.DominatedL1
