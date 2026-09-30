import BTZEntropy.Comparison.SpinReferenceMeasure
import BTZEntropy.Comparison.SpinComplexSeries
import BTZEntropy.Analytic.ReferenceInversionTransform
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.Convex

/-!
# Poisson identity on the complex thermal half-plane

Both sides are actual transforms: the weighted integer-spin physical measure
and the locally normally convergent modular-image series. Their proved real
Poisson identity extends by the analytic identity theorem. The central image
is identified with the actual continuous-spin reference transform.
-/

noncomputable section

open Filter Set
open scoped Topology

namespace BTZEntropy

private theorem analytic_halfPlane_identity (f g : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f {z : ℂ | 0 < z.re})
    (hg : AnalyticOnNhd ℂ g {z : ℂ | 0 < z.re})
    (hreal : ∀ x : ℝ, 0 < x → f x = g x)
    {z : ℂ} (hz : 0 < z.re) : f z = g z := by
  have hcast : Tendsto ((↑) : ℝ → ℂ) (𝓝[≠] 1) (𝓝[≠] 1) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · exact tendsto_nhdsWithin_of_tendsto_nhds Complex.continuous_ofReal.continuousAt
    · exact eventually_nhdsWithin_iff.mpr (Eventually.of_forall fun t ht =>
        Complex.ofReal_ne_one.mpr ht)
  have hfreq : ∃ᶠ w in 𝓝[≠] (1 : ℂ), f w = g w := by
    apply hcast.frequently
    apply ((Eventually.filter_mono nhdsWithin_le_nhds) ?_).frequently
    exact (eventually_gt_nhds (show (0 : ℝ) < 1 by norm_num)).mono fun x hx => hreal x hx
  exact hf.eqOn_of_preconnected_of_frequently_eq hg
    (convex_halfSpace_re_gt (0 : ℝ)).isPreconnected (by simp) hfreq hz

private theorem re_scaledThermal_pos {z : ℂ} (hz : 0 < z.re) :
    0 < (z / (2 * (Real.pi : ℂ))).re := by
  rw [show (2 * (Real.pi : ℂ)) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; rfl,
    Complex.div_ofReal_re]
  exact div_pos hz (by positivity)

/-- The central modular image equals the actual complex continuum reference. -/
theorem complexSpinImage_zero_eq_reference {a : ℝ} {z : ℂ}
    (ha : 2 ≤ a) (hz : 0 < z.re) :
    complexSpinImage a (z / (2 * (Real.pi : ℂ))) 0 =
      complexReferencePrimaryTransform a z := by
  rw [complexSpinImage_zero a (re_scaledThermal_pos hz), complexReferencePrimaryTransform_eq ha hz]
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hz0 : z ≠ 0 := by intro h; simp [h] at hz
  have h0 : (z / (2 * (Real.pi : ℂ)))⁻¹ = 2 * (Real.pi : ℂ) / z := by field_simp
  have h1 : 2 * (Real.pi : ℂ) * a / (z / (2 * (Real.pi : ℂ))) =
      4 * (Real.pi : ℂ) ^ 2 * a / z := by field_simp; ring
  have h2 : -2 * (Real.pi : ℂ) / (z / (2 * (Real.pi : ℂ))) =
      -4 * (Real.pi : ℂ) ^ 2 / z := by field_simp; ring
  rw [h0, h1, h2]

/-- Exact Poisson summation for the same physical integer-spin Laplace integral
throughout the right half-plane. -/
theorem integerSpinPrimaryComplexTransform_eq_images {a : ℝ} (ha : 2 ≤ a)
    {z : ℂ} (hz : 0 < z.re) :
    integerSpinPrimaryComplexTransform a z =
      complexSpinImageSum a (z / (2 * (Real.pi : ℂ))) := by
  apply analytic_halfPlane_identity _ _
    (analyticOnNhd_integerSpinPrimaryComplexTransform ha) ?_ ?_ hz
  · intro w hw
    exact AnalyticAt.comp (f := fun v : ℂ => v / (2 * (Real.pi : ℂ))) (x := w)
      (analyticOnNhd_complexSpinImageSum (show 0 ≤ a by linarith)
        (w / (2 * (Real.pi : ℂ))) (re_scaledThermal_pos hw))
      analyticAt_id.div_const
  · intro β hβ
    let y := β / (2 * Real.pi)
    have hy : 0 < y := div_pos hβ (by positivity)
    have hβeq : 2 * Real.pi * y = β := by dsimp [y]; field_simp
    have hzcast : (β : ℂ) / (2 * (Real.pi : ℂ)) = (y : ℂ) := by
      dsimp [y]
      push_cast
      rfl
    rw [hzcast, ← hβeq, integerSpinPrimaryComplexTransform_real ha hy,
      complexSpinImageSum_ofReal hy, ← integerSpinReferenceThermal_eq_images ha hy]
    exact (mul_div_cancel_left₀ _ (Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.2 hy)))).symm

/-- Exact noncentral-image error of the physical integer-spin transform. -/
theorem integerSpinPrimaryComplexTransform_sub_reference {a : ℝ} (ha : 2 ≤ a)
    {z : ℂ} (hz : 0 < z.re) :
    integerSpinPrimaryComplexTransform a z - complexReferencePrimaryTransform a z =
      complexSpinTailSum a (z / (2 * (Real.pi : ℂ))) := by
  rw [integerSpinPrimaryComplexTransform_eq_images ha hz,
    complexSpinImageSum_eq_central_add_tail (show 0 ≤ a by linarith) (re_scaledThermal_pos hz),
    complexSpinImage_zero_eq_reference ha hz]
  ring

end BTZEntropy
