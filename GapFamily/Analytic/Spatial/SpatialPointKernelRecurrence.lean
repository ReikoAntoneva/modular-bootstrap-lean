import GapFamily.Analytic.Spatial.SpatialPointParameterDeriv
import GapFamily.Analytic.Spatial.SpatialRadialPower

noncomputable section
namespace GapFamily.Analytic.SpatialPoint
open scoped ContDiff ComplexConjugate

/-- The reflected-point denominator gives exactly the same principal complex
power, since its base is positive on the upper half-plane. -/
theorem pointKernel_eq_reflected_power (s : ℂ) {z w : ℂ}
    (hz : 0 < z.im) (hw : 0 < w.im) :
    pointKernel s z w = (1 / 4 : ℂ) *
      ((4 * z.im * w.im / Complex.normSq (z - conj w) : ℝ) : ℂ) ^ s := by
  have he : 4 * z.im * w.im / Complex.normSq (z - conj w) =
      (pointParameter z w)⁻¹ := by
    rw [pointParameter_eq_normSq_sub_conj hz hw, inv_div]
  rw [he, Complex.ofReal_inv,
    Complex.inv_cpow_ofReal_nonneg (pointParameter_pos hz hw).le,
    pointKernel, Complex.cpow_neg]

/-- The normalized point-kernel recurrence for the actual ordinary negative
hyperbolic Laplacian. It holds for every complex exponent. -/
theorem pointKernel_laplacian_recurrence (s : ℂ) {z w : ℂ}
    (hz : 0 < z.im) (hw : 0 < w.im) :
    LaplacianCovariance.ordinaryHyperbolicLaplacian
        (fun v : ℂ => pointKernel s v w) z -
      s * (1 - s) * pointKernel s z w =
      s ^ 2 * pointKernel (s + 1) z w := by
  change LaplacianCovariance.ordinaryHyperbolicLaplacian
      (fun v : ℂ => radialPower s (pointParameter v w)) z -
    s * (1 - s) * radialPower s (pointParameter z w) =
    s ^ 2 * radialPower (s + 1) (pointParameter z w)
  rw [ordinaryHyperbolicLaplacian_comp_pointParameter hz hw
    ((radialPower_contDiffAt s (pointParameter_pos hz hw)).of_le (by norm_num))]
  exact radialPower_recurrence s (pointParameter_pos hz hw)

end GapFamily.Analytic.SpatialPoint
