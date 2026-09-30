import GapFamily.Analytic.Cusp.Fourier.CuspFourierCutoffCommutator

noncomputable section

namespace GapFamily.Analytic.LaplacianCovariance

open Set Filter
open scoped Topology ContDiff
open CuspFourierCutoff

/-- The literal complex power has its ordinary second real derivative at every
positive height, for all complex exponents, including zero and one. -/
theorem deriv2_power (s : ℂ) {y : ℝ} (hy : 0 < y) :
    deriv (deriv (fun t : ℝ => (t : ℂ) ^ s)) y =
      s * (s - 1) * (y : ℂ) ^ (s - 2) := by
  have heq : deriv (fun t : ℝ => (t : ℂ) ^ s) =ᶠ[𝓝 y]
      (fun t : ℝ => s * (t : ℂ) ^ (s - 1)) := by
    filter_upwards [Ioi_mem_nhds hy] with t ht using (hasDerivAt_power s ht).deriv
  have hd := ((hasDerivAt_power (s - 1) hy).const_mul s).congr_of_eventuallyEq heq
  rw [hd.deriv, show s - 1 - 1 = s - 2 by ring]
  ring

/-- The radial power cancels exactly against the spectral eigenvalue. -/
theorem power_eigenvalue (s : ℂ) {y : ℝ} (hy : 0 < y) :
    -(y : ℂ) ^ 2 * deriv (deriv (fun t : ℝ => (t : ℂ) ^ s)) y -
      s * (1 - s) * (y : ℂ) ^ s = 0 := by
  have hp : (y : ℂ) ^ 2 * (y : ℂ) ^ (s - 2) = (y : ℂ) ^ s := by
    rw [sq_mul_power _ hy, sub_add_cancel]
  rw [deriv2_power s hy]
  linear_combination -s * (s - 1) * hp

/-- The direct zero-energy Fourier seed satisfies the literal coordinate PDE.
This is an ordinary pointwise identity, not an operator-domain assertion. -/
theorem zeroEnergy_coordinate_residual (J : ℤ) (s : ℂ) (x : ℝ)
    {y : ℝ} (hy : 0 < y) :
    -(y : ℂ) ^ 2 *
        (deriv (deriv (fun t : ℝ => (y : ℂ) ^ s * cuspFourierMode J t)) x +
          deriv (deriv (fun t : ℝ => (t : ℂ) ^ s * cuspFourierMode J x)) y) -
      s * (1 - s) * (y : ℂ) ^ s * cuspFourierMode J x =
      (2 * (Real.pi : ℂ) * (J : ℂ)) ^ 2 *
        (y : ℂ) ^ (s + 2) * cuspFourierMode J x := by
  rw [deriv_const_mul_field', deriv_const_mul_field,
    deriv_mul_const_field', deriv_mul_const_field, deriv2_mode]
  have hc := power_eigenvalue s hy
  have hp := sq_mul_power s hy
  linear_combination
    cuspFourierMode J x * hc +
      (2 * (Real.pi : ℂ) * (J : ℂ)) ^ 2 * cuspFourierMode J x * hp

end GapFamily.Analytic.LaplacianCovariance
