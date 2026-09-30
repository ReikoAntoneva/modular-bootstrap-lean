import GapFamily.Analytic.Transform.CosRootGaussian
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

noncomputable section
namespace GapFamily.Analytic.CosRootLaplace
open Set MeasureTheory

/-- The literal half-line inverse-square-root weighted project cosRoot factor. -/
def cosRootHalfLaplaceIntegrand (A z : ℂ) (u : ℝ) : ℂ :=
  ((u ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * Complex.exp (-z * (u : ℂ)) *
    cosRoot (A * (u : ℂ))

/-- The actual entire cosRoot becomes an ordinary cosine after the square substitution. -/
theorem cosRoot_mul_real_sq (A : ℂ) (t : ℝ) :
    cosRoot (A * ((t ^ 2 : ℝ) : ℂ)) = Complex.cos (A ^ (1 / 2 : ℂ) * (t : ℂ)) := by
  have hsq : (A ^ (1 / 2 : ℂ)) ^ (2 : ℕ) = A := by
    simpa only [one_div] using Complex.cpow_ofNat_inv_pow A 2
  calc
    _ = cosRoot ((A ^ (1 / 2 : ℂ) * (t : ℂ)) ^ (2 : ℕ)) := by
      rw [mul_pow, hsq, Complex.ofReal_pow]
    _ = _ := cosRoot_sq _

/-- The actual weighted Jacobian cancels exactly on the open positive half-line. -/
theorem cosRootHalfLaplace_square_jacobian (A z : ℂ) {t : ℝ} (ht : 0 < t) :
    (2 * t) • cosRootHalfLaplaceIntegrand A z (t ^ (2 : ℝ)) =
      (2 : ℂ) * (Complex.exp (-z * (t : ℂ) ^ 2) *
        Complex.cos (A ^ (1 / 2 : ℂ) * (t : ℂ))) := by
  have hp : (t ^ (2 : ℕ)) ^ (-(1 / 2 : ℝ)) = t⁻¹ := by
    rw [Real.rpow_neg (sq_nonneg t), ← Real.sqrt_eq_rpow, Real.sqrt_sq ht.le]
  rw [Real.rpow_two, cosRootHalfLaplaceIntegrand, hp, cosRoot_mul_real_sq,
    Complex.ofReal_pow, Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_ofNat,
    Complex.ofReal_inv]
  have ht0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  field_simp

/-- Ordinary Bochner integrability, valid for every complex A and every Re(z)>0. -/
theorem integrableOn_cosRootHalfLaplaceIntegrand (A : ℂ) {z : ℂ} (hz : 0 < z.re) :
    IntegrableOn (cosRootHalfLaplaceIntegrand A z) (Ioi (0 : ℝ)) := by
  apply (integrableOn_Ioi_comp_rpow_iff (cosRootHalfLaplaceIntegrand A z)
    (by norm_num : (2 : ℝ) ≠ 0)).mp
  have hg := ((integrable_gaussian_cos hz (A ^ (1 / 2 : ℂ))).const_mul (2 : ℂ)).integrableOn (s := Ioi (0 : ℝ))
  apply hg.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have he := cosRootHalfLaplace_square_jacobian A z ht
  simpa only [abs_of_pos (by norm_num : (0 : ℝ) < 2),
    show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one] using he.symm

/-- The actual half-line Gaussian-Laplace factor, with principal complex powers and no
restriction on A. Every integral here is an ordinary Bochner integral. -/
theorem integral_cosRootHalfLaplaceIntegrand (A : ℂ) {z : ℂ} (hz : 0 < z.re) :
    (∫ u : ℝ in Ioi 0, cosRootHalfLaplaceIntegrand A z u) =
      (Real.sqrt Real.pi : ℂ) * z ^ (-(1 / 2 : ℂ)) *
        Complex.exp (-A / (4 * z)) := by
  rw [← integral_comp_rpow_Ioi_of_pos (g := cosRootHalfLaplaceIntegrand A z)
    (by norm_num : (0 : ℝ) < 2)]
  calc
    _ = ∫ t : ℝ in Ioi 0, (2 : ℂ) *
        (Complex.exp (-z * (t : ℂ) ^ 2) *
          Complex.cos (A ^ (1 / 2 : ℂ) * (t : ℂ))) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      simpa only [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one] using
        cosRootHalfLaplace_square_jacobian A z ht
    _ = _ := by
      rw [integral_const_mul, integral_gaussian_cos_Ioi hz]
      have hsq : (A ^ (1 / 2 : ℂ)) ^ (2 : ℕ) = A := by
        simpa only [one_div] using Complex.cpow_ofNat_inv_pow A 2
      rw [hsq]
      ring

end GapFamily.Analytic.CosRootLaplace
