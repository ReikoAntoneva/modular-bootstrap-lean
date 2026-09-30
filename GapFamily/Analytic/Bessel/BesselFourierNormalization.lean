import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

noncomputable section
namespace GapFamily.Analytic.BesselCoshOrder

/-- The reciprocal Gaussian transform has the literal positive Fourier-Bessel argument. -/
theorem sqrt_fourier_argument {y n : ℝ} (hy : 0 < y) (hn : 0 < n) :
    Real.sqrt (y ^ 2 * (Real.pi ^ 2 * n ^ 2)) = Real.pi * n * y := by
  rw [show y ^ 2 * (Real.pi ^ 2 * n ^ 2) = (Real.pi * n * y) ^ 2 by ring]
  exact Real.sqrt_sq (by positivity)

/-- The positive Mellin scaling parameter is exactly the frequency-to-height ratio. -/
theorem sqrt_fourier_scale {y n : ℝ} (hy : 0 < y) (hn : 0 < n) :
    Real.sqrt ((Real.pi ^ 2 * n ^ 2) / y ^ 2) = Real.pi * n / y := by
  rw [show (Real.pi ^ 2 * n ^ 2) / y ^ 2 = (Real.pi * n / y) ^ 2 by
    rw [div_pow, mul_pow]]
  exact Real.sqrt_sq (by positivity)

/-- The real nonnegative square root agrees with the principal complex half power. -/
theorem ofReal_sqrt_eq_cpow_half {x : ℝ} (hx : 0 ≤ x) :
    (Real.sqrt x : ℂ) = (x : ℂ) ^ (1 / 2 : ℂ) := by
  rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow hx]
  norm_num

/-- The exact Gamma-Gaussian and Mellin factors simplify to the Fourier-Bessel coefficient.
The arbitrary denominator g is not required to be nonzero. -/
theorem fourier_mellin_prefactor (s g : ℂ) {y n : ℝ} (hy : 0 < y) (hn : 0 < n) :
    (y : ℂ) ^ s / g * (Real.sqrt Real.pi : ℂ) *
        (2 * (Real.sqrt ((Real.pi ^ 2 * n ^ 2) / y ^ 2) : ℂ) ^ (s - 1 / 2)) =
      2 * (Real.pi : ℂ) ^ s / g * (n : ℂ) ^ (s - 1 / 2) * (Real.sqrt y : ℂ) := by
  have hyn : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy.ne'
  have hpn : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hyp : (y : ℂ) ^ (s - 1 / 2) ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hyn)
  have hys : (y : ℂ) ^ s = (y : ℂ) ^ (s - 1 / 2) * (y : ℂ) ^ (1 / 2 : ℂ) := by
    rw [← Complex.cpow_add _ _ hyn]
    congr 1
    ring
  have hps : (Real.pi : ℂ) ^ s =
      (Real.pi : ℂ) ^ (s - 1 / 2) * (Real.pi : ℂ) ^ (1 / 2 : ℂ) := by
    rw [← Complex.cpow_add _ _ hpn]
    congr 1
    ring
  have hf : (y : ℂ) ^ s * (Real.sqrt Real.pi : ℂ) *
        ((Real.pi * n / y : ℝ) : ℂ) ^ (s - 1 / 2) =
      (Real.pi : ℂ) ^ s * (n : ℂ) ^ (s - 1 / 2) * (Real.sqrt y : ℂ) := by
    rw [Complex.ofReal_div,
      Complex.div_cpow_ofReal_nonneg (mul_pos Real.pi_pos hn).le hy.le,
      Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg Real.pi_pos.le hn.le,
      ofReal_sqrt_eq_cpow_half Real.pi_pos.le, ofReal_sqrt_eq_cpow_half hy.le,
      hys, hps]
    calc
      _ = ((y : ℂ) ^ (s - 1 / 2) / (y : ℂ) ^ (s - 1 / 2)) *
          ((Real.pi : ℂ) ^ (s - 1 / 2) * (Real.pi : ℂ) ^ (1 / 2 : ℂ) *
            (n : ℂ) ^ (s - 1 / 2) * (y : ℂ) ^ (1 / 2 : ℂ)) := by ring
      _ = _ := by rw [div_self hyp, one_mul]
  rw [sqrt_fourier_scale hy hn]
  calc
    _ = (2 / g) * ((y : ℂ) ^ s * (Real.sqrt Real.pi : ℂ) *
        ((Real.pi * n / y : ℝ) : ℂ) ^ (s - 1 / 2)) := by ring
    _ = (2 / g) * ((Real.pi : ℂ) ^ s * (n : ℂ) ^ (s - 1 / 2) *
        (Real.sqrt y : ℂ)) := by rw [hf]
    _ = _ := by ring

end GapFamily.Analytic.BesselCoshOrder
