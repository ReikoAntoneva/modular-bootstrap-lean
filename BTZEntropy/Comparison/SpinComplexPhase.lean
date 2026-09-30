import BTZEntropy.Comparison.SpinImageBound
import Mathlib.Analysis.Complex.Basic

/-!
# Uniform complex phase loss for noncentral spin images

The strict exponential loss persists on the entire vertical inversion line.
At least one of the two shifted chiral denominators is a unit distance from
its imaginary-axis center, because the image label is a nonzero integer.
-/

noncomputable section

namespace BTZEntropy

theorem spinComplexPhase_partialFraction (z : ℂ) (n : ℝ) (hz : 0 < z.re) :
    z / (z ^ 2 + (n : ℂ) ^ 2) =
      ((z + (n : ℂ) * Complex.I)⁻¹ + (z - (n : ℂ) * Complex.I)⁻¹) / 2 := by
  have hp : z + (n : ℂ) * Complex.I ≠ 0 := by
    intro h
    have hh := congrArg Complex.re h
    simp at hh
    linarith
  have hm : z - (n : ℂ) * Complex.I ≠ 0 := by
    intro h
    have hh := congrArg Complex.re h
    simp at hh
    linarith
  have hf : (z + (n : ℂ) * Complex.I) * (z - (n : ℂ) * Complex.I) =
      z ^ 2 + (n : ℂ) ^ 2 := by
    calc
      _ = z ^ 2 - (n : ℂ) ^ 2 * Complex.I ^ 2 := by ring
      _ = _ := by rw [Complex.I_sq]; ring
  rw [← hf]
  field_simp
  ring

theorem spinComplexPhase_re (z : ℂ) (n : ℝ) (hz : 0 < z.re) :
    (z / (z ^ 2 + (n : ℂ) ^ 2)).re =
      (z.re / (z.re ^ 2 + (z.im + n) ^ 2) +
        z.re / (z.re ^ 2 + (z.im - n) ^ 2)) / 2 := by
  rw [spinComplexPhase_partialFraction z n hz]
  simp only [Complex.div_ofNat_re, Complex.add_re, Complex.inv_re,
    Complex.normSq_apply, Complex.add_im, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, sub_zero, add_zero, mul_one, ← sq,
    zero_pow (by decide : (2 : ℕ) ≠ 0)]

private theorem chiral_pair_le {x t n : ℝ} (hx : 0 < x) (hn : 1 ≤ |n|) :
    (x / (x ^ 2 + (t + n) ^ 2) + x / (x ^ 2 + (t - n) ^ 2)) / 2 ≤
      (1 / x + x / (x ^ 2 + 1)) / 2 := by
  have hsq : 1 ≤ n ^ 2 := by nlinarith [sq_abs n]
  have hp : 0 < x ^ 2 + (t + n) ^ 2 := by positivity
  have hm : 0 < x ^ 2 + (t - n) ^ 2 := by positivity
  have hbase : ∀ s : ℝ, x / (x ^ 2 + s ^ 2) ≤ 1 / x := by
    intro s
    apply (div_le_div_iff₀ (by positivity) hx).mpr
    nlinarith [sq_nonneg s]
  have hone : ∀ s : ℝ, 1 ≤ s ^ 2 → x / (x ^ 2 + s ^ 2) ≤ x / (x ^ 2 + 1) := by
    intro s hs
    exact div_le_div_of_nonneg_left hx.le (by positivity) (by linarith)
  have hor : 1 ≤ (t + n) ^ 2 ∨ 1 ≤ (t - n) ^ 2 := by
    by_contra h
    push Not at h
    nlinarith [sq_nonneg t]
  rcases hor with h | h
  · linarith [hone (t + n) h, hbase (t - n)]
  · linarith [hbase (t + n), hone (t - n) h]

/-- A noncentral image loses a fixed positive exponent uniformly over the
whole vertical line, including neighborhoods of its two shifted poles. -/
theorem spinComplexPhase_re_le {z : ℂ} (hz : 0 < z.re) {n : ℤ} (hn : n ≠ 0) :
    (z / (z ^ 2 + (n : ℂ) ^ 2)).re ≤
      1 / z.re - 1 / (2 * z.re * (1 + z.re ^ 2)) := by
  have hnorm : (1 : ℝ) ≤ |(n : ℝ)| := by exact_mod_cast Int.one_le_abs hn
  have hphase := spinComplexPhase_re z (n : ℝ) hz
  simp only [Complex.ofReal_intCast] at hphase
  rw [hphase]
  calc
    _ ≤ (1 / z.re + z.re / (z.re ^ 2 + 1)) / 2 := chiral_pair_le hz hnorm
    _ = _ := by field_simp; ring

theorem spinComplexPhase_exp_le {a : ℝ} (ha : 0 ≤ a) {z : ℂ}
    (hz : 0 < z.re) {n : ℤ} (hn : n ≠ 0) :
    Real.exp (2 * Real.pi * a * (z / (z ^ 2 + (n : ℂ) ^ 2)).re) ≤
      Real.exp (2 * Real.pi * a / z.re) *
        Real.exp (-(spinImageDecayRate z.re / 2) * a) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h := mul_le_mul_of_nonneg_left (spinComplexPhase_re_le hz hn)
    (by positivity : 0 ≤ 2 * Real.pi * a)
  convert h using 1
  unfold spinImageDecayRate
  field_simp
  ring

/-- The chiral denominators have product at least `Re z * |n|`, uniformly in
`Im z`. This yields a summable `|n|^(-3/2)` envelope after both null factors. -/
theorem norm_spinComplexDenominator_ge {z : ℂ} (hz : 0 ≤ z.re) (n : ℝ) :
    z.re * |n| ≤ ‖z ^ 2 + (n : ℂ) ^ 2‖ := by
  have hp : z.re ≤ ‖z + (n : ℂ) * Complex.I‖ := by
    simpa using Complex.re_le_norm (z + (n : ℂ) * Complex.I)
  have hm : z.re ≤ ‖z - (n : ℂ) * Complex.I‖ := by
    simpa using Complex.re_le_norm (z - (n : ℂ) * Complex.I)
  have hip : |z.im + n| ≤ ‖z + (n : ℂ) * Complex.I‖ := by
    simpa using Complex.abs_im_le_norm (z + (n : ℂ) * Complex.I)
  have him : |z.im - n| ≤ ‖z - (n : ℂ) * Complex.I‖ := by
    simpa using Complex.abs_im_le_norm (z - (n : ℂ) * Complex.I)
  have hor : |n| ≤ |z.im + n| ∨ |n| ≤ |z.im - n| := by
    by_contra h
    push Not at h
    have ht := norm_sub_le (z.im + n) (z.im - n)
    rw [show (z.im + n) - (z.im - n) = 2 * n by ring] at ht
    simp only [Real.norm_eq_abs, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at ht
    linarith
  have hf : z ^ 2 + (n : ℂ) ^ 2 =
      (z + (n : ℂ) * Complex.I) * (z - (n : ℂ) * Complex.I) := by
    calc
      _ = z ^ 2 - (n : ℂ) ^ 2 * Complex.I ^ 2 := by rw [Complex.I_sq]; ring
      _ = _ := by ring
  rw [hf, norm_mul]
  rcases hor with h | h
  · calc
      _ ≤ ‖z - (n : ℂ) * Complex.I‖ * ‖z + (n : ℂ) * Complex.I‖ :=
        mul_le_mul hm (h.trans hip) (abs_nonneg _) (norm_nonneg _)
      _ = _ := mul_comm _ _
  · exact mul_le_mul hp (h.trans him) (abs_nonneg _) (norm_nonneg _)

end BTZEntropy
