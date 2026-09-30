import GapFamily.Analytic.Kernel.KernelAnalytic
import GapFamily.Analytic.Transform.CosRootSqrtBound
import GapFamily.Analytic.Foundation.MinSeries

/-!
# Complex output bound for the higher kernel

The input energy remains as an explicit factor, including in the scalar channel.
The exponential grows on the square-root scale of the chiral arguments.
The continued zero-order arithmetic term is not included in this estimate.
-/

noncomputable section

namespace GapFamily.Analytic

open scoped Real

/-- Physical input energies control the sum of the two complex chiral arguments. -/
theorem norm_higherKernelArg_sum_le (j J : ℤ) (e : ℂ) (E : ℝ)
    (hE : |(J : ℝ)| ≤ E) :
    ‖higherKernelArgPlus j J e E‖ + ‖higherKernelArgMinus j J e E‖ ≤
      8 * π ^ 2 * (‖e‖ + |(j : ℝ)|) * E := by
  have hEp : 0 ≤ E + (J : ℝ) := by linarith [(abs_le.mp hE).1]
  have hEm : 0 ≤ E - (J : ℝ) := by linarith [(abs_le.mp hE).2]
  have hplus : ‖(E : ℂ) + (J : ℂ)‖ = E + (J : ℝ) := by
    rw [← Complex.ofReal_intCast, ← Complex.ofReal_add, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg hEp]
  have hminus : ‖(E : ℂ) - (J : ℂ)‖ = E - (J : ℝ) := by
    rw [← Complex.ofReal_intCast, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg hEm]
  have hj : ‖(j : ℂ)‖ = |(j : ℝ)| := by
    rw [← Complex.ofReal_intCast, Complex.norm_real, Real.norm_eq_abs]
  have hp := norm_add_le e (j : ℂ)
  have hm := norm_sub_le e (j : ℂ)
  rw [hj] at hp hm
  unfold higherKernelArgPlus higherKernelArgMinus
  simp only [norm_mul, norm_pow, Complex.norm_ofNat, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos Real.pi_pos, hplus, hminus]
  calc
    _ ≤ 4 * π ^ 2 * (E + J) * (‖e‖ + |(j : ℝ)|) +
        4 * π ^ 2 * (E - J) * (‖e‖ + |(j : ℝ)|) := by
      exact add_le_add (mul_le_mul_of_nonneg_left hp (by positivity))
        (mul_le_mul_of_nonneg_left hm (by positivity))
    _ = _ := by ring

/-- A useful square-root bound on the sum of the complex chiral growth exponents. -/
theorem sqrt_norm_higherKernelArg_sum_le (j J : ℤ) (e : ℂ) (E : ℝ)
    (hE : |(J : ℝ)| ≤ E) :
    Real.sqrt ‖higherKernelArgPlus j J e E‖ +
        Real.sqrt ‖higherKernelArgMinus j J e E‖ ≤
      8 * π * Real.sqrt ((‖e‖ + |(j : ℝ)|) * E) := by
  have hE0 : 0 ≤ E := (abs_nonneg _).trans hE
  have hM : 0 ≤ ‖e‖ + |(j : ℝ)| := by positivity
  have hsum := norm_higherKernelArg_sum_le j J e E hE
  have hb : 8 * π ^ 2 * (‖e‖ + |(j : ℝ)|) * E ≤
      (4 * π * Real.sqrt ((‖e‖ + |(j : ℝ)|) * E)) ^ 2 := by
    nlinarith [Real.sq_sqrt (mul_nonneg hM hE0),
      mul_nonneg (sq_nonneg π) (mul_nonneg hM hE0)]
  have hp : Real.sqrt ‖higherKernelArgPlus j J e E‖ ≤
      4 * π * Real.sqrt ((‖e‖ + |(j : ℝ)|) * E) := by
    apply (Real.sqrt_le_iff).mpr
    constructor
    · positivity
    · exact (le_add_of_nonneg_right (norm_nonneg _)).trans (hsum.trans hb)
  have hm : Real.sqrt ‖higherKernelArgMinus j J e E‖ ≤
      4 * π * Real.sqrt ((‖e‖ + |(j : ℝ)|) * E) := by
    apply (Real.sqrt_le_iff).mpr
    constructor
    · positivity
    · exact (le_add_of_nonneg_left (norm_nonneg _)).trans (hsum.trans hb)
  linarith

/-- Every genuine arithmetic summand has square-root exponential growth. -/
theorem norm_higherKernelTerm_le_exp_sqrt (j J : ℤ) (e E : ℂ) (n : ℕ) :
    ‖higherKernelTerm j J e E n‖ ≤
      ((‖higherKernelArgPlus j J e E‖ + ‖higherKernelArgMinus j J e E‖) / 2 *
        Real.exp (Real.sqrt ‖higherKernelArgPlus j J e E‖ +
          Real.sqrt ‖higherKernelArgMinus j J e E‖)) /
        ((n : ℝ) + 1) ^ 2 := by
  have hd : 1 ≤ ((n : ℝ) + 1) ^ 2 := by
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have hb := norm_cosRoot_mul_sub_one_div_le_exp_sqrt
    (higherKernelArgPlus j J e E) (higherKernelArgMinus j J e E)
    (((n : ℝ) + 1) ^ 2) hd
  push_cast at hb
  unfold higherKernelTerm
  rw [norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) (norm_kloostermanSum_div_le_one j J n)).trans
    (by simpa only [Nat.cast_add, Nat.cast_one] using hb)

/-- Summing the actual arithmetic terms preserves square-root exponential growth. -/
theorem norm_higherKernel_le_exp_sqrt (j J : ℤ) (e E : ℂ) :
    ‖higherKernel j J e E‖ ≤
      2 * (‖higherKernelArgPlus j J e E‖ + ‖higherKernelArgMinus j J e E‖) *
        Real.exp (Real.sqrt ‖higherKernelArgPlus j J e E‖ +
          Real.sqrt ‖higherKernelArgMinus j J e E‖) := by
  let A := (‖higherKernelArgPlus j J e E‖ + ‖higherKernelArgMinus j J e E‖) / 2 *
    Real.exp (Real.sqrt ‖higherKernelArgPlus j J e E‖ +
      Real.sqrt ‖higherKernelArgMinus j J e E‖)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hs := summable_one_div_nat_sq.mul_left A
  have hterm : ∀ n, ‖higherKernelTerm j J e E n‖ ≤ A * (1 / ((n : ℝ) + 1) ^ 2) := by
    intro n
    simpa only [A, mul_one_div] using norm_higherKernelTerm_le_exp_sqrt j J e E n
  calc
    _ = 2 * ‖∑' n, higherKernelTerm j J e E n‖ := by
      simp [higherKernel]
    _ ≤ 2 * ∑' n, ‖higherKernelTerm j J e E n‖ :=
      mul_le_mul_of_nonneg_left
        (norm_tsum_le_tsum_norm (summable_norm_higherKernelTerm j J e E)) (by norm_num)
    _ ≤ 2 * ∑' n : ℕ, A * (1 / ((n : ℝ) + 1) ^ 2) :=
      mul_le_mul_of_nonneg_left
        (Summable.tsum_le_tsum hterm (summable_norm_higherKernelTerm j J e E) hs)
        (by norm_num)
    _ = 2 * (A * ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ 2) := by rw [tsum_mul_left]
    _ ≤ 2 * (A * 2) := by
      gcongr
      exact tsum_one_div_nat_sq_le_two
    _ = _ := by dsimp [A]; ring

/-- A physical input and complex output obey a linear-energy, square-root-exponential bound. -/
theorem norm_higherKernel_complex_output_le (j J : ℤ) (e : ℂ) (E : ℝ)
    (hE : |(J : ℝ)| ≤ E) :
    ‖higherKernel j J e E‖ ≤
      16 * π ^ 2 * (‖e‖ + |(j : ℝ)|) * E *
        Real.exp (8 * π * Real.sqrt ((‖e‖ + |(j : ℝ)|) * E)) := by
  have hE0 : 0 ≤ E := (abs_nonneg _).trans hE
  calc
    _ ≤ 2 * (‖higherKernelArgPlus j J e E‖ + ‖higherKernelArgMinus j J e E‖) *
        Real.exp (Real.sqrt ‖higherKernelArgPlus j J e E‖ +
          Real.sqrt ‖higherKernelArgMinus j J e E‖) :=
      norm_higherKernel_le_exp_sqrt j J e E
    _ ≤ 2 * (8 * π ^ 2 * (‖e‖ + |(j : ℝ)|) * E) *
        Real.exp (8 * π * Real.sqrt ((‖e‖ + |(j : ℝ)|) * E)) := by
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left (norm_higherKernelArg_sum_le j J e E hE) (by norm_num))
        (Real.exp_le_exp.mpr (sqrt_norm_higherKernelArg_sum_le j J e E hE))
        (Real.exp_pos _).le (by positivity)
    _ = _ := by ring

/-- Uniform compact-output bound, retaining the scalar integrability factor at zero input. -/
theorem norm_higherKernel_complex_output_compact_le (j J : ℤ) (e : ℂ) (E R b : ℝ)
    (hE : |(J : ℝ)| ≤ E) (he : ‖e‖ ≤ R) (hEb : E ≤ b) :
    ‖higherKernel j J e E‖ ≤
      (16 * π ^ 2 * (R + |(j : ℝ)|) *
        Real.exp (8 * π * Real.sqrt ((R + |(j : ℝ)|) * b))) * E := by
  have hE0 : 0 ≤ E := (abs_nonneg _).trans hE
  have hR : 0 ≤ R := (norm_nonneg _).trans he
  have hb : 0 ≤ b := hE0.trans hEb
  calc
    _ ≤ 16 * π ^ 2 * (‖e‖ + |(j : ℝ)|) * E *
        Real.exp (8 * π * Real.sqrt ((‖e‖ + |(j : ℝ)|) * E)) :=
      norm_higherKernel_complex_output_le j J e E hE
    _ ≤ 16 * π ^ 2 * (R + |(j : ℝ)|) * E *
        Real.exp (8 * π * Real.sqrt ((R + |(j : ℝ)|) * b)) := by gcongr
    _ = _ := by ring

/-- The compact-output response coefficient with the input-energy factor removed. -/
def higherKernelCompactBound (j : ℤ) (b R : ℝ) : ℝ :=
  16 * π ^ 2 * (R + |(j : ℝ)|) *
    Real.exp (8 * π * Real.sqrt ((R + |(j : ℝ)|) * b))

/-- The coefficient is nonnegative on every nonnegative output radius. -/
theorem higherKernelCompactBound_nonneg (j : ℤ) (b R : ℝ) (hR : 0 ≤ R) :
    0 ≤ higherKernelCompactBound j b R := by
  unfold higherKernelCompactBound
  positivity

/-- Stable compact-band API for actual holomorphic response integrals. -/
theorem norm_higherKernel_complex_output_on_band_le (j J : ℤ) (e : ℂ) (E b R : ℝ)
    (hE : |(J : ℝ)| ≤ E) (hEb : E ≤ b) (he : ‖e‖ ≤ R) :
    ‖higherKernel j J e E‖ ≤ higherKernelCompactBound j b R * E :=
  norm_higherKernel_complex_output_compact_le j J e E R b hE he hEb

/-- Output radii proportional to the band give exponential growth linear in the band. -/
theorem higherKernelCompactBound_scaled_le (j : ℤ) (b R κ : ℝ)
    (hb : 0 ≤ b) (hκ : 0 ≤ κ)
    (hj : |(j : ℝ)| ≤ b) (hRb : R ≤ κ * b) :
    higherKernelCompactBound j b R ≤
      16 * π ^ 2 * (κ + 1) * b *
        Real.exp (8 * π * Real.sqrt (κ + 1) * b) := by
  have hm : R + |(j : ℝ)| ≤ (κ + 1) * b := by nlinarith
  have hs : Real.sqrt (((κ + 1) * b) * b) = Real.sqrt (κ + 1) * b := by
    rw [show ((κ + 1) * b) * b = (κ + 1) * b ^ 2 by ring,
      Real.sqrt_mul (by positivity), Real.sqrt_sq hb]
  unfold higherKernelCompactBound
  calc
    _ ≤ 16 * π ^ 2 * ((κ + 1) * b) *
        Real.exp (8 * π * Real.sqrt (((κ + 1) * b) * b)) := by gcongr
    _ = _ := by rw [hs]; simp only [mul_assoc]

/-- The higher kernel on a scaled output disk has growth exponential in the band width. -/
theorem norm_higherKernel_scaled_output_on_band_le (j J : ℤ) (e : ℂ) (E b κ : ℝ)
    (hE : |(J : ℝ)| ≤ E) (hEb : E ≤ b) (hκ : 0 ≤ κ)
    (hj : |(j : ℝ)| ≤ b) (he : ‖e‖ ≤ κ * b) :
    ‖higherKernel j J e E‖ ≤
      (16 * π ^ 2 * (κ + 1) * b *
        Real.exp (8 * π * Real.sqrt (κ + 1) * b)) * E := by
  have hE0 : 0 ≤ E := (abs_nonneg _).trans hE
  have hb : 0 ≤ b := hE0.trans hEb
  exact (norm_higherKernel_complex_output_on_band_le j J e E b (κ * b) hE hEb he).trans
    (mul_le_mul_of_nonneg_right
      (higherKernelCompactBound_scaled_le j b (κ * b) κ hb hκ hj le_rfl) hE0)

end GapFamily.Analytic
