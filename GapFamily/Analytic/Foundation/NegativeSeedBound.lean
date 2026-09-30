import GapFamily.Analytic.Foundation.Vacuum
import GapFamily.Analytic.Foundation.CoshBound

/-!
# Negative seed bound

The genuine Kloosterman summand has quadratic denominator decay multiplied
by the hyperbolic exponential. The seed's two nonnegative chiral magnitudes
are bounded separately, so the result applies to all four vacuum seeds.
-/

noncomputable section

namespace GapFamily.Analytic

open scoped Real

/-- Hyperbolic normalization at an arbitrary real denominator. -/
theorem cosRoot_neg_four_pi_sq_mul_div_sq {x : ℝ} (hx : 0 ≤ x) (d : ℝ) :
    cosRoot (-4 * (π : ℂ) ^ 2 * x / (d : ℂ) ^ 2) =
      (Real.cosh (2 * π * Real.sqrt x / d) : ℂ) := by
  have hs : (2 * π * Real.sqrt x / d) ^ 2 = 4 * π ^ 2 * x / d ^ 2 := by
    rw [div_pow]
    congr 1
    nlinarith [Real.sq_sqrt hx]
  have hi : (((2 * π * Real.sqrt x / d : ℝ) : ℂ) * Complex.I) ^ 2 =
      -4 * (π : ℂ) ^ 2 * x / (d : ℂ) ^ 2 := by
    rw [mul_pow, ← Complex.ofReal_pow, hs, Complex.I_sq]
    push_cast
    ring
  rw [← hi, cosRoot_sq, Complex.cos_mul_I, ← Complex.ofReal_cosh]

/-- The actual negative seed summand has the two expected hyperbolic factors. -/
theorem higherKernelTerm_negative (j J : ℤ) (e E : ℝ)
    (he : |(j : ℝ)| ≤ e) (hp : 0 ≤ -(E + J)) (hm : 0 ≤ -(E - J)) (n : ℕ) :
    higherKernelTerm j J e E n =
      (kloostermanSum j J n / ((n + 1 : ℕ) : ℂ)) *
        (((Real.cosh (2 * π * Real.sqrt (-(E + J) * (e + j)) /
          ((n + 1 : ℕ) : ℝ))) : ℂ) *
          ((Real.cosh (2 * π * Real.sqrt (-(E - J) * (e - j)) /
          ((n + 1 : ℕ) : ℝ))) : ℂ) - 1) := by
  have hep : 0 ≤ e + (j : ℝ) := by linarith [(abs_le.mp he).1]
  have hem : 0 ≤ e - (j : ℝ) := by linarith [(abs_le.mp he).2]
  have hpc := cosRoot_neg_four_pi_sq_mul_div_sq (mul_nonneg hp hep)
    ((n + 1 : ℕ) : ℝ)
  have hmc := cosRoot_neg_four_pi_sq_mul_div_sq (mul_nonneg hm hem)
    ((n + 1 : ℕ) : ℝ)
  have hap : higherKernelArgPlus j J e E / ((n + 1 : ℕ) : ℂ) ^ 2 =
      -4 * (π : ℂ) ^ 2 * ((-(E + J) * (e + j) : ℝ) : ℂ) /
        (((n + 1 : ℕ) : ℝ) : ℂ) ^ 2 := by
    unfold higherKernelArgPlus
    push_cast
    ring
  have ham : higherKernelArgMinus j J e E / ((n + 1 : ℕ) : ℂ) ^ 2 =
      -4 * (π : ℂ) ^ 2 * ((-(E - J) * (e - j) : ℝ) : ℂ) /
        (((n + 1 : ℕ) : ℝ) : ℂ) ^ 2 := by
    unfold higherKernelArgMinus
    push_cast
    ring
  unfold higherKernelTerm
  rw [hap, ham, hpc, hmc]

/-- A negative seed has quadratic denominator decay and the source's uniform
hyperbolic exponential, with the actual normalized Kloosterman sum retained. -/
theorem norm_higherKernelTerm_negative_le (j J : ℤ) (a e E : ℝ)
    (he : |(j : ℝ)| ≤ e)
    (hp0 : 0 ≤ -(E + J)) (hp : -(E + J) ≤ a)
    (hm0 : 0 ≤ -(E - J)) (hm : -(E - J) ≤ a) (n : ℕ) :
    ‖higherKernelTerm j J e E n‖ ≤
      4 * π ^ 2 * (a * e / ((n + 1 : ℕ) : ℝ) ^ 2) *
        Real.exp (4 * π * Real.sqrt (a * e) / ((n + 1 : ℕ) : ℝ)) := by
  let d : ℝ := ((n + 1 : ℕ) : ℝ)
  let x : ℝ := 2 * π * Real.sqrt (-(E + J) * (e + j)) / d
  let y : ℝ := 2 * π * Real.sqrt (-(E - J) * (e - j)) / d
  have hd : 0 < d := by dsimp [d]; positivity
  have hx : 0 ≤ x := by dsimp [x]; positivity
  have hy : 0 ≤ y := by dsimp [y]; positivity
  have ha : 0 ≤ a := hp0.trans hp
  have he0 : 0 ≤ e := (abs_nonneg _).trans he
  have hep : 0 ≤ e + (j : ℝ) := by linarith [(abs_le.mp he).1]
  have hem : 0 ≤ e - (j : ℝ) := by linarith [(abs_le.mp he).2]
  have hsp : 0 ≤ -(E + J) * (e + j) := mul_nonneg hp0 hep
  have hsm : 0 ≤ -(E - J) * (e - j) := mul_nonneg hm0 hem
  have hx2 : x ^ 2 = 4 * π ^ 2 * (-(E + J) * (e + j)) / d ^ 2 := by
    dsimp [x]
    rw [div_pow]
    congr 1
    nlinarith [Real.sq_sqrt hsp]
  have hy2 : y ^ 2 = 4 * π ^ 2 * (-(E - J) * (e - j)) / d ^ 2 := by
    dsimp [y]
    rw [div_pow]
    congr 1
    nlinarith [Real.sq_sqrt hsm]
  have hsum : -(E + J) * (e + j) + -(E - J) * (e - j) ≤ 2 * a * e := by
    nlinarith [mul_le_mul_of_nonneg_right hp hep, mul_le_mul_of_nonneg_right hm hem]
  have hpoly : (x ^ 2 + y ^ 2) / 2 ≤ 4 * π ^ 2 * (a * e / d ^ 2) := by
    rw [hx2, hy2]
    have hb := mul_le_mul_of_nonneg_left hsum
      (show 0 ≤ 4 * π ^ 2 / d ^ 2 by positivity)
    calc
      _ = (4 * π ^ 2 / d ^ 2 *
          (-(E + J) * (e + j) + -(E - J) * (e - j))) / 2 := by ring
      _ ≤ (4 * π ^ 2 / d ^ 2 * (2 * a * e)) / 2 :=
        div_le_div_of_nonneg_right hb (by norm_num)
      _ = _ := by ring
  have hexp : x + y ≤ 4 * π * Real.sqrt (a * e) / d := by
    have hraw : 2 * π * Real.sqrt (-(E + J) * (e + j)) +
        2 * π * Real.sqrt (-(E - J) * (e - j)) ≤ 4 * π * Real.sqrt (a * e) := by
      calc
        _ ≤ 2 * π * Real.sqrt (a * (e + j)) +
            2 * π * Real.sqrt (a * (e - j)) := by gcongr
        _ ≤ _ := vacuum_exponent_le_four_pi_sqrt ha he
    calc
      x + y = (2 * π * Real.sqrt (-(E + J) * (e + j)) +
        2 * π * Real.sqrt (-(E - J) * (e - j))) / d := by dsimp [x, y]; ring
      _ ≤ _ := div_le_div_of_nonneg_right hraw hd.le
  have hbracket : ‖(Real.cosh x : ℂ) * (Real.cosh y : ℂ) - 1‖ ≤
      (x ^ 2 + y ^ 2) / 2 * Real.exp (x + y) := by
    rw [← Complex.ofReal_mul, ← Complex.ofReal_one, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs]
    exact cosh_mul_cosh_sub_one_abs_le hx hy
  rw [higherKernelTerm_negative j J e E he hp0 hm0 n]
  change ‖(kloostermanSum j J n / ((n + 1 : ℕ) : ℂ)) *
    ((Real.cosh x : ℂ) * (Real.cosh y : ℂ) - 1)‖ ≤ _
  calc
    _ ≤ 1 * ‖(Real.cosh x : ℂ) * (Real.cosh y : ℂ) - 1‖ := by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (norm_kloostermanSum_div_le_one j J n)
        (norm_nonneg _)
    _ ≤ (x ^ 2 + y ^ 2) / 2 * Real.exp (x + y) := by simpa using hbracket
    _ ≤ _ := mul_le_mul hpoly (Real.exp_le_exp.mpr hexp) (Real.exp_pos _).le
      (by positivity)

end GapFamily.Analytic
