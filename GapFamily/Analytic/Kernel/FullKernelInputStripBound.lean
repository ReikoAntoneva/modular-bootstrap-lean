import GapFamily.Analytic.Transform.CosRootShiftBound
import GapFamily.Analytic.Kernel.FullKernelResponse

/-!
# Input strip growth of the full kernel

For physical output energy, the exponential depends on the imaginary part of
the input square-root coordinate. Its real part contributes only polynomially.
-/

noncomputable section

namespace GapFamily.Analytic

open scoped Real

/-- The sum of the two physical chiral square roots has the sharp uniform bound. -/
theorem sqrt_chiral_sum_le (e t : ℝ) (ht : |t| ≤ e) :
    Real.sqrt (e + t) + Real.sqrt (e - t) ≤ 2 * Real.sqrt e := by
  have he : 0 ≤ e := (abs_nonneg _).trans ht
  have hp : 0 ≤ e + t := by linarith [(abs_le.mp ht).1]
  have hm : 0 ≤ e - t := by linarith [(abs_le.mp ht).2]
  have hs1 := Real.sq_sqrt hp
  have hs2 := Real.sq_sqrt hm
  have hs3 := Real.sq_sqrt he
  have hs4 := sq_nonneg (Real.sqrt (e + t) - Real.sqrt (e - t))
  have hs5 := Real.sqrt_nonneg (e + t)
  have hs6 := Real.sqrt_nonneg (e - t)
  have hs7 := Real.sqrt_nonneg e
  nlinarith

/-- The physical chiral constants yield the radius coefficient `4π√e`. -/
theorem sqrt_chiral_kernel_sum_le (e t : ℝ) (ht : |t| ≤ e) :
    Real.sqrt (4 * π ^ 2 * (e + t)) +
      Real.sqrt (4 * π ^ 2 * (e - t)) ≤ 4 * π * Real.sqrt e := by
  have hfour : Real.sqrt (4 * π ^ 2) = 2 * π := by
    rw [show 4 * π ^ 2 = (2 * π) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  rw [Real.sqrt_mul (show 0 ≤ 4 * π ^ 2 by positivity),
    Real.sqrt_mul (show 0 ≤ 4 * π ^ 2 by positivity), hfour]
  have h := mul_le_mul_of_nonneg_left (sqrt_chiral_sum_le e t ht)
    (show 0 ≤ 2 * π by positivity)
  nlinarith

/-- Each actual arithmetic summand has strip growth and denominator-square decay. -/
theorem norm_higherKernelTerm_input_strip_le (j J : ℤ) (e : ℝ) (z : ℂ)
    (he : |(j : ℝ)| ≤ e) (n : ℕ) :
    ‖higherKernelTerm j J e (|(J : ℝ)| + z ^ 2) n‖ ≤
      (4 * π ^ 2 * e * (‖z‖ ^ 2 + 2 * |(J : ℝ)|) *
        Real.exp (4 * π * Real.sqrt e * |z.im|)) / ((n : ℝ) + 1) ^ 2 := by
  have he0 : 0 ≤ e := (abs_nonneg _).trans he
  have hep : 0 ≤ e + (j : ℝ) := by linarith [(abs_le.mp he).1]
  have hem : 0 ≤ e - (j : ℝ) := by linarith [(abs_le.mp he).2]
  have hJp : 0 ≤ |(J : ℝ)| + (J : ℝ) := by linarith [neg_le_abs (J : ℝ)]
  have hJm : 0 ≤ |(J : ℝ)| - (J : ℝ) := by linarith [le_abs_self (J : ℝ)]
  have hp : higherKernelArgPlus j J e (|(J : ℝ)| + z ^ 2) =
      ((4 * π ^ 2 * (e + (j : ℝ)) : ℝ) : ℂ) *
        (z ^ 2 + ((|(J : ℝ)| + (J : ℝ) : ℝ) : ℂ)) := by
    unfold higherKernelArgPlus
    push_cast
    ring
  have hm : higherKernelArgMinus j J e (|(J : ℝ)| + z ^ 2) =
      ((4 * π ^ 2 * (e - (j : ℝ)) : ℝ) : ℂ) *
        (z ^ 2 + ((|(J : ℝ)| - (J : ℝ) : ℝ) : ℂ)) := by
    unfold higherKernelArgMinus
    push_cast
    ring
  have hden : 1 ≤ ((n : ℝ) + 1) ^ 2 := by
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have h := norm_cosRoot_shift_mul_sub_one_div_le z
    (4 * π ^ 2 * (e + (j : ℝ))) (4 * π ^ 2 * (e - (j : ℝ)))
    (|(J : ℝ)| + (J : ℝ)) (|(J : ℝ)| - (J : ℝ)) (((n : ℝ) + 1) ^ 2)
    (by positivity) (by positivity) hJp hJm hden
  have hpoly : (4 * π ^ 2 * (e + (j : ℝ)) * (‖z‖ ^ 2 + (|(J : ℝ)| + (J : ℝ))) +
      4 * π ^ 2 * (e - (j : ℝ)) * (‖z‖ ^ 2 + (|(J : ℝ)| - (J : ℝ)))) / 2 ≤
      4 * π ^ 2 * e * (‖z‖ ^ 2 + 2 * |(J : ℝ)|) := by
    have h1 : |(J : ℝ)| + (J : ℝ) ≤ 2 * |(J : ℝ)| := by
      linarith [le_abs_self (J : ℝ)]
    have h2 : |(J : ℝ)| - (J : ℝ) ≤ 2 * |(J : ℝ)| := by
      linarith [neg_le_abs (J : ℝ)]
    calc
      _ ≤ (4 * π ^ 2 * (e + (j : ℝ)) * (‖z‖ ^ 2 + 2 * |(J : ℝ)|) +
          4 * π ^ 2 * (e - (j : ℝ)) * (‖z‖ ^ 2 + 2 * |(J : ℝ)|)) / 2 := by
        gcongr
      _ = _ := by ring
  have hgrowth := sqrt_chiral_kernel_sum_le e (j : ℝ) he
  have hbound : (4 * π ^ 2 * (e + (j : ℝ)) * (‖z‖ ^ 2 + (|(J : ℝ)| + (J : ℝ))) +
        4 * π ^ 2 * (e - (j : ℝ)) * (‖z‖ ^ 2 + (|(J : ℝ)| - (J : ℝ)))) / 2 *
        Real.exp ((Real.sqrt (4 * π ^ 2 * (e + (j : ℝ))) +
          Real.sqrt (4 * π ^ 2 * (e - (j : ℝ)))) * |z.im|) ≤
      4 * π ^ 2 * e * (‖z‖ ^ 2 + 2 * |(J : ℝ)|) *
        Real.exp (4 * π * Real.sqrt e * |z.im|) := by
    exact mul_le_mul hpoly (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_right hgrowth (abs_nonneg _)))
      (Real.exp_pos _).le (by positivity)
  unfold higherKernelTerm
  rw [norm_mul]
  refine (mul_le_of_le_one_left (norm_nonneg _)
    (norm_kloostermanSum_div_le_one j J n)).trans ?_
  rw [hp, hm]
  have hcast : (((((n : ℝ) + 1) ^ 2) : ℝ) : ℂ) = ((n + 1 : ℕ) : ℂ) ^ 2 := by
    push_cast
    rfl
  rw [hcast] at h
  exact h.trans (div_le_div_of_nonneg_right hbound (sq_nonneg _))

/-- The actual higher kernel grows exponentially only with the input imaginary part. -/
theorem norm_higherKernel_input_strip_le (j J : ℤ) (e : ℝ) (z : ℂ)
    (he : |(j : ℝ)| ≤ e) :
    ‖higherKernel j J e (|(J : ℝ)| + z ^ 2)‖ ≤
      16 * π ^ 2 * e * (‖z‖ ^ 2 + 2 * |(J : ℝ)|) *
        Real.exp (4 * π * Real.sqrt e * |z.im|) := by
  let A := 4 * π ^ 2 * e * (‖z‖ ^ 2 + 2 * |(J : ℝ)|) *
    Real.exp (4 * π * Real.sqrt e * |z.im|)
  have he0 : 0 ≤ e := (abs_nonneg _).trans he
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hs := summable_one_div_nat_sq.mul_left A
  have hterm : ∀ n, ‖higherKernelTerm j J e (|(J : ℝ)| + z ^ 2) n‖ ≤
      A * (1 / ((n : ℝ) + 1) ^ 2) := by
    intro n
    simpa only [A, mul_one_div] using norm_higherKernelTerm_input_strip_le j J e z he n
  calc
    _ = 2 * ‖∑' n, higherKernelTerm j J e (|(J : ℝ)| + z ^ 2) n‖ := by
      simp [higherKernel]
    _ ≤ 2 * ∑' n, ‖higherKernelTerm j J e (|(J : ℝ)| + z ^ 2) n‖ :=
      mul_le_mul_of_nonneg_left
        (norm_tsum_le_tsum_norm (summable_norm_higherKernelTerm j J _ _)) (by norm_num)
    _ ≤ 2 * ∑' n : ℕ, A * (1 / ((n : ℝ) + 1) ^ 2) :=
      mul_le_mul_of_nonneg_left
        (Summable.tsum_le_tsum hterm (summable_norm_higherKernelTerm j J _ _) hs)
        (by norm_num)
    _ = 2 * (A * ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ 2) := by rw [tsum_mul_left]
    _ ≤ 2 * (A * 2) := by
      gcongr
      exact tsum_one_div_nat_sq_le_two
    _ = _ := by dsimp [A]; ring

/-- The full kernel includes the actual central arithmetic term. -/
theorem norm_fullKernel_input_strip_le (j J : ℤ) (e : ℝ) (z : ℂ)
    (he : |(j : ℝ)| ≤ e) :
    ‖fullKernelHol j J e (|(J : ℝ)| + z ^ 2)‖ ≤
      centralKernelBound * (|(j : ℝ)| * |(J : ℝ)|) +
        16 * π ^ 2 * e * (‖z‖ ^ 2 + 2 * |(J : ℝ)|) *
          Real.exp (4 * π * Real.sqrt e * |z.im|) :=
  (norm_add_le _ _).trans (add_le_add (norm_centralKernel_le j J)
    (norm_higherKernel_input_strip_le j J e z he))

/-- The full holomorphic input extension includes its scalar rank correction. -/
theorem norm_correctedKernelHolInput_strip_le (j J : ℤ) (e : ℝ) (z : ℂ)
    (he : |(j : ℝ)| ≤ e) :
    ‖correctedKernelHolInput j J 1 e z‖ ≤
      centralKernelBound * (|(j : ℝ)| * |(J : ℝ)|) +
        16 * π ^ 2 * e * (‖z‖ ^ 2 + 2 * |(J : ℝ)|) *
          Real.exp (4 * π * Real.sqrt e * |z.im|) +
        12 * Real.sqrt e * ‖z‖ := by
  unfold correctedKernelHolInput
  simp only [Complex.ofReal_one, one_mul, Real.sqrt_one, mul_one]
  refine (norm_add_le _ _).trans (add_le_add
    (norm_fullKernel_input_strip_le j J e z he) ?_)
  split_ifs
  · simp only [norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg e)]
    exact le_rfl
  · simp only [norm_zero]
    positivity

/-- A rectangle in the square-root coordinate has an energy-factor majorant.
Only the imaginary height enters the exponential. -/
theorem norm_correctedKernelHolInput_rectangle_le (j J : ℤ) (e B R r : ℝ) (z : ℂ)
    (he : |(j : ℝ)| ≤ e) (heB : e ≤ B) (hz : ‖z‖ ≤ R) (him : |z.im| ≤ r) :
    ‖correctedKernelHolInput j J 1 e z‖ ≤
      (centralKernelBound * |(J : ℝ)| +
        16 * π ^ 2 * (R ^ 2 + 2 * |(J : ℝ)|) *
          Real.exp (4 * π * r * Real.sqrt B)) * e +
        12 * R * Real.sqrt e := by
  have he0 : 0 ≤ e := (abs_nonneg _).trans he
  have hB : 0 ≤ B := he0.trans heB
  have hR : 0 ≤ R := (norm_nonneg _).trans hz
  have hr : 0 ≤ r := (abs_nonneg _).trans him
  have hc : centralKernelBound * (|(j : ℝ)| * |(J : ℝ)|) ≤
      centralKernelBound * |(J : ℝ)| * e := by
    nlinarith [mul_le_mul_of_nonneg_left he
      (mul_nonneg centralKernelBound_pos.le (abs_nonneg (J : ℝ)))]
  have hh : 16 * π ^ 2 * e * (‖z‖ ^ 2 + 2 * |(J : ℝ)|) *
        Real.exp (4 * π * Real.sqrt e * |z.im|) ≤
      16 * π ^ 2 * e * (R ^ 2 + 2 * |(J : ℝ)|) *
        Real.exp (4 * π * r * Real.sqrt B) := by
    rw [show 4 * π * r * Real.sqrt B = 4 * π * Real.sqrt B * r by ring]
    gcongr
  have hrank : 12 * Real.sqrt e * ‖z‖ ≤ 12 * R * Real.sqrt e := by
    nlinarith [mul_le_mul_of_nonneg_left hz
      (show 0 ≤ 12 * Real.sqrt e by positivity)]
  exact (norm_correctedKernelHolInput_strip_le j J e z he).trans (by
    nlinarith [hc, hh, hrank])

/-- On a disk centered on the real axis, the exponential is independent of the center. -/
theorem norm_correctedKernelHolInput_real_disk_le (j J : ℤ) (e B x r : ℝ) (z : ℂ)
    (he : |(j : ℝ)| ≤ e) (heB : e ≤ B) (hz : z ∈ Metric.closedBall (x : ℂ) r) :
    ‖correctedKernelHolInput j J 1 e z‖ ≤
      (centralKernelBound * |(J : ℝ)| +
        16 * π ^ 2 * ((|x| + r) ^ 2 + 2 * |(J : ℝ)|) *
          Real.exp (4 * π * r * Real.sqrt B)) * e +
        12 * (|x| + r) * Real.sqrt e := by
  have hdist : ‖z - (x : ℂ)‖ ≤ r := by
    simpa only [Metric.mem_closedBall, dist_eq_norm] using hz
  have him : |z.im| ≤ r := by
    have h := (Complex.abs_im_le_norm (z - (x : ℂ))).trans hdist
    simpa only [Complex.sub_im, Complex.ofReal_im, sub_zero] using h
  have hnorm : ‖z‖ ≤ |x| + r := by
    have h := norm_add_le (z - (x : ℂ)) (x : ℂ)
    simp only [sub_add_cancel, Complex.norm_real, Real.norm_eq_abs] at h
    linarith
  exact norm_correctedKernelHolInput_rectangle_le j J e B (|x| + r) r z
    he heB hnorm him

end GapFamily.Analytic
