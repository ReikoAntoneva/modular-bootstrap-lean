import GapFamily.Analytic.Arithmetic.Kloosterman
import GapFamily.Analytic.Foundation.VacuumFactor
import GapFamily.Analytic.Foundation.SpinRadical

/-!
# The actual four-seed vacuum at denominator one

The null subtractions are taken from the same Kloosterman kernel as the
physical-energy estimates. This module does not supply the continued
zero-order term of the vacuum completion.
-/

noncomputable section

namespace GapFamily.Analytic

open scoped Real

/-- A negative real argument in the entire cosine-root series is hyperbolic. -/
theorem cosRoot_neg_ofReal_nonneg {x : ℝ} (hx : 0 ≤ x) :
    cosRoot (- (x : ℂ)) = (Real.cosh (Real.sqrt x) : ℂ) := by
  have hs : (Real.sqrt x : ℂ) ^ 2 = (x : ℂ) := by
    exact_mod_cast Real.sq_sqrt hx
  have hi : ((Real.sqrt x : ℂ) * Complex.I) ^ 2 = -(x : ℂ) := by
    rw [mul_pow, hs, Complex.I_sq]
    ring
  rw [← hi, cosRoot_sq, Complex.cos_mul_I, ← Complex.ofReal_cosh]

/-- The normalization of each negative-energy chiral factor. -/
theorem cosRoot_neg_four_pi_sq_mul {x : ℝ} (hx : 0 ≤ x) :
    cosRoot (-4 * (π : ℂ) ^ 2 * x) = (Real.cosh (2 * π * Real.sqrt x) : ℂ) := by
  have hs : (2 * π * Real.sqrt x) ^ 2 = 4 * π ^ 2 * x := by
    nlinarith [Real.sq_sqrt hx]
  have hi : (((2 * π * Real.sqrt x : ℝ) : ℂ) * Complex.I) ^ 2 =
      -4 * (π : ℂ) ^ 2 * x := by
    rw [mul_pow, ← Complex.ofReal_pow, hs, Complex.I_sq]
    push_cast
    ring
  rw [← hi, cosRoot_sq, Complex.cos_mul_I, ← Complex.ofReal_cosh]

/-- The four original vacuum seeds, with the outer kernel factor two. -/
def vacuumHigherTerm (a e : ℝ) (j : ℤ) (n : ℕ) : ℂ :=
  2 * (higherKernelTerm j 0 e (-a) n -
    higherKernelTerm j 1 e (1-a) n -
    higherKernelTerm j (-1) e (1-a) n +
    higherKernelTerm j 0 e (2-a) n)

/-- The convergent entire part of the actual four-seed vacuum combination. -/
def vacuumHigherKernel (a e : ℝ) (j : ℤ) : ℂ :=
  higherKernel j 0 e (-a) - higherKernel j 1 e (1-a) -
    higherKernel j (-1) e (1-a) + higherKernel j 0 e (2-a)

/-- The entire vacuum series converges before any infinite-sum identity is used. -/
theorem summable_vacuumHigherTerm (a e : ℝ) (j : ℤ) :
    Summable (vacuumHigherTerm a e j) :=
  (((summable_higherKernelTerm j 0 e (-a)).sub
    (summable_higherKernelTerm j 1 e (1-a))).sub
    (summable_higherKernelTerm j (-1) e (1-a))).add
    (summable_higherKernelTerm j 0 e (2-a)) |>.mul_left 2

/-- The actual four finite seed outputs agree with the convergent termwise series. -/
theorem vacuumHigherKernel_eq_tsum (a e : ℝ) (j : ℤ) :
    vacuumHigherKernel a e j = ∑' n, vacuumHigherTerm a e j n := by
  have h0 := summable_higherKernelTerm j 0 (e : ℂ) (-a)
  have hp := summable_higherKernelTerm j 1 (e : ℂ) (1-a)
  have hm := summable_higherKernelTerm j (-1) (e : ℂ) (1-a)
  have h2 := summable_higherKernelTerm j 0 (e : ℂ) (2-a)
  simp only [vacuumHigherTerm, tsum_mul_left,
    ((h0.sub hp).sub hm).tsum_add h2, (h0.sub hp).tsum_sub hm, h0.tsum_sub hp,
    vacuumHigherKernel, higherKernel]
  ring

/-- The denominator-one bracket factors before any hyperbolic estimate. -/
theorem vacuumHigherTerm_zero_factor (a e : ℝ) (j : ℤ) :
    vacuumHigherTerm a e j 0 =
      2 * (cosRoot (-4 * (π : ℂ) ^ 2 * a * ((e : ℂ) + j)) -
        cosRoot (-4 * (π : ℂ) ^ 2 * (a - 2) * ((e : ℂ) + j))) *
      (cosRoot (-4 * (π : ℂ) ^ 2 * a * ((e : ℂ) - j)) -
        cosRoot (-4 * (π : ℂ) ^ 2 * (a - 2) * ((e : ℂ) - j))) := by
  unfold vacuumHigherTerm
  simp only [higherKernelTerm_zero, higherKernelArgPlus, higherKernelArgMinus]
  norm_num
  ring_nf

/-- Hyperbolic form of the exact four-seed term on the closed physical output cone. -/
theorem vacuumHigherTerm_zero_eq_cosh (a e : ℝ) (j : ℤ)
    (ha : 2 ≤ a) (he : |(j : ℝ)| ≤ e) :
    vacuumHigherTerm a e j 0 =
      ((2 * (Real.cosh (2 * π * Real.sqrt (a * (e + j))) -
          Real.cosh (2 * π * Real.sqrt ((a - 2) * (e + j)))) *
        (Real.cosh (2 * π * Real.sqrt (a * (e - j))) -
          Real.cosh (2 * π * Real.sqrt ((a - 2) * (e - j)))) : ℝ) : ℂ) := by
  have hplus : 0 ≤ e + (j : ℝ) := by linarith [(abs_le.mp he).1]
  have hminus : 0 ≤ e - (j : ℝ) := by linarith [(abs_le.mp he).2]
  have hfactor (A t : ℝ) (hA : 0 ≤ A) (ht : 0 ≤ t) :
      cosRoot (-4 * (π : ℂ) ^ 2 * A * t) =
        (Real.cosh (2 * π * Real.sqrt (A * t)) : ℂ) := by
    simpa only [Complex.ofReal_mul, mul_assoc] using
      cosRoot_neg_four_pi_sq_mul (mul_nonneg hA ht)
  have hap := hfactor a (e + j) (by linarith) hplus
  have ham := hfactor a (e - j) (by linarith) hminus
  have hbp := hfactor (a - 2) (e + j) (by linarith) hplus
  have hbm := hfactor (a - 2) (e - j) (by linarith) hminus
  push_cast at hap ham hbp hbm ⊢
  rw [vacuumHigherTerm_zero_factor, hap, ham, hbp, hbm]

/-- The real denominator-one numerator, extracted from the actual four-seed kernel. -/
def vacuumLeading (a e : ℝ) (j : ℤ) : ℝ := (vacuumHigherTerm a e j 0).re

/-- The real numerator inherits the exact null-subtracted factorization. -/
theorem vacuumLeading_eq_cosh (a e : ℝ) (j : ℤ)
    (ha : 2 ≤ a) (he : |(j : ℝ)| ≤ e) :
    vacuumLeading a e j =
      2 * (Real.cosh (2 * π * Real.sqrt (a * (e + j))) -
          Real.cosh (2 * π * Real.sqrt ((a - 2) * (e + j)))) *
        (Real.cosh (2 * π * Real.sqrt (a * (e - j))) -
          Real.cosh (2 * π * Real.sqrt ((a - 2) * (e - j)))) := by
  simpa only [vacuumLeading, Complex.ofReal_re] using
    congrArg Complex.re (vacuumHigherTerm_zero_eq_cosh a e j ha he)

/-- No imaginary part is hidden by taking the real numerator. -/
theorem vacuumHigherTerm_zero_eq_ofReal (a e : ℝ) (j : ℤ)
    (ha : 2 ≤ a) (he : |(j : ℝ)| ≤ e) :
    vacuumHigherTerm a e j 0 = (vacuumLeading a e j : ℂ) := by
  rw [vacuumLeading_eq_cosh a e j ha he, vacuumHigherTerm_zero_eq_cosh a e j ha he]

/-- The leading vacuum term vanishes exactly at either closed spin edge. -/
theorem vacuumLeading_at_spin_edge (a : ℝ) (j : ℤ) (ha : 2 ≤ a) :
    vacuumLeading a |(j : ℝ)| j = 0 := by
  rw [vacuumLeading_eq_cosh a |(j : ℝ)| j ha le_rfl]
  rcases le_or_gt 0 (j : ℝ) with hj | hj
  · simp [abs_of_nonneg hj]
  · simp [abs_of_neg hj]

/-- The source's `2 D_a(e+j) D_a(e-j)` is the actual denominator-one term. -/
theorem vacuumLeading_eq (a e : ℝ) (j : ℤ)
    (ha : 2 ≤ a) (he : |(j : ℝ)| ≤ e) :
    vacuumLeading a e j = 2 * vacuumDifference a (e + j) * vacuumDifference a (e - j) :=
  vacuumLeading_eq_cosh a e j ha he

/-- Positivity of the actual leading numerator on the closed spin cone. -/
theorem vacuumLeading_nonneg (a e : ℝ) (j : ℤ)
    (ha : 2 ≤ a) (he : |(j : ℝ)| ≤ e) :
    0 ≤ vacuumLeading a e j := by
  rw [vacuumLeading_eq a e j ha he]
  exact mul_nonneg (mul_nonneg (by norm_num) (vacuumDifference_nonneg ha))
    (vacuumDifference_nonneg ha)

/-- The denominator-one vacuum upper bound, uniform up to the spin edge. -/
theorem vacuumLeading_le_exp (a e : ℝ) (j : ℤ)
    (ha : 2 ≤ a) (he : |(j : ℝ)| ≤ e) :
    vacuumLeading a e j ≤ 2 * Real.exp (4 * π * Real.sqrt (a * e)) := by
  rw [vacuumLeading_eq a e j ha he]
  calc
    _ ≤ 2 * Real.exp (2 * π * Real.sqrt (a * (e + j))) *
        Real.exp (2 * π * Real.sqrt (a * (e - j))) :=
      mul_le_mul (mul_le_mul_of_nonneg_left (vacuumDifference_le_exp a (e + j))
        (by norm_num)) (vacuumDifference_le_exp a (e - j))
        (vacuumDifference_nonneg ha) (by positivity)
    _ = 2 * Real.exp (2 * π * Real.sqrt (a * (e + j)) +
        2 * π * Real.sqrt (a * (e - j))) := by rw [Real.exp_add]; ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact Real.exp_le_exp.mpr (vacuum_exponent_le_four_pi_sqrt (by linarith) he)

/-- The lower bound retains the vanishing factor `e²-j²` at every spin edge. -/
theorem vacuumLeading_ge_exp (a e : ℝ) (j : ℤ)
    (ha : 100 ≤ a) (he : |(j : ℝ)| ≤ e) :
    (2 * π ^ 4 / 625) * (e ^ 2 - (j : ℝ) ^ 2) * Real.exp (8 * Real.sqrt (a * e)) ≤
      vacuumLeading a e j := by
  have ha2 : 2 ≤ a := by linarith
  have hplus : 0 ≤ e + (j : ℝ) := by linarith [(abs_le.mp he).1]
  have hminus : 0 ≤ e - (j : ℝ) := by linarith [(abs_le.mp he).2]
  have hedge : 0 ≤ e ^ 2 - (j : ℝ) ^ 2 := by nlinarith [mul_nonneg hplus hminus]
  have hp := vacuumDifference_ge_exp ha2 hplus
  have hm := vacuumDifference_ge_exp ha2 hminus
  have hmul := mul_le_mul (mul_le_mul_of_nonneg_left hp (show (0 : ℝ) ≤ 2 by norm_num))
    hm (by positivity : 0 ≤ π ^ 2 / 25 * (e - (j : ℝ)) *
      Real.exp ((19 / 20 : ℝ) * π * (Real.sqrt a + Real.sqrt (a - 2)) *
        Real.sqrt (e - (j : ℝ))))
    (mul_nonneg (by norm_num) (vacuumDifference_nonneg ha2))
  calc
    _ ≤ (2 * π ^ 4 / 625) * (e ^ 2 - (j : ℝ) ^ 2) *
        Real.exp ((19 / 20 : ℝ) * π * (Real.sqrt a + Real.sqrt (a - 2)) *
          (Real.sqrt (e + j) + Real.sqrt (e - j))) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Real.exp_le_exp.mpr (eight_sqrt_mul_le_vacuum_exponent ha he)
    _ = 2 * (π ^ 2 / 25 * (e + j) *
        Real.exp ((19 / 20 : ℝ) * π * (Real.sqrt a + Real.sqrt (a - 2)) *
          Real.sqrt (e + j))) * (π ^ 2 / 25 * (e - j) *
        Real.exp ((19 / 20 : ℝ) * π * (Real.sqrt a + Real.sqrt (a - 2)) *
          Real.sqrt (e - j))) := by
      rw [mul_add, Real.exp_add]
      ring
    _ ≤ vacuumLeading a e j := by
      rw [vacuumLeading_eq a e j ha2 he]
      exact hmul

end GapFamily.Analytic
