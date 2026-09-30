import GapFamily.Analytic.Foundation.MomentCancellation
import GapFamily.Quadrature.MarkovBound
import GapFamily.Analytic.Foundation.PolynomialExtrapolation
import GapFamily.Analytic.Foundation.PolynomialL2
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Algebra.Order.Archimedean.Basic

/-!
# Quantitative propagation from a separated real interval

The fixed disk bound is combined with actual Taylor polynomials and polynomial
extrapolation; no smallness propagation estimate is an external input.
-/

open Set Metric MeasureTheory Polynomial
open scoped BigOperators

namespace GapFamily.Analytic

noncomputable def realTaylorPolynomial (F : ℂ → ℂ) (n : ℕ) : ℝ[X] :=
  ∑ j ∈ Finset.range (n+1), C ((taylorCoefficient F 0 j).re) * X^j

noncomputable def imagTaylorPolynomial (F : ℂ → ℂ) (n : ℕ) : ℝ[X] :=
  ∑ j ∈ Finset.range (n+1), C ((taylorCoefficient F 0 j).im) * X^j

theorem realTaylorPolynomial_natDegree (F : ℂ → ℂ) (n : ℕ) :
    (realTaylorPolynomial F n).natDegree ≤ n := by
  apply natDegree_sum_le_of_forall_le
  intro j hj
  exact (natDegree_C_mul_X_pow_le _ _).trans (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))

theorem imagTaylorPolynomial_natDegree (F : ℂ → ℂ) (n : ℕ) :
    (imagTaylorPolynomial F n).natDegree ≤ n := by
  apply natDegree_sum_le_of_forall_le
  intro j hj
  exact (natDegree_C_mul_X_pow_le _ _).trans (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))

theorem realTaylorPolynomial_eval (F : ℂ → ℂ) (n : ℕ) (x : ℝ) :
    (realTaylorPolynomial F n).eval x = (taylorPolynomial F 0 n (x : ℂ)).re := by
  simp [realTaylorPolynomial, taylorPolynomial, Polynomial.eval_finsetSum,
    ← Complex.ofReal_pow]

theorem imagTaylorPolynomial_eval (F : ℂ → ℂ) (n : ℕ) (x : ℝ) :
    (imagTaylorPolynomial F n).eval x = (taylorPolynomial F 0 n (x : ℂ)).im := by
  simp [imagTaylorPolynomial, taylorPolynomial, Polynomial.eval_finsetSum,
    ← Complex.ofReal_pow]

/-- The actual Cauchy remainder on the relevant real segment of the fixed disk. -/
theorem propagation_taylor_error {F : ℂ → ℂ} {A : ℝ} (hA : 0 ≤ A)
    (hf : DiffContOnCl ℂ F (ball 0 16384))
    (hbound : ∀ z ∈ sphere (0 : ℂ) 16384, ‖F z‖ ≤ A)
    (n : ℕ) {x : ℝ} (hx : x ∈ Icc 0 2) :
    ‖F (x : ℂ) - taylorPolynomial F 0 n (x : ℂ)‖ ≤ A / (64 * ((64 : ℝ)^n)^2) := by
  have h := norm_taylor_remainder_le (by norm_num : (0 : ℝ) < 16384) hA
    (by norm_num : (0 : ℝ) ≤ 1/4096) (by norm_num : (1 : ℝ)/4096 < 1)
    hf hbound (z := (x : ℂ)) (by
      simp only [sub_zero, Complex.norm_real, Real.norm_eq_abs]
      rw [abs_of_nonneg hx.1]
      norm_num
      linarith [hx.2]) n
  have heq : A * ((1 : ℝ)/4096)^(n+1) / (1-1/4096) =
      A / (4095 * ((64 : ℝ)^n)^2) := by
    rw [pow_succ, div_pow]
    have hp : (4096 : ℝ)^n = ((64 : ℝ)^n)^2 := by
      rw [show (4096 : ℝ) = 64^2 by norm_num, ← pow_mul, Nat.mul_comm, pow_mul]
    rw [hp]
    field_simp
    ring
  rw [heq] at h
  apply h.trans
  apply div_le_div_of_nonneg_left hA (by positivity)
  have hp : 0 ≤ ((64 : ℝ)^n)^2 := sq_nonneg _
  nlinarith


/-- Absorb the linear degree loss into the extrapolation base. -/
theorem propagation_degree_factor_le (n : ℕ) :
    ((n : ℝ)+1) * (21 : ℝ)^n ≤ (64 : ℝ)^n := by
  have hn : (n : ℝ)+1 ≤ (2 : ℝ)^n := by
    induction n with
    | zero => norm_num
    | succ n ih =>
      push_cast
      rw [pow_succ]
      have hp : (1 : ℝ) ≤ 2^n := one_le_pow₀ (by norm_num)
      linarith
  calc
    _ ≤ (2 : ℝ)^n * (21 : ℝ)^n := mul_le_mul_of_nonneg_right hn (by positivity)
    _ = (42 : ℝ)^n := by rw [← mul_pow]; norm_num
    _ ≤ (64 : ℝ)^n := pow_le_pow_left₀ (by norm_num) (by norm_num) n

/-- Balance the finite-degree extrapolation error with the geometric Taylor tail. -/
theorem propagation_geometric_balance {A δ v : ℝ} (hA : 0 ≤ A) (hδ : 0 ≤ δ)
    (hvA : v ≤ A)
    (hbound : ∀ n : ℕ, v ≤ 32 * 64 ^ n * δ + A / 64 ^ n) :
    v ≤ 100 * Real.sqrt (A * δ) := by
  by_cases hv : v ≤ 0
  · exact hv.trans (by positivity)
  have hvpos : 0 < v := lt_of_not_ge hv
  have hApos : 0 < A := hvpos.trans_le hvA
  by_cases hδ0 : δ = 0
  · subst δ
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (A / v) (show (1 : ℝ) < 64 by norm_num)
    have hp : (0 : ℝ) < 64 ^ n := by positivity
    have hAv : A < 64 ^ n * v := (div_lt_iff₀ hvpos).mp hn
    have hh := hbound n
    simp only [mul_zero, zero_add] at hh
    have := (le_div_iff₀ hp).mp hh
    nlinarith
  have hδpos : 0 < δ := lt_of_le_of_ne hδ (Ne.symm hδ0)
  let S := Real.sqrt (A * δ)
  have hSpos : 0 < S := Real.sqrt_pos.2 (mul_pos hApos hδpos)
  have hSsq : S ^ 2 = A * δ := Real.sq_sqrt (mul_nonneg hA hδ)
  by_cases hAδ : A ≤ δ
  · have hAS : A ≤ S := by nlinarith [mul_le_mul_of_nonneg_left hAδ hA]
    change v ≤ 100 * S
    linarith
  have hδA : δ < A := lt_of_not_ge hAδ
  have hδS : δ ≤ S := by nlinarith [mul_le_mul_of_nonneg_right hδA.le hδ]
  have hratio : 1 ≤ S / δ := (le_div_iff₀ hδpos).2 (by simpa using hδS)
  obtain ⟨n, hlo, hhi⟩ := exists_nat_pow_near hratio (show (1 : ℝ) < 64 by norm_num)
  have hp : (0 : ℝ) < 64 ^ n := by positivity
  have hfirst : 64 ^ n * δ ≤ S := (le_div_iff₀ hδpos).mp hlo
  have hupper : S < (64 ^ n * 64) * δ := by
    exact (div_lt_iff₀ hδpos).mp (by simpa only [pow_succ] using hhi)
  have hsecond : A / 64 ^ n < 64 * S := by
    apply (div_lt_iff₀ hp).2
    apply (mul_lt_mul_iff_right₀ hδpos).mp
    nlinarith [mul_lt_mul_of_pos_right hupper hSpos]
  change v ≤ 100 * S
  have hh := hbound n
  nlinarith



/-- On an interval of length at most one, the integral is bounded by the L² norm. -/
theorem propagation_integral_le_sqrt_integral_sq {f : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hlen : b-a ≤ 1) (hf : ContinuousOn f (Icc a b)) :
    (∫ x in a..b, f x) ≤ Real.sqrt (∫ x in a..b, (f x)^2) := by
  let I : ℝ := ∫ x in a..b, f x
  have hfi : IntervalIntegrable f volume a b := hf.intervalIntegrable_of_Icc hab
  have hfsi : IntervalIntegrable (fun x => (f x)^2) volume a b := (hf.pow 2).intervalIntegrable_of_Icc hab
  have hnonneg : 0 ≤ ∫ x in a..b, (f x-I)^2 :=
    intervalIntegral.integral_nonneg hab (fun x hx => sq_nonneg _)
  have heq : (∫ x in a..b, (f x-I)^2) =
      (∫ x in a..b, (f x)^2) - 2*I*I + (b-a)*I^2 := by
    calc
      _ = ∫ x in a..b, (f x)^2 - (2*I)*f x + I^2 := by
        apply intervalIntegral.integral_congr
        intro x hx
        ring
      _ = _ := by
        rw [intervalIntegral.integral_add (hfsi.sub (hfi.const_mul (2*I)))
          intervalIntegrable_const, intervalIntegral.integral_sub hfsi (hfi.const_mul (2*I)),
          intervalIntegral.integral_const_mul, intervalIntegral.integral_const]
        rfl
  rw [heq] at hnonneg
  have hsq : I^2 ≤ ∫ x in a..b, (f x)^2 := by
    have hlen' := mul_le_mul_of_nonneg_right hlen (sq_nonneg I)
    nlinarith
  have hmassnonneg : 0 ≤ ∫ x in a..b, (f x)^2 :=
    intervalIntegral.integral_nonneg hab (fun x hx => sq_nonneg _)
  have hsqrt : (Real.sqrt (∫ x in a..b, (f x)^2))^2 = ∫ x in a..b, (f x)^2 :=
    Real.sq_sqrt hmassnonneg
  change I ≤ _
  nlinarith [Real.sqrt_nonneg (∫ x in a..b, (f x)^2)]

/-- Uniform error bounds perturb the interval L² norm by at most the error when length ≤ 1. -/
theorem propagation_l2_error {F G : ℝ → ℂ} {a b R : ℝ}
    (hab : a ≤ b) (hlen : b-a ≤ 1)
    (hF : ContinuousOn F (Icc a b)) (hG : ContinuousOn G (Icc a b))
    (hR : 0 ≤ R) (hFG : ∀ x ∈ Icc a b, ‖F x-G x‖ ≤ R) :
    Real.sqrt (∫ x in a..b, ‖G x‖^2) ≤
      Real.sqrt (∫ x in a..b, ‖F x‖^2) + R := by
  have hfi : IntervalIntegrable (fun x => ‖F x‖) volume a b := hF.norm.intervalIntegrable_of_Icc hab
  have hfsi : IntervalIntegrable (fun x => ‖F x‖^2) volume a b := (hF.norm.pow 2).intervalIntegrable_of_Icc hab
  have hgsi : IntervalIntegrable (fun x => ‖G x‖^2) volume a b := (hG.norm.pow 2).intervalIntegrable_of_Icc hab
  have hbnd : (∫ x in a..b, ‖G x‖^2) ≤ ∫ x in a..b, (‖F x‖+R)^2 := by
    apply intervalIntegral.integral_mono_on hab hgsi
      ((hF.norm.add continuousOn_const).pow 2 |>.intervalIntegrable_of_Icc hab)
    intro x hx
    have hx' : ‖G x‖ ≤ ‖F x‖+R := by
      calc
        ‖G x‖ = ‖F x - (F x-G x)‖ := by congr 1; abel
        _ ≤ ‖F x‖ + ‖F x-G x‖ := norm_sub_le _ _
        _ ≤ ‖F x‖ + R := add_le_add le_rfl (hFG x hx)
    change ‖G x‖^2 ≤ (‖F x‖+R)^2
    nlinarith [norm_nonneg (F x), norm_nonneg (G x)]
  have heq : (∫ x in a..b, (‖F x‖+R)^2) =
      (∫ x in a..b, ‖F x‖^2) + 2*R*(∫ x in a..b, ‖F x‖) + (b-a)*R^2 := by
    calc
      _ = ∫ x in a..b, ‖F x‖^2 + (2*R)*‖F x‖ + R^2 := by
        apply intervalIntegral.integral_congr
        intro x hx
        ring
      _ = _ := by
        rw [intervalIntegral.integral_add (hfsi.add (hfi.const_mul (2*R)))
          intervalIntegrable_const, intervalIntegral.integral_add hfsi (hfi.const_mul (2*R)),
          intervalIntegral.integral_const_mul, intervalIntegral.integral_const]
        rfl
  rw [heq] at hbnd
  have hnorm := propagation_integral_le_sqrt_integral_sq hab hlen hF.norm
  have hnorm' := mul_le_mul_of_nonneg_left hnorm (show 0 ≤ 2*R by positivity)
  have hlen' := mul_le_mul_of_nonneg_right hlen (sq_nonneg R)
  have hFnonneg : 0 ≤ ∫ x in a..b, ‖F x‖^2 :=
    intervalIntegral.integral_nonneg hab (fun x hx => sq_nonneg _)
  have hGnonneg : 0 ≤ ∫ x in a..b, ‖G x‖^2 :=
    intervalIntegral.integral_nonneg hab (fun x hx => sq_nonneg _)
  have hsF := Real.sq_sqrt hFnonneg
  have hsG := Real.sq_sqrt hGnonneg
  have hFs := Real.sqrt_nonneg (∫ x in a..b, ‖F x‖^2)
  have hGs := Real.sqrt_nonneg (∫ x in a..b, ‖G x‖^2)
  nlinarith

/-- Real polynomial extrapolation with the degree loss absorbed into base `64`. -/
theorem polynomial_extrapolation_l2 (p : ℝ[X]) (n : ℕ)
    (hdeg : p.natDegree ≤ n) {x : ℝ} (hx : x ∈ Icc 0 1) :
    |p.eval x| ≤ 16 * (64 : ℝ)^n *
      Real.sqrt (∫ y in Real.sqrt 2..Real.sqrt 3, (p.eval y)^2) := by
  have h := polynomial_extrapolation_sqrt_interval p n hdeg
    (fun y hy => polynomial_abs_eval_le_sqrt_integral_sqrt_two_three p n hdeg hy) hx
  apply h.trans
  calc
    _ = 16 * (((n : ℝ)+1) * (21 : ℝ)^n) *
        Real.sqrt (∫ y in Real.sqrt 2..Real.sqrt 3, (p.eval y)^2) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (propagation_degree_factor_le n) (by norm_num)) (by positivity)

theorem continuous_taylorPolynomial_real (F : ℂ → ℂ) (n : ℕ) :
    Continuous (fun x : ℝ => taylorPolynomial F 0 n (x : ℂ)) := by
  unfold taylorPolynomial
  fun_prop

/-- The complex Taylor polynomial inherits an actual L² extrapolation estimate. -/
theorem norm_taylorPolynomial_le_l2 (F : ℂ → ℂ) (n : ℕ)
    {x : ℝ} (hx : x ∈ Icc 0 1) :
    ‖taylorPolynomial F 0 n (x : ℂ)‖ ≤ 32 * (64 : ℝ)^n *
      Real.sqrt (∫ y in Real.sqrt 2..Real.sqrt 3, ‖taylorPolynomial F 0 n (y : ℂ)‖^2) := by
  have hab : Real.sqrt 2 ≤ Real.sqrt 3 := Real.sqrt_le_sqrt (by norm_num)
  have hreal : Real.sqrt (∫ y in Real.sqrt 2..Real.sqrt 3,
        ((realTaylorPolynomial F n).eval y)^2) ≤
      Real.sqrt (∫ y in Real.sqrt 2..Real.sqrt 3, ‖taylorPolynomial F 0 n (y : ℂ)‖^2) := by
    apply Real.sqrt_le_sqrt
    apply intervalIntegral.integral_mono_on hab
      ((realTaylorPolynomial F n).continuous.pow 2 |>.intervalIntegrable _ _)
      ((continuous_taylorPolynomial_real F n).norm.pow 2 |>.intervalIntegrable _ _)
    intro y _
    change ((realTaylorPolynomial F n).eval y)^2 ≤ ‖taylorPolynomial F 0 n (y : ℂ)‖^2
    rw [realTaylorPolynomial_eval]
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).mpr
      (Complex.abs_re_le_norm (taylorPolynomial F 0 n (y : ℂ)))
  have himag : Real.sqrt (∫ y in Real.sqrt 2..Real.sqrt 3,
        ((imagTaylorPolynomial F n).eval y)^2) ≤
      Real.sqrt (∫ y in Real.sqrt 2..Real.sqrt 3, ‖taylorPolynomial F 0 n (y : ℂ)‖^2) := by
    apply Real.sqrt_le_sqrt
    apply intervalIntegral.integral_mono_on hab
      ((imagTaylorPolynomial F n).continuous.pow 2 |>.intervalIntegrable _ _)
      ((continuous_taylorPolynomial_real F n).norm.pow 2 |>.intervalIntegrable _ _)
    intro y _
    change ((imagTaylorPolynomial F n).eval y)^2 ≤ ‖taylorPolynomial F 0 n (y : ℂ)‖^2
    rw [imagTaylorPolynomial_eval]
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).mpr
      (Complex.abs_im_le_norm (taylorPolynomial F 0 n (y : ℂ)))
  have hr := (polynomial_extrapolation_l2 (realTaylorPolynomial F n) n
    (realTaylorPolynomial_natDegree F n) hx).trans
      (mul_le_mul_of_nonneg_left hreal (by positivity))
  have hi := (polynomial_extrapolation_l2 (imagTaylorPolynomial F n) n
    (imagTaylorPolynomial_natDegree F n) hx).trans
      (mul_le_mul_of_nonneg_left himag (by positivity))
  rw [realTaylorPolynomial_eval] at hr
  rw [imagTaylorPolynomial_eval] at hi
  have hnorm := Complex.norm_le_abs_re_add_abs_im (taylorPolynomial F 0 n (x : ℂ))
  linarith

/-- Restrict the actual holomorphic function continuously to the relevant real segment. -/
theorem fixedDisk_continuousOn_real {F : ℂ → ℂ}
    (hf : DiffContOnCl ℂ F (ball 0 16384)) :
    ContinuousOn (fun x : ℝ => F (x : ℂ)) (Icc 0 2) := by
  have hc : ContinuousOn F (closedBall (0 : ℂ) 16384) := by
    simpa only [closure_ball (0 : ℂ) (by norm_num : (16384 : ℝ) ≠ 0)] using hf.continuousOn
  apply hc.comp Complex.continuous_ofReal.continuousOn
  intro x hx
  simp only [mem_closedBall, dist_zero_right, Complex.norm_real, Real.norm_eq_abs]
  rw [abs_of_nonneg hx.1]
  linarith [hx.2]

/-- The observation interval integral in the propagation statement is an actual
finite L² integral. -/
theorem fixedDisk_observation_intervalIntegrable {F : ℂ → ℂ}
    (hf : DiffContOnCl ℂ F (ball 0 16384)) :
    IntervalIntegrable (fun x : ℝ => ‖F (x : ℂ)‖^2) volume (Real.sqrt 2) (Real.sqrt 3) := by
  have hsub : Icc (Real.sqrt 2) (Real.sqrt 3) ⊆ Icc (0 : ℝ) 2 :=
    Icc_subset_Icc (Real.sqrt_nonneg _) sqrt_three_le_two
  exact (((fixedDisk_continuousOn_real hf).mono hsub).norm.pow 2).intervalIntegrable_of_Icc
    (Real.sqrt_le_sqrt (by norm_num))

/-- Quantitative propagation with the exact default disk, exponent, and
constant. The inner square root is the actual ordinary L² norm on `[√2,√3]`. -/
theorem norm_le_sqrt_l2_of_fixed_disk {F : ℂ → ℂ} {A : ℝ} (hA : 0 ≤ A)
    (hf : DiffContOnCl ℂ F (ball 0 16384))
    (hbound : ∀ z ∈ closedBall (0 : ℂ) 16384, ‖F z‖ ≤ A)
    {x : ℝ} (hx : x ∈ Icc 0 1) :
    ‖F (x : ℂ)‖ ≤ 100 * Real.sqrt
      (A * Real.sqrt (∫ t in Real.sqrt 2..Real.sqrt 3, ‖F (t : ℂ)‖^2)) := by
  let δ := Real.sqrt (∫ t in Real.sqrt 2..Real.sqrt 3, ‖F (t : ℂ)‖^2)
  have hδ : 0 ≤ δ := Real.sqrt_nonneg _
  have hx2 : x ∈ Icc (0 : ℝ) 2 := ⟨hx.1, hx.2.trans (by norm_num)⟩
  have hFx : ‖F (x : ℂ)‖ ≤ A := by
    apply hbound
    simp only [mem_closedBall, dist_zero_right, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_nonneg hx.1]
    linarith [hx.2]
  apply propagation_geometric_balance hA hδ hFx
  intro n
  let Rn := A / (64 * ((64 : ℝ)^n)^2)
  have hRn : 0 ≤ Rn := by dsimp [Rn]; positivity
  have hboundary : ∀ z ∈ sphere (0 : ℂ) 16384, ‖F z‖ ≤ A :=
    fun z hz => hbound z (sphere_subset_closedBall hz)
  have hsub : Icc (Real.sqrt 2) (Real.sqrt 3) ⊆ Icc (0 : ℝ) 2 :=
    Icc_subset_Icc (Real.sqrt_nonneg _) sqrt_three_le_two
  have hFcont := (fixedDisk_continuousOn_real hf).mono hsub
  have hperturb := propagation_l2_error
    (Real.sqrt_le_sqrt (show (2 : ℝ) ≤ 3 by norm_num)) sqrt_interval_length_le_one
    hFcont (continuous_taylorPolynomial_real F n).continuousOn hRn
    (fun y hy => propagation_taylor_error hA hf hboundary n (hsub hy))
  have hpoly := norm_taylorPolynomial_le_l2 F n hx
  have htarget := propagation_taylor_error hA hf hboundary n hx2
  have htail : (32*(64 : ℝ)^n+1)*Rn ≤ A/(64 : ℝ)^n := by
    have hpow : (1 : ℝ) ≤ 64^n := one_le_pow₀ (by norm_num)
    calc
      _ ≤ (64*(64 : ℝ)^n)*Rn := mul_le_mul_of_nonneg_right (by nlinarith) hRn
      _ = _ := by
        dsimp [Rn]
        field_simp
  calc
    ‖F (x : ℂ)‖ ≤ ‖F (x : ℂ)-taylorPolynomial F 0 n (x : ℂ)‖ +
        ‖taylorPolynomial F 0 n (x : ℂ)‖ := norm_le_norm_sub_add _ _
    _ ≤ Rn + 32*(64 : ℝ)^n*(δ+Rn) :=
      add_le_add htarget (hpoly.trans (mul_le_mul_of_nonneg_left hperturb (by positivity)))
    _ = 32*(64 : ℝ)^n*δ + (32*(64 : ℝ)^n+1)*Rn := by ring
    _ ≤ _ := add_le_add le_rfl htail

end GapFamily.Analytic
