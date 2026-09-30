import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.PSeries

/-!
# Fourier decay of smooth periodic functions

Repeated integration by parts gives quantitative decay with an explicit derivative
bound. These estimates apply uniformly to a family whenever its derivative bound
is uniform.
-/

noncomputable section

open MeasureTheory Set
open scoped Real ContDiff

namespace BTZEntropy

/-- Translation invariance passes to every derivative, without regularity assumptions. -/
theorem periodic_iteratedDeriv {f : ℝ → ℂ} {T : ℝ}
    (hf : Function.Periodic f T) (p : ℕ) :
    Function.Periodic (iteratedDeriv p f) T := by
  have h := congrArg (iteratedDeriv p) (funext hf)
  rw [iteratedDeriv_comp_add_const] at h
  exact fun x => congrFun h x

/-- The absolute Fourier coefficient is bounded by the integral of the absolute value. -/
theorem norm_fourierCoeffOn_le_integral (f : ℝ → ℂ) (n : ℤ) :
    ‖fourierCoeffOn (by norm_num : (0 : ℝ) < 1) f n‖ ≤
      ∫ x in (0 : ℝ)..1, ‖f x‖ := by
  rw [fourierCoeffOn_eq_integral]
  simp only [sub_zero, div_one, one_smul]
  simpa only [norm_smul, fourier_apply, Circle.norm_coe, one_mul] using
    intervalIntegral.norm_integral_le_integral_norm (by norm_num : (0 : ℝ) ≤ 1)
      (μ := volume) (f := fun x => fourier (-n) (x : AddCircle ((1 : ℝ) - 0)) • f x)

/-- A bound on one period controls every Fourier coefficient. -/
theorem norm_fourierCoeffOn_le_of_bound {f : ℝ → ℂ} {C : ℝ}
    (hC : ∀ x ∈ Icc (0 : ℝ) 1, ‖f x‖ ≤ C) (n : ℤ) :
    ‖fourierCoeffOn (by norm_num : (0 : ℝ) < 1) f n‖ ≤ C := by
  rw [fourierCoeffOn_eq_integral]
  simp only [sub_zero, div_one, one_smul]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := 1) (C := C)
    (f := fun x => fourier (-n) (x : AddCircle (1 : ℝ)) • f x) ?_
  · simpa using h
  · intro x hx
    simp only [norm_smul, fourier_apply, Circle.norm_coe, one_mul]
    exact hC x (Ioc_subset_Icc_self (by simpa using hx))

/-- Repeated integration by parts, with all boundary terms canceled by periodicity. -/
theorem fourierCoeffOn_eq_iteratedDeriv {f : ℝ → ℂ}
    (hf : ContDiff ℝ ∞ f) (hperiod : Function.Periodic f 1)
    (p : ℕ) {n : ℤ} (hn : n ≠ 0) :
    fourierCoeffOn (by norm_num : (0 : ℝ) < 1) f n =
      (1 / (2 * Real.pi * Complex.I * n)) ^ p *
        fourierCoeffOn (by norm_num : (0 : ℝ) < 1) (iteratedDeriv p f) n := by
  induction p with
  | zero => simp
  | succ p ih =>
      have hstep := fourierCoeffOn_of_hasDerivAt
        (by norm_num : (0 : ℝ) < 1) hn
        (f := iteratedDeriv p f) (f' := iteratedDeriv (p + 1) f)
        (fun x _ => by
          rw [iteratedDeriv_succ]
          exact (hf.differentiable_iteratedDeriv p (by exact_mod_cast ENat.natCast_lt_top p)
            x).hasDerivAt)
        ((hf.continuous_iteratedDeriv (p + 1) (by simp)).intervalIntegrable 0 1)
      have hb : iteratedDeriv p f 1 = iteratedDeriv p f 0 := by
        simpa using periodic_iteratedDeriv hperiod p 0
      rw [hb] at hstep
      simp only [sub_self, mul_zero, Complex.ofReal_one, Complex.ofReal_zero,
        sub_zero, one_mul, zero_sub] at hstep
      rw [ih, hstep, pow_succ]
      simp only [neg_mul, div_neg]
      ring

/-- A derivative supremum gives an explicit inverse-power Fourier bound. -/
theorem norm_fourierCoeffOn_le_derivative_bound {f : ℝ → ℂ}
    (hf : ContDiff ℝ ∞ f) (hperiod : Function.Periodic f 1)
    (p : ℕ) {C : ℝ}
    (hC : ∀ x ∈ Icc (0 : ℝ) 1, ‖iteratedDeriv p f x‖ ≤ C)
    {n : ℤ} (hn : n ≠ 0) :
    ‖fourierCoeffOn (by norm_num : (0 : ℝ) < 1) f n‖ ≤
      C / (2 * Real.pi * ‖(n : ℝ)‖) ^ p := by
  rw [fourierCoeffOn_eq_iteratedDeriv hf hperiod p hn, norm_mul, norm_pow]
  have hnorm : ‖(1 : ℂ) / (2 * Real.pi * Complex.I * n)‖ =
      1 / (2 * Real.pi * ‖(n : ℝ)‖) := by
    simp [Complex.norm_intCast, Real.norm_of_nonneg Real.pi_pos.le]
  rw [hnorm]
  calc
    _ ≤ (1 / (2 * Real.pi * ‖(n : ℝ)‖)) ^ p * C :=
      mul_le_mul_of_nonneg_left (norm_fourierCoeffOn_le_of_bound hC n) (by positivity)
    _ = _ := by rw [div_pow]; ring

/-- The constant in inverse-power decay depends only on a bound for the specified derivative. -/
theorem norm_fourierCoeffOn_le_inverse_pow {f : ℝ → ℂ}
    (hf : ContDiff ℝ ∞ f) (hperiod : Function.Periodic f 1)
    (p : ℕ) {C : ℝ}
    (hC : ∀ x ∈ Icc (0 : ℝ) 1, ‖iteratedDeriv p f x‖ ≤ C)
    {n : ℤ} (hn : n ≠ 0) :
    ‖fourierCoeffOn (by norm_num : (0 : ℝ) < 1) f n‖ ≤
      (C / (2 * Real.pi) ^ p) / ‖(n : ℝ)‖ ^ p := by
  simpa only [mul_pow, div_div] using
    norm_fourierCoeffOn_le_derivative_bound hf hperiod p hC hn

/-- Smooth periodic functions have Fourier decay of every prescribed order. -/
theorem exists_fourierCoeffOn_decay {f : ℝ → ℂ}
    (hf : ContDiff ℝ ∞ f) (hperiod : Function.Periodic f 1) (p : ℕ) :
    ∃ C ≥ 0, ∀ n : ℤ, n ≠ 0 →
      ‖fourierCoeffOn (by norm_num : (0 : ℝ) < 1) f n‖ ≤ C / ‖(n : ℝ)‖ ^ p := by
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    (hf.continuous_iteratedDeriv p (by simp)).continuousOn
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 (by simp))
  exact ⟨M / (2 * Real.pi) ^ p, by positivity,
    fun _ hn => norm_fourierCoeffOn_le_inverse_pow hf hperiod p hM hn⟩

/-- Two extra derivatives give a common summable majorant for weighted coefficients. -/
theorem weighted_fourierCoeffOn_le {f : ℝ → ℂ}
    (hf : ContDiff ℝ ∞ f) (hperiod : Function.Periodic f 1)
    (p : ℕ) {C : ℝ}
    (hC : ∀ x ∈ Icc (0 : ℝ) 1, ‖iteratedDeriv (p + 2) f x‖ ≤ C)
    {n : ℤ} (hn : n ≠ 0) :
    ‖fourierCoeffOn (by norm_num : (0 : ℝ) < 1) f n‖ * (‖(n : ℝ)‖ + 1) ^ p ≤
      (C / (2 * Real.pi) ^ (p + 2) * 2 ^ p) / ‖(n : ℝ)‖ ^ 2 := by
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0 (by simp))
  have hr : 1 ≤ ‖(n : ℝ)‖ := by
    rw [Real.norm_eq_abs]
    exact_mod_cast Int.one_le_abs hn
  have hr0 : 0 < ‖(n : ℝ)‖ := lt_of_lt_of_le zero_lt_one hr
  calc
    _ ≤ ((C / (2 * Real.pi) ^ (p + 2)) / ‖(n : ℝ)‖ ^ (p + 2)) *
        (2 * ‖(n : ℝ)‖) ^ p := by
      apply mul_le_mul (norm_fourierCoeffOn_le_inverse_pow hf hperiod (p + 2) hC hn)
      · exact pow_le_pow_left₀ (by positivity) (by linarith) p
      · positivity
      · positivity
    _ = _ := by
      rw [mul_pow, pow_add]
      field_simp
      rw [mul_pow, pow_add]
      ring

/-- Every polynomially weighted absolute Fourier series of a smooth periodic function converges. -/
theorem summable_weighted_fourierCoeffOn {f : ℝ → ℂ}
    (hf : ContDiff ℝ ∞ f) (hperiod : Function.Periodic f 1) (p : ℕ) :
    Summable (fun n : ℤ =>
      ‖fourierCoeffOn (by norm_num : (0 : ℝ) < 1) f n‖ * (‖(n : ℝ)‖ + 1) ^ p) := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    (hf.continuous_iteratedDeriv (p + 2) (by simp)).continuousOn
  have hs := (Real.summable_one_div_int_pow.mpr (by norm_num : 1 < (2 : ℕ))).mul_left
    (C / (2 * Real.pi) ^ (p + 2) * 2 ^ p)
  apply hs.of_norm_bounded_eventually
  filter_upwards [Filter.eventually_cofinite_ne (0 : ℤ)] with n hn
  rw [Real.norm_of_nonneg (by positivity)]
  have h := weighted_fourierCoeffOn_le hf hperiod p hC hn
  simpa only [Real.norm_eq_abs, sq_abs, one_div, div_eq_mul_inv, one_mul] using h

end BTZEntropy
