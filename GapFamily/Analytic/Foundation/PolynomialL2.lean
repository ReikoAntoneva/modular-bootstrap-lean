import GapFamily.Quadrature.PolynomialBound

/-!
# Interval L² control of a real polynomial

Apply the polynomial derivative estimate to the square of a polynomial and
integrate beside its maximum. The resulting supremum estimate has linear
rather than exponential degree loss after taking a square root.
-/

open Set MeasureTheory

namespace GapFamily.Analytic

/-- On a nondegenerate real interval, the square of a degree-`k` polynomial is
bounded by its integral with quadratic degree loss. -/
theorem polynomial_sq_eval_le_integral
    (p : Polynomial ℝ) (k : ℕ) {a b : ℝ} (hab : a < b)
    (hdeg : p.natDegree ≤ k) {x : ℝ} (hx : x ∈ Icc a b) :
    (p.eval x) ^ 2 ≤ (64 * ((k : ℝ) + 1) ^ 2 / (b - a)) *
      ∫ y in a..b, (p.eval y) ^ 2 := by
  let q := p ^ 2
  have hqdeg : q.natDegree ≤ 2 * k := by
    exact (Polynomial.natDegree_pow_le).trans (by omega)
  have hqpos (y : ℝ) : 0 ≤ q.eval y := by
    simp only [q, Polynomial.eval_pow]
    exact sq_nonneg _
  obtain ⟨t, ht, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (nonempty_Icc.mpr hab.le) q.continuous.continuousOn
  have hbnd (y : ℝ) (hy : y ∈ Icc a b) : |q.eval y| ≤ q.eval t := by
    rw [abs_of_nonneg (hqpos y)]
    exact hmax hy
  have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
  have hR : 1 ≤ 4 * ((k : ℝ) + 1) ^ 2 := by nlinarith [sq_nonneg (k : ℝ)]
  have hpeak : q.eval t ≤ (16 * (4 * ((k : ℝ) + 1) ^ 2) / (b - a)) *
      ∫ y in a..b, q.eval y := by
    apply GapFamily.Quadrature.peak_le_integral_of_lipschitz_bound hab hR
      q.continuous.continuousOn (fun y _ => hqpos y) ht rfl
    intro y hy
    have hdbound : ∀ z ∈ Icc a b, ‖deriv q.eval z‖ ≤
        4 * (4 * ((k : ℝ) + 1) ^ 2) * q.eval t / (b - a) := by
      intro z hz
      have hbase := GapFamily.Quadrature.polynomial_derivative_abs_le_interval
        q (2 * k) hab hqdeg hbnd hz
      rw [q.deriv, Real.norm_eq_abs]
      apply hbase.trans
      apply div_le_div_of_nonneg_right _ (sub_nonneg.mpr hab.le)
      apply mul_le_mul_of_nonneg_right _ (hqpos t)
      norm_num only [Nat.cast_mul, Nat.cast_ofNat]
      nlinarith [sq_nonneg (k : ℝ)]
    simpa only [Real.norm_eq_abs] using Convex.norm_image_sub_le_of_norm_deriv_le
      (fun z (_ : z ∈ Icc a b) => q.differentiable.differentiableAt)
      hdbound (convex_Icc a b) ht hy
  have hbound := (hmax hx).trans hpeak
  simpa only [q, Polynomial.eval_pow, show (16 : ℝ) * (4 * ((k : ℝ) + 1) ^ 2) =
    64 * ((k : ℝ) + 1) ^ 2 by ring] using hbound

/-- The fixed interval in the propagation estimate has length greater than a quarter. -/
theorem sqrt_interval_length_gt_quarter :
    (1 / 4 : ℝ) < Real.sqrt 3 - Real.sqrt 2 := by
  have h₃ : (17 / 10 : ℝ) < Real.sqrt 3 := by
    apply Real.lt_sqrt_of_sq_lt
    norm_num
  have h₂ : Real.sqrt 2 < (29 / 20 : ℝ) := by
    apply (Real.sqrt_lt (by norm_num) (by norm_num)).2
    norm_num
  linarith

/-- The fixed propagation interval has length at most one. -/
theorem sqrt_interval_length_le_one : Real.sqrt 3 - Real.sqrt 2 ≤ 1 := by
  have h₂ : (1 : ℝ) ≤ Real.sqrt 2 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg (2 : ℝ)]
  have h₃ : Real.sqrt 3 ≤ (2 : ℝ) := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), Real.sqrt_nonneg (3 : ℝ)]
  linarith

/-- The right endpoint of the propagation interval lies within radius two. -/
theorem sqrt_three_le_two : Real.sqrt 3 ≤ (2 : ℝ) := by
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), Real.sqrt_nonneg (3 : ℝ)]

/-- On any interval of length at least a quarter, ordinary L² mass controls
point evaluation with the explicit linear degree loss `16 (k + 1)`. -/
theorem polynomial_abs_eval_le_sqrt_integral_of_length
    (p : Polynomial ℝ) (k : ℕ) {a b : ℝ} (hwidth : 1 / 4 ≤ b - a)
    (hdeg : p.natDegree ≤ k) {x : ℝ} (hx : x ∈ Icc a b) :
    |p.eval x| ≤ 16 * ((k : ℝ) + 1) *
      Real.sqrt (∫ y in a..b, (p.eval y) ^ 2) := by
  have hdpos : 0 < b - a := by linarith
  have hab : a < b := sub_pos.mp hdpos
  have hI : 0 ≤ ∫ y in a..b, (p.eval y) ^ 2 :=
    intervalIntegral.integral_nonneg hab.le (fun y _ => sq_nonneg _)
  have hfrac : 64 * ((k : ℝ) + 1) ^ 2 / (b - a) ≤
      256 * ((k : ℝ) + 1) ^ 2 := by
    apply (div_le_iff₀ hdpos).2
    nlinarith [sq_nonneg ((k : ℝ) + 1)]
  have hsq : (p.eval x) ^ 2 ≤
      (16 * ((k : ℝ) + 1) * Real.sqrt (∫ y in a..b, (p.eval y) ^ 2)) ^ 2 := by
    calc
      (p.eval x) ^ 2 ≤ (256 * ((k : ℝ) + 1) ^ 2) *
          (∫ y in a..b, (p.eval y) ^ 2) :=
        (polynomial_sq_eval_le_integral p k hab hdeg hx).trans
          (mul_le_mul_of_nonneg_right hfrac hI)
      _ = _ := by
        rw [mul_pow, mul_pow, Real.sq_sqrt hI]
        ring
  exact (sq_le_sq₀ (abs_nonneg _) (by positivity)).1 (by simpa using hsq)

/-- The real polynomial L² estimate on the fixed propagation interval. -/
theorem polynomial_abs_eval_le_sqrt_integral_sqrt_two_three
    (p : Polynomial ℝ) (k : ℕ) (hdeg : p.natDegree ≤ k)
    {x : ℝ} (hx : x ∈ Icc (Real.sqrt 2) (Real.sqrt 3)) :
    |p.eval x| ≤ 16 * ((k : ℝ) + 1) *
      Real.sqrt (∫ y in Real.sqrt 2..Real.sqrt 3, (p.eval y) ^ 2) :=
  polynomial_abs_eval_le_sqrt_integral_of_length p k
    sqrt_interval_length_gt_quarter.le hdeg hx

end GapFamily.Analytic
