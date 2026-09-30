import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Extremal
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Polynomial extrapolation across the observation gap

Chebyshev extremality bounds a degree-`k` real polynomial outside an interval
by the corresponding Chebyshev polynomial. On the normalized region `[1,10]`,
the elementary three-term recurrence gives the explicit growth factor `21^k`.
The physical observation interval `[√2,√3]` and target `[0,1]` fit inside this
region after affine reflection. This is the polynomial step of the propagation estimate.
-/

open Set Polynomial

namespace GapFamily.Analytic

/-- A uniform exponential Chebyshev bound on the explicit normalized region. -/
theorem chebyshev_eval_abs_le_twenty_one_pow (k : ℕ) (t : ℝ) (ht : |t| ≤ 10) :
    |(Polynomial.Chebyshev.T ℝ (k : ℤ)).eval t| ≤ (21 : ℝ) ^ k := by
  induction k using Nat.twoStepInduction with
  | zero => simp
  | one => simpa using (ht.trans (by norm_num : (10 : ℝ) ≤ 21))
  | more n hn hn1 =>
    have heq : (Polynomial.Chebyshev.T ℝ ((n + 2 : ℕ) : ℤ)).eval t =
        2 * t * (Polynomial.Chebyshev.T ℝ ((n + 1 : ℕ) : ℤ)).eval t -
          (Polynomial.Chebyshev.T ℝ (n : ℤ)).eval t := by
      push_cast
      simp only [Polynomial.Chebyshev.T_add_two, eval_sub, eval_mul, eval_ofNat, eval_X]
    rw [heq]
    calc
      |2 * t * (Polynomial.Chebyshev.T ℝ ((n + 1 : ℕ) : ℤ)).eval t -
          (Polynomial.Chebyshev.T ℝ (n : ℤ)).eval t| ≤
          |2 * t * (Polynomial.Chebyshev.T ℝ ((n + 1 : ℕ) : ℤ)).eval t| +
            |(Polynomial.Chebyshev.T ℝ (n : ℤ)).eval t| := abs_sub _ _
      _ = 2 * |t| * |(Polynomial.Chebyshev.T ℝ ((n + 1 : ℕ) : ℤ)).eval t| +
            |(Polynomial.Chebyshev.T ℝ (n : ℤ)).eval t| := by
              rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      _ ≤ 2 * 10 * (21 : ℝ) ^ (n + 1) + 21 ^ n := by
        gcongr
      _ ≤ 21 ^ (n + 2) := by
        simp only [pow_succ]
        nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 21) n]

/-- Chebyshev extremality with an arbitrary nonnegative magnitude bound. -/
theorem polynomial_eval_abs_le_chebyshev (p : Polynomial ℝ) (k : ℕ)
    (hdeg : p.natDegree ≤ k) {M t : ℝ} (hM : 0 ≤ M) (ht : 1 ≤ t)
    (hbnd : ∀ x ∈ Set.Icc (-1 : ℝ) 1, |p.eval x| ≤ M) :
    |p.eval t| ≤ (Polynomial.Chebyshev.T ℝ (k : ℤ)).eval t * M := by
  by_cases hM0 : M = 0
  · have hp : p = 0 := by
      apply p.eq_zero_of_infinite_isRoot
      apply (Set.Icc_infinite (show (-1 : ℝ) < 1 by norm_num)).mono
      intro x hx
      exact abs_nonpos_iff.mp (by simpa [hM0] using hbnd x hx)
    simp [hp, hM0]
  have hMpos : 0 < M := lt_of_le_of_ne hM (Ne.symm hM0)
  let q : Polynomial ℝ := C M⁻¹ * p
  have hqdeg : q.degree ≤ (k : WithBot ℕ) := by
    apply natDegree_le_iff_degree_le.mp
    exact (natDegree_C_mul_le _ _).trans hdeg
  have hqbnd : ∀ x ∈ Set.Icc (-1 : ℝ) 1, |q.eval x| ≤ 1 := by
    intro x hx
    dsimp [q]
    rw [eval_mul, eval_C, abs_mul, abs_of_pos (inv_pos.mpr hMpos)]
    have := mul_le_mul_of_nonneg_left (hbnd x hx) (le_of_lt (inv_pos.mpr hMpos))
    simpa [hM0] using this
  have hup := Chebyshev.eval_iterate_derivative_le_of_forall_abs_le_one
    (k := 0) ht hqdeg hqbnd
  have hneg := Chebyshev.eval_iterate_derivative_le_of_forall_abs_le_one
    (k := 0) (P := -q) (n := k) ht
    (by simpa using hqdeg) (by intro x hx; simpa using hqbnd x hx)
  simp only [Function.iterate_zero, id_eq, eval_neg] at hup hneg
  have habs : |q.eval t| ≤ (Chebyshev.T ℝ (k:ℤ)).eval t := abs_le.mpr ⟨by linarith, hup⟩
  dsimp [q] at habs
  simp only [eval_mul, eval_C, abs_mul, abs_of_pos (inv_pos.mpr hMpos)] at habs
  have := mul_le_mul_of_nonneg_left habs hM
  simpa [← mul_assoc, hM0, mul_comm M] using this

/-- Quantitative extrapolation from `[-1,1]` to the normalized interval `[1,10]`. -/
theorem polynomial_extrapolation_normalized (p : Polynomial ℝ) (k : ℕ)
    (hdeg : p.natDegree ≤ k) {M t : ℝ} (hM : 0 ≤ M) (ht : t ∈ Set.Icc 1 10)
    (hbnd : ∀ x ∈ Set.Icc (-1 : ℝ) 1, |p.eval x| ≤ M) :
    |p.eval t| ≤ (21 : ℝ)^k * M := by
  apply (polynomial_eval_abs_le_chebyshev p k hdeg hM ht.1 hbnd).trans
  apply mul_le_mul_of_nonneg_right _ hM
  exact (le_abs_self _).trans (chebyshev_eval_abs_le_twenty_one_pow k _ (by rw [abs_of_nonneg (by linarith [ht.1])]; exact ht.2))

/-- Affine reflection transports the normalized estimate to any nondegenerate
observation interval. -/
theorem polynomial_extrapolation_of_affine_coordinate
    (p : Polynomial ℝ) (k : ℕ) {a b M x : ℝ} (hab : a < b)
    (hdeg : p.natDegree ≤ k) (hbound : ∀ y ∈ Set.Icc a b, |p.eval y| ≤ M)
    (hx : (a+b-2*x)/(b-a) ∈ Set.Icc 1 10) :
    |p.eval x| ≤ (21 : ℝ)^k * M := by
  let q : Polynomial ℝ := p.comp (C ((a+b)/2) - C ((b-a)/2) * X)
  have hM : 0 ≤ M := (abs_nonneg (p.eval a)).trans (hbound a ⟨le_rfl, hab.le⟩)
  have hlin : (C ((a+b)/2) - C ((b-a)/2) * X : Polynomial ℝ).natDegree ≤ 1 := by
    apply (Polynomial.natDegree_sub_le _ _).trans
    apply max_le (by simp)
    simpa only [pow_one] using Polynomial.natDegree_C_mul_X_pow_le ((b-a)/2) 1
  have hqdeg : q.natDegree ≤ k := by
    exact Polynomial.natDegree_comp_le.trans ((Nat.mul_le_mul_left _ hlin).trans (by simpa using hdeg))
  have hqbound : ∀ t ∈ Set.Icc (-1) 1, |q.eval t| ≤ M := by
    intro t ht
    simp only [q, Polynomial.eval_comp, Polynomial.eval_sub, Polynomial.eval_C,
      Polynomial.eval_mul, Polynomial.eval_X]
    apply hbound
    have hmul₁ := mul_le_mul_of_nonneg_left ht.1 (show 0 ≤ (b-a)/2 by linarith)
    have hmul₂ := mul_le_mul_of_nonneg_left ht.2 (show 0 ≤ (b-a)/2 by linarith)
    constructor <;> linarith
  have hq := polynomial_extrapolation_normalized q k hqdeg hM hx hqbound
  have hinner : (a+b)/2 - (b-a)/2 * ((a+b-2*x)/(b-a)) = x := by
    field_simp [show b-a ≠ 0 from (sub_pos.mpr hab).ne']
    ring
  simpa only [q, Polynomial.eval_comp, Polynomial.eval_sub, Polynomial.eval_C,
    Polynomial.eval_mul, Polynomial.eval_X, hinner] using hq


/-- The actual observation and target intervals in the fixed-disk propagation
lemma. -/
theorem polynomial_extrapolation_sqrt_interval
    (p : Polynomial ℝ) (k : ℕ) {M x : ℝ}
    (hdeg : p.natDegree ≤ k)
    (hbound : ∀ y ∈ Set.Icc (Real.sqrt 2) (Real.sqrt 3), |p.eval y| ≤ M)
    (hx : x ∈ Set.Icc 0 1) :
    |p.eval x| ≤ (21 : ℝ)^k * M := by
  have h23 : Real.sqrt 2 < Real.sqrt 3 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  apply polynomial_extrapolation_of_affine_coordinate p k h23 hdeg hbound
  have hden : 0 < Real.sqrt 3 - Real.sqrt 2 := sub_pos.mpr h23
  have h2 : 1 ≤ Real.sqrt 2 := Real.one_le_sqrt.mpr (by norm_num)
  have h23bound : 11 * Real.sqrt 2 ≤ 9 * Real.sqrt 3 := by
    apply (sq_le_sq₀ (by positivity) (by positivity)).mp
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num),
      Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
  constructor
  · apply (le_div_iff₀ hden).mpr
    nlinarith [hx.2]
  · apply (div_le_iff₀ hden).mpr
    nlinarith [hx.1]


end GapFamily.Analytic
