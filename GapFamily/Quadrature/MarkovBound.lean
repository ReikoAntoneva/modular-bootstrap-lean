import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Extremal
import Mathlib.Analysis.Convex.Basic
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# A polynomial derivative bound on an interval

Chebyshev extremality controls derivatives at the endpoints of `[-1,1]`.
Affine normalization gives a bound at either endpoint of any subinterval.
For an arbitrary point in `[a,b]`, one adjoining subinterval has at least
half the original length, yielding the uniform constant `4 k² / (b-a)`.
-/

open Set Polynomial

namespace GapFamily.Quadrature

/-- The endpoint Markov bound follows directly from Chebyshev extremality,
including the zero-degree and zero-supremum cases. -/
theorem polynomial_derivative_abs_le_at_one (p : Polynomial ℝ) (k : ℕ) (hdeg : p.natDegree ≤ k)
    (M : ℝ) (hM : 0 ≤ M) (hbnd : ∀ x ∈ Set.Icc (-1 : ℝ) 1, |p.eval x| ≤ M) :
    |p.derivative.eval 1| ≤ (k : ℝ)^2 * M := by
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
    (k := 1) (x := 1) (le_refl 1) hqdeg hqbnd
  have hneg := Chebyshev.eval_iterate_derivative_le_of_forall_abs_le_one
    (k := 1) (x := 1) (P := -q) (n := k) (le_refl 1)
    (by simpa using hqdeg) (by intro x hx; simpa using hqbnd x hx)
  simp only [Function.iterate_one, Chebyshev.derivative_T_eval_one, Int.cast_natCast,
    derivative_neg, eval_neg] at hup hneg
  have habs : |q.derivative.eval 1| ≤ (k : ℝ)^2 := abs_le.mpr ⟨by linarith, hup⟩
  dsimp [q] at habs
  simp only [derivative_C_mul, eval_mul, eval_C, abs_mul,
    abs_of_pos (inv_pos.mpr hMpos)] at habs
  have := mul_le_mul_of_nonneg_left habs hM
  simpa [← mul_assoc, hM0, mul_comm M] using this

/-- Rescaling a bounded polynomial to any oriented segment gives a derivative
bound at its final endpoint. Both segment endpoints stay in the original interval. -/
theorem polynomial_derivative_scaled_le_of_interval_bound
    (p : Polynomial ℝ) (k : ℕ) {a b M u v : ℝ} (hM : 0 ≤ M)
    (hdeg : p.natDegree ≤ k) (hbound : ∀ x ∈ Set.Icc a b, |p.eval x| ≤ M)
    (hu : u ∈ Set.Icc a b) (hv : v ∈ Set.Icc a b) :
    |p.derivative.eval v| * |v - u| ≤ 2 * (k : ℝ)^2 * M := by
  let q : Polynomial ℝ := p.comp (C ((u+v)/2) + C ((v-u)/2) * X)
  have hlin : (C ((u+v)/2) + C ((v-u)/2) * X : Polynomial ℝ).natDegree ≤ 1 := by
    apply (Polynomial.natDegree_add_le _ _).trans
    apply max_le (by simp)
    simpa only [pow_one] using Polynomial.natDegree_C_mul_X_pow_le ((v-u)/2) 1
  have hqdeg : q.natDegree ≤ k := by
    exact Polynomial.natDegree_comp_le.trans ((Nat.mul_le_mul_left _ hlin).trans (by simpa using hdeg))
  have hqbound : ∀ t ∈ Set.Icc (-1) 1, |q.eval t| ≤ M := by
    intro t ht
    simp only [q, Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_C,
      Polynomial.eval_mul, Polynomial.eval_X]
    apply hbound
    have hmem := (convex_Icc a b) hu hv
      (show 0 ≤ (1-t)/2 by linarith [ht.2])
      (show 0 ≤ (1+t)/2 by linarith [ht.1])
      (show (1-t)/2+(1+t)/2 = 1 by ring)
    convert hmem using 1
    simp only [smul_eq_mul]
    ring
  have hend := polynomial_derivative_abs_le_at_one q k hqdeg M hM hqbound
  have hqder : q.derivative.eval 1 = p.derivative.eval v * ((v-u)/2) := by
    simp only [q, Polynomial.derivative_comp, Polynomial.derivative_add,
      Polynomial.derivative_C, Polynomial.derivative_mul, Polynomial.derivative_X,
      zero_mul, mul_one, zero_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X]
    rw [show (u+v)/2+(v-u)/2 = v by ring]
    ring
  rw [hqder, abs_mul, abs_div] at hend
  norm_num at hend
  nlinarith


/-- A uniform derivative bound obtained from the longer of the two intervals
adjoining the evaluation point. -/
theorem polynomial_derivative_abs_le_interval
    (p : Polynomial ℝ) (k : ℕ) {a b M x : ℝ} (hab : a < b)
    (hdeg : p.natDegree ≤ k) (hbound : ∀ y ∈ Set.Icc a b, |p.eval y| ≤ M)
    (hx : x ∈ Set.Icc a b) :
    |p.derivative.eval x| ≤ 4 * (k : ℝ)^2 * M / (b-a) := by
  have hM : 0 ≤ M := (abs_nonneg (p.eval a)).trans (hbound a ⟨le_rfl, hab.le⟩)
  apply (le_div_iff₀ (sub_pos.mpr hab)).mpr
  by_cases hmid : (a+b)/2 ≤ x
  · have hh := polynomial_derivative_scaled_le_of_interval_bound p k hM hdeg hbound
      (u := a) ⟨le_rfl, hab.le⟩ hx
    rw [abs_of_nonneg (sub_nonneg.mpr hx.1)] at hh
    have hprod := mul_nonneg (abs_nonneg (p.derivative.eval x))
      (show 0 ≤ 2*(x-a)-(b-a) by linarith)
    nlinarith
  · have hh := polynomial_derivative_scaled_le_of_interval_bound p k hM hdeg hbound
      (u := b) ⟨hab.le, le_rfl⟩ hx
    rw [abs_of_nonpos (sub_nonpos.mpr hx.2)] at hh
    have hprod := mul_nonneg (abs_nonneg (p.derivative.eval x))
      (show 0 ≤ 2*(b-x)-(b-a) by linarith)
    nlinarith


/-- The slightly weaker degree convention used in construction C3. -/
theorem polynomial_derivative_abs_le_degree_succ_cube
    (p : Polynomial ℝ) (k : ℕ) {a b M x : ℝ} (hab : a < b)
    (hdeg : p.natDegree ≤ k) (hbound : ∀ y ∈ Set.Icc a b, |p.eval y| ≤ M)
    (hx : x ∈ Set.Icc a b) :
    |p.derivative.eval x| ≤ 4 * ((k : ℝ) + 1)^3 * M / (b-a) := by
  apply (polynomial_derivative_abs_le_interval p k hab hdeg hbound hx).trans
  have hM : 0 ≤ M := (abs_nonneg (p.eval a)).trans (hbound a ⟨le_rfl, hab.le⟩)
  have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg _
  have hpow : (k : ℝ)^2 ≤ ((k : ℝ) + 1)^3 := by
    nlinarith [pow_nonneg hk 3, sq_nonneg (k : ℝ)]
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow (by norm_num)) hM)
    (sub_nonneg.mpr hab.le)

end GapFamily.Quadrature
