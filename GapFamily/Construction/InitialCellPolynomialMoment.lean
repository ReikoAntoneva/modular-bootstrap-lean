import GapFamily.Quadrature.PolynomialBound

/-!
# Polynomial moment and variation on an initial cell

A value attained on the upper half of an interval controls its nonnegative
polynomial mass there. A uniform bound on the full interval controls variation.
-/

open Set MeasureTheory
open GapFamily.Quadrature

namespace GapFamily.Construction

/-- Any attained value of a nonnegative polynomial on the upper half of a cell
gives a lower bound for its ordinary mass on that half. -/
theorem polynomial_upperHalf_integral_lower
    (p : Polynomial ℝ) (k : ℕ) {a b t S : ℝ} (hab : a < b)
    (hdeg : p.natDegree ≤ k)
    (hpos : ∀ x ∈ Icc ((a+b)/2) b, 0 ≤ p.eval x)
    (ht : t ∈ Icc ((a+b)/2) b) (hS : p.eval t = S) :
    (b-a) / (32 * ((k : ℝ)+1)^3) * S ≤
      ∫ x in Icc ((a+b)/2) b, p.eval x := by
  have hhalf : (a+b)/2 < b := by linarith
  have hp := polynomial_eval_le_integral p k hhalf hdeg hpos ht
  rw [hS] at hp
  have hd : b-a ≠ 0 := sub_ne_zero.mpr hab.ne'
  have hk : (k : ℝ)+1 ≠ 0 := by positivity
  have hscale : 0 ≤ (b-a) / (32 * ((k : ℝ)+1)^3) := by positivity
  have hmul := mul_le_mul_of_nonneg_left hp hscale
  have heq : (b-a) / (32 * ((k : ℝ)+1)^3) *
      ((16 * ((k : ℝ)+1)^3 / (b-(a+b)/2)) *
        (∫ x in (a+b)/2..b, p.eval x)) = ∫ x in (a+b)/2..b, p.eval x := by
    rw [show b-(a+b)/2 = (b-a)/2 by ring]
    field_simp
    ring
  rw [heq, intervalIntegral.integral_of_le hhalf.le,
    ← integral_Icc_eq_integral_Ioc] at hmul
  exact hmul

/-- The same upper-half mass bound in interval-integral notation. -/
theorem polynomial_upperHalf_intervalIntegral_lower
    (p : Polynomial ℝ) (k : ℕ) {a b t : ℝ} (hab : a < b)
    (hdeg : p.natDegree ≤ k)
    (hpos : ∀ x ∈ Icc ((a+b)/2) b, 0 ≤ p.eval x)
    (ht : t ∈ Icc ((a+b)/2) b) :
    (b-a) / (32 * ((k : ℝ)+1)^3) * p.eval t ≤
      ∫ x in (a+b)/2..b, p.eval x := by
  rw [intervalIntegral.integral_of_le (show (a+b)/2 ≤ b by linarith),
    ← integral_Icc_eq_integral_Ioc]
  exact polynomial_upperHalf_integral_lower p k hab hdeg hpos ht rfl

/-- A uniform polynomial bound controls partition variation with the C3
degree convention. -/
theorem polynomial_variation_le_sup_bound
    (p : Polynomial ℝ) (k : ℕ) {a b M : ℝ} (hab : a < b)
    (hdeg : p.natDegree ≤ k)
    (hbnd : ∀ x ∈ Icc a b, |p.eval x| ≤ M) :
    (eVariationOn p.eval (Icc a b)).toReal ≤ 4 * ((k : ℝ)+1)^3 * M := by
  calc
    _ ≤ ∫ x in a..b, |p.derivative.eval x| :=
      polynomial_variation_le_integral_abs_derivative p hab.le
    _ ≤ ∫ x in a..b, 4 * ((k : ℝ)+1)^3 * M / (b-a) :=
      intervalIntegral.integral_mono_on hab.le
        (p.derivative.continuous.abs.intervalIntegrable a b) intervalIntegrable_const
        (fun x hx => polynomial_derivative_abs_le_degree_succ_cube p k hab hdeg hbnd hx)
    _ = _ := by
      have hd : b-a ≠ 0 := sub_ne_zero.mpr hab.ne'
      simp only [intervalIntegral.integral_const, smul_eq_mul]
      field_simp

end GapFamily.Construction
