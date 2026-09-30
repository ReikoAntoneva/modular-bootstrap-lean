import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

namespace GapFamily.Analytic.SelbergClearedProduct

variable {ι : Type*} [DecidableEq ι]

/-- Clearing all finite denominators is valid even where some denominator vanishes. -/
theorem cleared_identity_of_finite_sum (s : Finset ι)
    {D0 Z0 A0 : ℂ} {D Z A c : ι → ℂ}
    (hA0 : A0 = D0 * Z0) (hA : ∀ i ∈ s, A i = D i * Z i)
    (hsum : Z0 = ∑ i ∈ s, c i * Z i) :
    A0 * (∏ i ∈ s, D i) =
      D0 * ∑ i ∈ s, c i * A i * ∏ e ∈ s.erase i, D e := by
  rw [hA0, hsum, mul_assoc, Finset.sum_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [hA i hi, ← Finset.mul_prod_erase s D hi]
  ring

/-- At unit coefficients the cleared identity recovers the original sum
whenever all of its actual denominator factors are nonzero. -/
theorem finite_sum_of_cleared_identity (s : Finset ι)
    {D0 Z0 A0 : ℂ} {D Z A : ι → ℂ}
    (hD0 : D0 ≠ 0) (hD : ∀ i ∈ s, D i ≠ 0)
    (hA0 : A0 = D0 * Z0) (hA : ∀ i ∈ s, A i = D i * Z i)
    (hcleared : A0 * (∏ i ∈ s, D i) =
      D0 * ∑ i ∈ s, A i * ∏ e ∈ s.erase i, D e) :
    Z0 = ∑ i ∈ s, Z i := by
  have hprod : (∏ i ∈ s, D i) ≠ 0 := Finset.prod_ne_zero_iff.mpr hD
  have hfactor : (∑ i ∈ s, A i * ∏ e ∈ s.erase i, D e) =
      (∑ i ∈ s, Z i) * ∏ e ∈ s, D e := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    rw [hA i hi, ← Finset.mul_prod_erase s D hi]
    ring
  apply mul_left_cancel₀ hD0
  apply mul_right_cancel₀ hprod
  calc
    (D0 * Z0) * (∏ i ∈ s, D i) = A0 * (∏ i ∈ s, D i) := by rw [hA0]
    _ = D0 * ∑ i ∈ s, A i * ∏ e ∈ s.erase i, D e := hcleared
    _ = (D0 * ∑ i ∈ s, Z i) * ∏ e ∈ s, D e := by rw [hfactor, mul_assoc]

end GapFamily.Analytic.SelbergClearedProduct
