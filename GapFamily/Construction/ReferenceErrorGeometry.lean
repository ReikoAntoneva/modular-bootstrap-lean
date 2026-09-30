import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Uniform geometry of the reference-error exponent

Above the reference threshold, all polynomial parameters are controlled by
the product `a * e`. A fixed enlargement of that threshold also absorbs the
input-band exponential losses into one square-root output-energy exponent.
-/

open Real

namespace GapFamily.Construction

/-- Every additive polynomial parameter is bounded by the output product. -/
theorem referenceError_polynomial_base_le {a b e : ℝ}
    (hb : 1 ≤ b) (ha : b ≤ a) (he : 1 ≤ e) :
    1 + a + b + e ≤ 4 * (a * e) := by
  have ha1 : 1 ≤ a := hb.trans ha
  have hae : a ≤ a * e := le_mul_of_one_le_right (zero_le_one.trans ha1) he
  have hea : e ≤ a * e := le_mul_of_one_le_left (zero_le_one.trans he) ha1
  have hbae : b ≤ a * e := ha.trans hae
  have h1ae : 1 ≤ a * e := ha1.trans hae
  linarith

/-- Polynomial loss is a fixed power of the square-root output energy. -/
theorem referenceError_polynomial_le_sqrt_pow (p : ℕ) {a b e : ℝ}
    (hb : 1 ≤ b) (ha : b ≤ a) (he : 1 ≤ e) :
    (1 + a + b + e) ^ p ≤ (4 : ℝ) ^ p * (sqrt (a * e)) ^ (2 * p) := by
  have ha0 : 0 ≤ a := zero_le_one.trans (hb.trans ha)
  have he0 : 0 ≤ e := zero_le_one.trans he
  calc
    _ ≤ (4 * (a * e)) ^ p :=
      pow_le_pow_left₀ (by positivity) (referenceError_polynomial_base_le hb ha he) p
    _ = _ := by rw [mul_pow, pow_mul, sq_sqrt (mul_nonneg ha0 he0)]

/-- The square-root output product dominates the band scale. -/
theorem referenceError_sqrt_product_ge {a b e : ℝ}
    (hb : 0 ≤ b) (ha : b ≤ a) (he : b ≤ e) : b ≤ sqrt (a * e) := by
  apply (le_sqrt hb (mul_nonneg (hb.trans ha) (hb.trans he))).mpr
  simpa only [pow_two] using mul_le_mul ha he hb (hb.trans ha)

/-- A fixed threshold enlargement absorbs both the square-root input-band
loss and the linear band loss into the square-root output exponent. -/
theorem referenceError_exponent_le_sqrt {a b e C D R : ℝ}
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hb : 1 ≤ b) (ha : b ≤ a)
    (hR : (C + D) ^ 2 ≤ R) (he : R * b ≤ e) :
    C * sqrt (a * b) + D * b ≤ sqrt (a * e) := by
  have hb0 : 0 ≤ b := zero_le_one.trans hb
  have ha0 : 0 ≤ a := hb0.trans ha
  have hab0 : 0 ≤ a * b := mul_nonneg ha0 hb0
  have hR0 : 0 ≤ R := (sq_nonneg (C + D)).trans hR
  have he0 : 0 ≤ e := (mul_nonneg hR0 hb0).trans he
  have hbs : b ≤ sqrt (a * b) := referenceError_sqrt_product_ge hb0 ha le_rfl
  calc
    _ ≤ (C + D) * sqrt (a * b) := by
      nlinarith [mul_le_mul_of_nonneg_left hbs hD]
    _ ≤ sqrt (a * e) := by
      apply (le_sqrt (mul_nonneg (add_nonneg hC hD) (sqrt_nonneg _))
        (mul_nonneg ha0 he0)).mpr
      calc
        _ = (C + D) ^ 2 * (a * b) := by rw [mul_pow, sq_sqrt hab0]
        _ ≤ R * (a * b) := mul_le_mul_of_nonneg_right hR hab0
        _ = a * (R * b) := by ring
        _ ≤ a * e := mul_le_mul_of_nonneg_left he ha0

end GapFamily.Construction
