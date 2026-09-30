import GapFamily.Construction.ReferenceErrorGeometry
import Mathlib.Analysis.Complex.Exponential

/-!
# Uniform absorption of the reference correction

A fixed enlargement of the reference threshold absorbs the input exponential
loss. Beyond a uniform band scale, one additional term of the exponential
series absorbs any fixed polynomial prefactor. The enlargement can be chosen
before the polynomial constants and before any later cell ratio.
-/

open Real

namespace GapFamily.Construction

/-- A concrete exponential-series threshold absorbs a polynomial with a
quarter of the exponential left as a reserve. -/
theorem referenceError_polynomial_absorption {K x : ℝ}
    (hx : 0 ≤ x) (n : ℕ)
    (hlarge : 4 * K * ((n + 1).factorial : ℝ) ≤ x) :
    K * x ^ n ≤ exp x / 4 := by
  have hfac : 0 < ((n + 1).factorial : ℝ) := by positivity
  have hcoeff : 4 * K ≤ x / ((n + 1).factorial : ℝ) :=
    (le_div_iff₀ hfac).mpr hlarge
  have hterm : 4 * (K * x ^ n) ≤ x ^ (n + 1) / ((n + 1).factorial : ℝ) := by
    calc
      _ = (4 * K) * x ^ n := by ring
      _ ≤ (x / ((n + 1).factorial : ℝ)) * x ^ n :=
        mul_le_mul_of_nonneg_right hcoeff (pow_nonneg hx n)
      _ = _ := by rw [pow_succ]; ring
  have hexp := pow_div_factorial_le_exp x hx (n + 1)
  linarith

/-- Explicit sufficient conditions for uniform reference-error absorption. -/
theorem referenceError_absorption {A C D R a b e : ℝ} (p : ℕ)
    (hA : 0 ≤ A) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hR1 : 1 ≤ R) (hR : (C + D) ^ 2 ≤ R)
    (hb : 1 ≤ b) (ha : b ≤ a) (he : R * b ≤ e)
    (hlarge : 4 * (A * 4 ^ p) * ((2 * p + 1).factorial : ℝ) ≤ b) :
    A * (1 + a + b + e) ^ p * exp (C * sqrt (a * b) + D * b) ≤
      exp (7 * sqrt (a * e)) / 4 := by
  have hb0 : 0 ≤ b := zero_le_one.trans hb
  have hbe : b ≤ e := (le_mul_of_one_le_left hb0 hR1).trans he
  have he1 : 1 ≤ e := hb.trans hbe
  have hbx : b ≤ sqrt (a * e) := referenceError_sqrt_product_ge hb0 ha hbe
  have hpoly : A * (1 + a + b + e) ^ p ≤ exp (sqrt (a * e)) / 4 := by
    calc
      _ ≤ A * (4 ^ p * sqrt (a * e) ^ (2 * p)) :=
        mul_le_mul_of_nonneg_left (referenceError_polynomial_le_sqrt_pow p hb ha he1) hA
      _ = (A * 4 ^ p) * sqrt (a * e) ^ (2 * p) := by ring
      _ ≤ _ := referenceError_polynomial_absorption
        (sqrt_nonneg _) (2 * p) (hlarge.trans hbx)
  have hexp : exp (C * sqrt (a * b) + D * b) ≤ exp (sqrt (a * e)) :=
    exp_le_exp.mpr (referenceError_exponent_le_sqrt hC hD hb ha hR he)
  calc
    _ ≤ (exp (sqrt (a * e)) / 4) * exp (sqrt (a * e)) :=
      mul_le_mul hpoly hexp (exp_nonneg _) (by positivity)
    _ = exp (2 * sqrt (a * e)) / 4 := by rw [two_mul, exp_add]; ring
    _ ≤ _ := div_le_div_of_nonneg_right
      (exp_le_exp.mpr (by nlinarith [sqrt_nonneg (a * e)])) (by norm_num)

/-- The integer reference enlargement depends only on the exponential losses.
For every polynomial prefactor, a later integer band threshold works uniformly
in both the input and the output energies. -/
theorem exists_referenceError_radius {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D) :
    ∃ R₀ : ℕ, 3 < R₀ ∧ ∀ (A : ℝ), 0 ≤ A → ∀ p : ℕ,
      ∃ n₀ : ℕ, 1 ≤ n₀ ∧ ∀ a b e : ℝ,
        (n₀ : ℝ) ≤ b → b ≤ a → (R₀ : ℝ) * b ≤ e →
        A * (1 + a + b + e) ^ p * exp (C * sqrt (a * b) + D * b) ≤
          exp (7 * sqrt (a * e)) / 4 := by
  obtain ⟨R₀, hR₀⟩ := exists_nat_gt (max 3 ((C + D) ^ 2))
  have hR3 : (3 : ℝ) < R₀ := (le_max_left _ _).trans_lt hR₀
  have hR : (C + D) ^ 2 ≤ (R₀ : ℝ) :=
    (le_max_right _ _).trans hR₀.le
  refine ⟨R₀, by exact_mod_cast hR3, ?_⟩
  intro A hA p
  obtain ⟨n₀, hn₀⟩ := exists_nat_ge
    (max 1 (4 * (A * 4 ^ p) * ((2 * p + 1).factorial : ℝ)))
  have hn1 : (1 : ℝ) ≤ n₀ := (le_max_left _ _).trans hn₀
  have hnlarge : 4 * (A * 4 ^ p) * ((2 * p + 1).factorial : ℝ) ≤ n₀ :=
    (le_max_right _ _).trans hn₀
  refine ⟨n₀, by exact_mod_cast hn1, ?_⟩
  intro a b e hb ha he
  exact referenceError_absorption p hA hC hD (by linarith) hR
    (hn1.trans hb) ha he (hnlarge.trans hb)

/-- Uniform reference-error absorption with the radius chosen before the band
threshold, in the fixed-constant form used by the construction. -/
theorem exists_referenceError_absorption {A C D : ℝ} (p : ℕ)
    (hA : 0 ≤ A) (hC : 0 ≤ C) (hD : 0 ≤ D) :
    ∃ R₀ : ℕ, 3 < R₀ ∧ ∃ n₀ : ℕ, 1 ≤ n₀ ∧ ∀ a b e : ℝ,
      (n₀ : ℝ) ≤ b → b ≤ a → (R₀ : ℝ) * b ≤ e →
      A * (1 + a + b + e) ^ p * exp (C * sqrt (a * b) + D * b) ≤
        exp (7 * sqrt (a * e)) / 4 := by
  obtain ⟨R₀, hR₀, h⟩ := exists_referenceError_radius hC hD
  exact ⟨R₀, hR₀, h A hA p⟩

end GapFamily.Construction
