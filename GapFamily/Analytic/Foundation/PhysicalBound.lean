import GapFamily.Analytic.Arithmetic.Kloosterman
import GapFamily.Analytic.Foundation.MinSeries
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Physical estimate for the nonzero-order kernel

The higher kernel keeps each product-minus-one intact. The physical cone makes
both chiral arguments nonnegative, so the bounded real cosines and their
quadratic vanishing give a summable minimum majorant. The continued central
Kloosterman-zeta term is not included in this module.
-/

noncomputable section

namespace GapFamily.Analytic

open scoped Real

/-- Quadratic vanishing of the entire factor on a nonnegative real argument. -/
theorem norm_cosRoot_ofReal_sub_one_le {x : ℝ} (hx : 0 ≤ x) :
    ‖cosRoot (x : ℂ) - 1‖ ≤ x / 2 := by
  rw [cosRoot_ofReal_nonneg hx, ← Complex.ofReal_one, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr (Real.cos_le_one _))]
  have h := Real.one_sub_sq_div_two_le_cos (x := Real.sqrt x)
  rw [Real.sq_sqrt hx] at h
  linarith

/-- Both physical factors are bounded, without expanding their denominator sum. -/
theorem norm_cosRoot_ofReal_mul_sub_one_le_two {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    ‖cosRoot (x : ℂ) * cosRoot (y : ℂ) - 1‖ ≤ 2 := by
  calc
    _ ≤ ‖cosRoot (x : ℂ) * cosRoot (y : ℂ)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ ≤ 1 * 1 + 1 := by
      rw [norm_mul, norm_one]
      exact add_le_add (mul_le_mul (norm_cosRoot_ofReal_le_one hx)
        (norm_cosRoot_ofReal_le_one hy) (norm_nonneg _) zero_le_one) le_rfl
    _ = 2 := by norm_num

/-- The intact physical bracket vanishes linearly in its two squared arguments. -/
theorem norm_cosRoot_ofReal_mul_sub_one_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    ‖cosRoot (x : ℂ) * cosRoot (y : ℂ) - 1‖ ≤ (x + y) / 2 := by
  rw [show cosRoot (x : ℂ) * cosRoot (y : ℂ) - 1 =
    (cosRoot (x : ℂ) - 1) * cosRoot (y : ℂ) + (cosRoot (y : ℂ) - 1) by ring]
  calc
    _ ≤ ‖(cosRoot (x : ℂ) - 1) * cosRoot (y : ℂ)‖ +
        ‖cosRoot (y : ℂ) - 1‖ := norm_add_le _ _
    _ ≤ (x / 2) * 1 + y / 2 := by
      rw [norm_mul]
      exact add_le_add (mul_le_mul (norm_cosRoot_ofReal_sub_one_le hx)
        (norm_cosRoot_ofReal_le_one hy) (norm_nonneg _) (by positivity))
        (norm_cosRoot_ofReal_sub_one_le hy)
    _ = _ := by ring

private theorem physical_argument_nonneg (j J : ℤ) (e E : ℝ)
    (he : |(j : ℝ)| ≤ e) (hE : |(J : ℝ)| ≤ E) (n : ℕ) :
    0 ≤ 4 * π ^ 2 * (E + J) * (e + j) / ((n + 1 : ℕ) : ℝ) ^ 2 ∧
    0 ≤ 4 * π ^ 2 * (E - J) * (e - j) / ((n + 1 : ℕ) : ℝ) ^ 2 := by
  obtain ⟨hej, hje⟩ := abs_le.mp he
  obtain ⟨hEJ, hJE⟩ := abs_le.mp hE
  constructor <;> apply div_nonneg
  · exact mul_nonneg (mul_nonneg (by positivity) (by linarith)) (by linarith)
  · positivity
  · exact mul_nonneg (mul_nonneg (by positivity) (by linarith)) (by linarith)
  · positivity

/-- An individual physical summand is bounded by two, uniformly in all spins. -/
theorem norm_higherKernelTerm_physical_le_two (j J : ℤ) (e E : ℝ)
    (he : |(j : ℝ)| ≤ e) (hE : |(J : ℝ)| ≤ E) (n : ℕ) :
    ‖higherKernelTerm j J e E n‖ ≤ 2 := by
  obtain ⟨hp, hm⟩ := physical_argument_nonneg j J e E he hE n
  have hb := norm_cosRoot_ofReal_mul_sub_one_le_two hp hm
  unfold higherKernelTerm higherKernelArgPlus higherKernelArgMinus
  push_cast at hb
  calc
    _ ≤ 1 * ‖cosRoot (4 * (π : ℂ) ^ 2 * ((E : ℂ) + J) * ((e : ℂ) + j) /
        ((n + 1 : ℕ) : ℂ) ^ 2) * cosRoot (4 * (π : ℂ) ^ 2 * ((E : ℂ) - J) *
        ((e : ℂ) - j) / ((n + 1 : ℕ) : ℂ) ^ 2) - 1‖ := by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (norm_kloostermanSum_div_le_one j J n)
        (norm_nonneg _)
    _ ≤ 2 := by simpa using hb

/-- Quadratic physical decay before summing the intact denominator bracket. -/
theorem norm_higherKernelTerm_physical_le_div (j J : ℤ) (e E : ℝ)
    (he : |(j : ℝ)| ≤ e) (hE : |(J : ℝ)| ≤ E) (n : ℕ) :
    ‖higherKernelTerm j J e E n‖ ≤
      8 * π ^ 2 * (e * E / ((n + 1 : ℕ) : ℝ) ^ 2) := by
  obtain ⟨hp, hm⟩ := physical_argument_nonneg j J e E he hE n
  have hb := norm_cosRoot_ofReal_mul_sub_one_le hp hm
  have hjJ : (j : ℝ) * J ≤ e * E := calc
    _ ≤ |(j : ℝ) * J| := le_abs_self _
    _ = |(j : ℝ)| * |(J : ℝ)| := abs_mul _ _
    _ ≤ e * E := mul_le_mul he hE (abs_nonneg _) (le_trans (abs_nonneg _) he)
  have harg :
      (4 * π ^ 2 * (E + J) * (e + j) / ((n + 1 : ℕ) : ℝ) ^ 2 +
        4 * π ^ 2 * (E - J) * (e - j) / ((n + 1 : ℕ) : ℝ) ^ 2) / 2 ≤
      8 * π ^ 2 * (e * E / ((n + 1 : ℕ) : ℝ) ^ 2) := by
    have hmul := mul_le_mul_of_nonneg_left hjJ (show 0 ≤ 4 * π ^ 2 by positivity)
    calc
      _ = (4 * π ^ 2 * (e * E + (j : ℝ) * J)) / ((n + 1 : ℕ) : ℝ) ^ 2 := by ring
      _ ≤ (8 * π ^ 2 * (e * E)) / ((n + 1 : ℕ) : ℝ) ^ 2 := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        nlinarith [hmul]
      _ = _ := by ring
  unfold higherKernelTerm higherKernelArgPlus higherKernelArgMinus
  push_cast at hb
  calc
    _ ≤ 1 * ‖cosRoot (4 * (π : ℂ) ^ 2 * ((E : ℂ) + J) * ((e : ℂ) + j) /
        ((n + 1 : ℕ) : ℂ) ^ 2) * cosRoot (4 * (π : ℂ) ^ 2 * ((E : ℂ) - J) *
        ((e : ℂ) - j) / ((n + 1 : ℕ) : ℂ) ^ 2) - 1‖ := by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (norm_kloostermanSum_div_le_one j J n)
        (norm_nonneg _)
    _ ≤ _ := by simpa using hb
    _ ≤ _ := harg

/-- A minimum majorant valid uniformly on the physical cone. -/
theorem norm_higherKernelTerm_physical_le_min (j J : ℤ) (e E : ℝ)
    (he : |(j : ℝ)| ≤ e) (hE : |(J : ℝ)| ≤ E) (n : ℕ) :
    ‖higherKernelTerm j J e E n‖ ≤
      8 * π ^ 2 * min 1 (e * E / ((n + 1 : ℕ) : ℝ) ^ 2) := by
  by_cases h : 1 ≤ e * E / ((n + 1 : ℕ) : ℝ) ^ 2
  · rw [min_eq_left h, mul_one]
    exact (norm_higherKernelTerm_physical_le_two j J e E he hE n).trans
      (by nlinarith [Real.one_le_pi_div_two])
  · rw [min_eq_right (le_of_not_ge h)]
    exact norm_higherKernelTerm_physical_le_div j J e E he hE n

/-- The higher-order physical kernel obeys a square-root growth bound.
The separately continued zero-order term is not part of `higherKernel`. -/
theorem norm_higherKernel_physical_le_sqrt (j J : ℤ) (e E : ℝ)
    (he : |(j : ℝ)| ≤ e) (hE : |(J : ℝ)| ≤ E) :
    ‖higherKernel j J e E‖ ≤ 64 * π ^ 2 * Real.sqrt (e * E) := by
  have heE : 0 ≤ e * E := mul_nonneg
    (le_trans (abs_nonneg _) he) (le_trans (abs_nonneg _) hE)
  have hs : Summable (fun n : ℕ => min 1 (e * E / ((n + 1 : ℕ) : ℝ) ^ 2)) := by
    simpa only [Nat.cast_add, Nat.cast_one] using summable_min_one_div_nat_sq heE
  have ht : (∑' n : ℕ, min 1 (e * E / ((n + 1 : ℕ) : ℝ) ^ 2)) ≤
      4 * Real.sqrt (e * E) := by
    simpa only [Nat.cast_add, Nat.cast_one] using tsum_min_one_div_nat_sq_le heE
  calc
    ‖higherKernel j J e E‖ = 2 * ‖∑' n : ℕ, higherKernelTerm j J e E n‖ := by
      simp [higherKernel]
    _ ≤ 2 * (∑' n : ℕ, ‖higherKernelTerm j J e E n‖) := by
      gcongr
      exact norm_tsum_le_tsum_norm (summable_norm_higherKernelTerm j J e E)
    _ ≤ 2 * (∑' n : ℕ, 8 * π ^ 2 * min 1 (e * E / ((n + 1 : ℕ) : ℝ) ^ 2)) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact Summable.tsum_le_tsum (norm_higherKernelTerm_physical_le_min j J e E he hE)
        (summable_norm_higherKernelTerm j J e E) (hs.mul_left _)
    _ = 2 * (8 * π ^ 2 * (∑' n : ℕ, min 1 (e * E / ((n + 1 : ℕ) : ℝ) ^ 2))) := by
      rw [tsum_mul_left]
    _ ≤ 2 * (8 * π ^ 2 * (4 * Real.sqrt (e * E))) := by gcongr
    _ = _ := by ring

/-- Linear vanishing in either scalar energy is retained independently of the
square-root growth bound. This is used at the scalar endpoint for integrability. -/
theorem norm_higherKernel_physical_le_mul (j J : ℤ) (e E : ℝ)
    (he : |(j : ℝ)| ≤ e) (hE : |(J : ℝ)| ≤ E) :
    ‖higherKernel j J e E‖ ≤ 32 * π ^ 2 * (e * E) := by
  have heE : 0 ≤ e * E := mul_nonneg
    (le_trans (abs_nonneg _) he) (le_trans (abs_nonneg _) hE)
  have hs : Summable (fun n : ℕ => (1 : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 2) := by
    simpa only [Nat.cast_add, Nat.cast_one] using summable_one_div_nat_sq
  have ht : (∑' n : ℕ, (1 : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 2) ≤ 2 := by
    simpa only [Nat.cast_add, Nat.cast_one] using tsum_one_div_nat_sq_le_two
  calc
    ‖higherKernel j J e E‖ = 2 * ‖∑' n : ℕ, higherKernelTerm j J e E n‖ := by
      simp [higherKernel]
    _ ≤ 2 * (∑' n : ℕ, ‖higherKernelTerm j J e E n‖) := by
      gcongr
      exact norm_tsum_le_tsum_norm (summable_norm_higherKernelTerm j J e E)
    _ ≤ 2 * (∑' n : ℕ, (8 * π ^ 2 * (e * E)) * (1 / ((n + 1 : ℕ) : ℝ) ^ 2)) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply Summable.tsum_le_tsum _ (summable_norm_higherKernelTerm j J e E) (hs.mul_left _)
      intro n
      simpa only [mul_one_div, mul_div_assoc] using
        norm_higherKernelTerm_physical_le_div j J e E he hE n
    _ = 2 * ((8 * π ^ 2 * (e * E)) * (∑' n : ℕ, 1 / ((n + 1 : ℕ) : ℝ) ^ 2)) := by
      rw [tsum_mul_left]
    _ ≤ 2 * ((8 * π ^ 2 * (e * E)) * 2) := by gcongr
    _ = _ := by ring

end GapFamily.Analytic
