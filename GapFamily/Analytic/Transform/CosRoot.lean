import Mathlib.LinearAlgebra.Complex.FiniteDimensional

import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.ChangeOrigin
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.PSeries

/-!
# Entire cosine of a square root

The energy kernel uses the entire power series directly. Its agreement with a
real square-root cosine is asserted only on nonnegative real arguments.
-/

noncomputable section

namespace GapFamily.Analytic

/-- The coefficients of the entire function used in the energy kernel. -/
def cosRootCoeff (n : ℕ) : ℂ := (-1 : ℂ) ^ n / (2 * n).factorial

/-- The canonical entire-energy factor; no branch of a complex square root occurs. -/
def cosRoot (z : ℂ) : ℂ := ∑' n : ℕ, (-1 : ℂ) ^ n * z ^ n / (2 * n).factorial

private theorem cosRootCoeff_norm (n : ℕ) :
    ‖cosRootCoeff n‖ = 1 / ((2 * n).factorial : ℝ) := by
  simp [cosRootCoeff, norm_pow]

/-- Absolute convergence at every complex energy. -/
theorem summable_cosRoot (z : ℂ) :
    Summable (fun n : ℕ => (-1 : ℂ) ^ n * z ^ n / (2 * n).factorial) := by
  apply Summable.of_norm_bounded (Real.summable_pow_div_factorial ‖z‖)
  intro n
  simp only [norm_div, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
    Complex.norm_natCast]
  apply div_le_div_of_nonneg_left (pow_nonneg (norm_nonneg _) _) (by positivity)
  exact_mod_cast Nat.factorial_le (show n ≤ 2 * n by omega)

/-- A global bound from comparison with the exponential series. -/
theorem norm_cosRoot_le_exp (z : ℂ) : ‖cosRoot z‖ ≤ Real.exp ‖z‖ := by
  rw [Real.exp_eq_exp_ℝ]
  apply tsum_of_norm_bounded (NormedSpace.expSeries_div_hasSum_exp ‖z‖)
  intro n
  simp only [norm_div, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
    Complex.norm_natCast]
  apply div_le_div_of_nonneg_left (pow_nonneg (norm_nonneg _) _) (by positivity)
  exact_mod_cast Nat.factorial_le (show n ≤ 2 * n by omega)

/-- The vanishing needed to keep each product-minus-one kernel summand intact. -/
theorem norm_cosRoot_sub_one_le (z : ℂ) :
    ‖cosRoot z - 1‖ ≤ ‖z‖ * Real.exp ‖z‖ := by
  have htail : cosRoot z - 1 =
      ∑' n : ℕ, (-1 : ℂ) ^ (n + 1) * z ^ (n + 1) / (2 * (n + 1)).factorial := by
    have h := (summable_cosRoot z).sum_add_tsum_nat_add 1
    apply sub_eq_iff_eq_add.mpr
    simpa [cosRoot, add_comm] using h.symm
  rw [htail, Real.exp_eq_exp_ℝ]
  apply tsum_of_norm_bounded ((NormedSpace.expSeries_div_hasSum_exp ‖z‖).mul_left ‖z‖)
  intro n
  simp only [norm_div, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
    Complex.norm_natCast]
  rw [pow_succ, mul_comm (‖z‖ ^ n), mul_div_assoc]
  gcongr
  omega

/-- The intact product-minus-one obeys a bound vanishing in its two arguments. -/
theorem norm_cosRoot_mul_sub_one_le (z w : ℂ) :
    ‖cosRoot z * cosRoot w - 1‖ ≤ (‖z‖ + ‖w‖) * Real.exp (‖z‖ + ‖w‖) := by
  rw [show cosRoot z * cosRoot w - 1 =
    (cosRoot z - 1) * cosRoot w + (cosRoot w - 1) by ring]
  calc
    _ ≤ ‖(cosRoot z - 1) * cosRoot w‖ + ‖cosRoot w - 1‖ := norm_add_le _ _
    _ ≤ (‖z‖ * Real.exp ‖z‖) * Real.exp ‖w‖ + ‖w‖ * Real.exp ‖w‖ := by
      rw [norm_mul]
      exact add_le_add (mul_le_mul (norm_cosRoot_sub_one_le z) (norm_cosRoot_le_exp w)
        (norm_nonneg _) (mul_nonneg (norm_nonneg _) (Real.exp_pos _).le))
        (norm_cosRoot_sub_one_le w)
    _ = ‖z‖ * Real.exp (‖z‖ + ‖w‖) + ‖w‖ * Real.exp ‖w‖ := by
      rw [Real.exp_add]
      ring
    _ ≤ ‖z‖ * Real.exp (‖z‖ + ‖w‖) + ‖w‖ * Real.exp (‖z‖ + ‖w‖) := by
      gcongr
      exact le_add_of_nonneg_left (norm_nonneg _)
    _ = _ := by ring

/-- Uniform scaling yields the denominator-square majorant used by the kernel. -/
theorem norm_cosRoot_mul_sub_one_div_le (z w : ℂ) (d : ℝ) (hd : 1 ≤ d) :
    ‖cosRoot (z / d) * cosRoot (w / d) - 1‖ ≤
      ((‖z‖ + ‖w‖) * Real.exp (‖z‖ + ‖w‖)) / d := by
  have hd0 : 0 ≤ d := le_trans zero_le_one hd
  have hnorm : ‖z / (d : ℂ)‖ + ‖w / (d : ℂ)‖ = (‖z‖ + ‖w‖) / d := by
    simp [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hd0, add_div]
  calc
    _ ≤ (‖z / (d : ℂ)‖ + ‖w / (d : ℂ)‖) *
        Real.exp (‖z / (d : ℂ)‖ + ‖w / (d : ℂ)‖) := norm_cosRoot_mul_sub_one_le _ _
    _ = ((‖z‖ + ‖w‖) / d) * Real.exp ((‖z‖ + ‖w‖) / d) := by rw [hnorm]
    _ ≤ ((‖z‖ + ‖w‖) / d) * Real.exp (‖z‖ + ‖w‖) := by
      gcongr
      exact div_le_self (add_nonneg (norm_nonneg _) (norm_nonneg _)) hd
    _ = _ := by ring

/-- The intact higher-order bracket is absolutely summable over denominators. -/
theorem summable_cosRoot_mul_sub_one (z w : ℂ) :
    Summable (fun n : ℕ =>
      cosRoot (z / ((n + 1 : ℕ) : ℂ) ^ 2) *
        cosRoot (w / ((n + 1 : ℕ) : ℂ) ^ 2) - 1) := by
  have hs : Summable (fun n : ℕ =>
      ((‖z‖ + ‖w‖) * Real.exp (‖z‖ + ‖w‖)) / ((n + 1 : ℕ) : ℝ) ^ 2) := by
    simpa [div_eq_mul_inv] using
      ((summable_nat_add_iff 1).mpr
        (Real.summable_one_div_nat_pow.mpr (show 1 < 2 by norm_num))).mul_left
          ((‖z‖ + ‖w‖) * Real.exp (‖z‖ + ‖w‖))
  apply Summable.of_norm_bounded hs
  intro n
  have hd : 1 ≤ (((n + 1 : ℕ) : ℝ) ^ 2) := by
    have hn : 1 ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
    nlinarith
  simpa only [Complex.ofReal_pow, Complex.ofReal_natCast] using
    norm_cosRoot_mul_sub_one_div_le z w (((n + 1 : ℕ) : ℝ) ^ 2) hd

/-- Bounded normalized arithmetic weights preserve absolute convergence. -/
theorem summable_weighted_cosRoot_mul_sub_one (z w : ℂ) (a : ℕ → ℂ)
    (ha : ∀ n, ‖a n‖ ≤ 1) :
    Summable (fun n : ℕ => a n *
      (cosRoot (z / ((n + 1 : ℕ) : ℂ) ^ 2) *
        cosRoot (w / ((n + 1 : ℕ) : ℂ) ^ 2) - 1)) := by
  apply Summable.of_norm_bounded (summable_cosRoot_mul_sub_one z w).norm
  intro n
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (ha n)

/-- The multilinear power series realizing `cosRoot`. -/
def cosRootSeries : FormalMultilinearSeries ℂ ℂ ℂ :=
  FormalMultilinearSeries.ofScalars ℂ cosRootCoeff

@[simp] theorem cosRootSeries_radius : cosRootSeries.radius = ⊤ := by
  apply FormalMultilinearSeries.radius_eq_top_of_summable_norm
  intro r
  refine Summable.of_nonneg_of_le (fun n => by positivity) ?_
    (Real.summable_pow_div_factorial (r : ℝ))
  intro n
  simp only [cosRootSeries, FormalMultilinearSeries.ofScalars_norm, cosRootCoeff_norm]
  rw [one_div_mul_eq_div]
  apply div_le_div_of_nonneg_left (pow_nonneg r.coe_nonneg _) (by positivity)
  exact_mod_cast Nat.factorial_le (show n ≤ 2 * n by omega)

private theorem cosRootSeries_sum : cosRootSeries.sum = cosRoot := by
  funext z
  unfold cosRootSeries
  change FormalMultilinearSeries.ofScalarsSum cosRootCoeff z = cosRoot z
  rw [FormalMultilinearSeries.ofScalars_sum_eq]
  apply tsum_congr
  intro n
  simp [cosRootCoeff, smul_eq_mul, div_mul_eq_mul_div]

/-- A power-series certificate on the whole complex plane. -/
theorem cosRoot_hasFPowerSeriesOnBall :
    HasFPowerSeriesOnBall cosRoot cosRootSeries 0 ⊤ := by
  have h := cosRootSeries.hasFPowerSeriesOnBall (by simp)
  simpa only [cosRootSeries_radius, cosRootSeries_sum] using h

/-- `cosRoot` is entire. -/
theorem cosRoot_analyticAt (z : ℂ) : AnalyticAt ℂ cosRoot z := by
  apply cosRoot_hasFPowerSeriesOnBall.analyticAt_of_mem
  simp

/-- Continuity follows from the globally convergent analytic representation. -/
theorem cosRoot_continuous : Continuous cosRoot :=
  continuous_iff_continuousAt.mpr fun z => (cosRoot_analyticAt z).continuousAt

/-- The factor equals the usual cosine whenever its argument is a square. -/
theorem cosRoot_sq (z : ℂ) : cosRoot (z ^ 2) = Complex.cos z := by
  exact (by
    convert Complex.hasSum_cos z using 1
    funext n
    congr 2
    rw [← pow_mul] : HasSum (fun n : ℕ => (-1 : ℂ) ^ n * (z ^ 2) ^ n /
      (2 * n).factorial) (Complex.cos z)).tsum_eq

/-- Physical agreement, with the nonnegativity hypothesis made explicit. -/
theorem cosRoot_ofReal_nonneg {x : ℝ} (hx : 0 ≤ x) :
    cosRoot (x : ℂ) = (Real.cos (Real.sqrt x) : ℂ) := by
  have hsq : (Real.sqrt x : ℂ) ^ 2 = (x : ℂ) := by
    exact_mod_cast Real.sq_sqrt hx
  rw [← hsq, cosRoot_sq, ← Complex.ofReal_cos]

/-- The physical real factor has norm at most one. -/
theorem norm_cosRoot_ofReal_le_one {x : ℝ} (hx : 0 ≤ x) : ‖cosRoot (x : ℂ)‖ ≤ 1 := by
  rw [cosRoot_ofReal_nonneg hx, Complex.norm_real, Real.norm_eq_abs]
  exact Real.abs_cos_le_one _

@[simp] theorem cosRoot_zero : cosRoot 0 = 1 := by
  simpa using cosRoot_sq (0 : ℂ)

end GapFamily.Analytic
