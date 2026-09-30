import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# An explicit algebraic coercivity estimate

The energy estimate and the propagated response estimate combine into a
quadratic inequality in the vector norm and the square root of its energy.
The following elementary argument extracts an explicit positive constant.
-/

noncomputable section

namespace GapFamily.Analytic

/-- An explicit positive coefficient in the final quadratic lower bound. -/
def coercivityEstimateConstant (M K : ℝ) : ℝ :=
  (4 * (M + K + 1))⁻¹ ^ 2

theorem coercivityEstimateConstant_pos {M K : ℝ} (hM : 0 ≤ M) (hK : 0 ≤ K) :
    0 < coercivityEstimateConstant M K := by
  unfold coercivityEstimateConstant
  positivity

/-- The quadratic response inequality controls the norm by the square root of energy. -/
theorem norm_le_coercivityFactor_mul_sqrt {x q M K : ℝ}
    (hq : 0 ≤ q) (hM : 0 ≤ M) (hK : 0 ≤ K)
    (h : x ^ 2 ≤ 2 * M * q + 2 * K * x * Real.sqrt q) :
    x ≤ (4 * (M + K + 1)) * Real.sqrt q := by
  have hs : 0 ≤ Real.sqrt q := Real.sqrt_nonneg q
  have hD : 1 ≤ 4 * (M + K + 1) := by linarith
  by_contra hnot
  have hlt : (4 * (M + K + 1)) * Real.sqrt q < x := lt_of_not_ge hnot
  have hxpos : 0 < x := (mul_nonneg (by linarith) hs).trans_lt hlt
  have hsx : Real.sqrt q ≤ x :=
    (le_mul_of_one_le_left hs hD).trans hlt.le
  have hqx : q ≤ x * Real.sqrt q := by
    nlinarith [Real.sq_sqrt hq, mul_nonneg hs (sub_nonneg.mpr hsx)]
  have hmain : x ^ 2 ≤ 2 * (M + K) * x * Real.sqrt q := by
    nlinarith [mul_le_mul_of_nonneg_left hqx hM]
  have hstrict : (2 * (M + K)) * Real.sqrt q < x :=
    (mul_le_mul_of_nonneg_right (by linarith : 2 * (M + K) ≤ 4 * (M + K + 1)) hs).trans_lt hlt
  nlinarith [mul_lt_mul_of_pos_left hstrict hxpos]

/-- Homogeneous coercivity extracted directly from the quadratic response inequality. -/
theorem coercivityEstimateConstant_mul_sq_le {x q M K : ℝ}
    (hx : 0 ≤ x) (hq : 0 ≤ q) (hM : 0 ≤ M) (hK : 0 ≤ K)
    (h : x ^ 2 ≤ 2 * M * q + 2 * K * x * Real.sqrt q) :
    coercivityEstimateConstant M K * x ^ 2 ≤ q := by
  have hD : 0 < 4 * (M + K + 1) := by linarith
  have hs := norm_le_coercivityFactor_mul_sqrt hq hM hK h
  have hdiv : x / (4 * (M + K + 1)) ≤ Real.sqrt q :=
    (div_le_iff₀ hD).mpr (by simpa only [mul_comm] using hs)
  have hsquare := (sq_le_sq₀ (div_nonneg hx hD.le) (Real.sqrt_nonneg q)).mpr hdiv
  rw [Real.sq_sqrt hq] at hsquare
  convert hsquare using 1
  unfold coercivityEstimateConstant
  ring

/-- Unit normalization gives an explicit nonzero lower bound for the energy. -/
theorem coercivityEstimateConstant_le_of_unit {q M K : ℝ}
    (hq : 0 ≤ q) (hM : 0 ≤ M) (hK : 0 ≤ K)
    (h : 1 ≤ 2 * M * q + 2 * K * Real.sqrt q) :
    coercivityEstimateConstant M K ≤ q := by
  have h' : (1 : ℝ) ^ 2 ≤ 2 * M * q + 2 * K * 1 * Real.sqrt q := by simpa using h
  simpa using coercivityEstimateConstant_mul_sq_le (by norm_num : (0 : ℝ) ≤ 1) hq hM hK h'

/-- The triangle decomposition, an energy bound for its first term, and a
propagation bound for its second term imply homogeneous coercivity. -/
theorem coercivityEstimateConstant_mul_sq_le_of_triangle {x y z q M K : ℝ}
    (hx : 0 ≤ x) (hq : 0 ≤ q) (hM : 0 ≤ M) (hK : 0 ≤ K)
    (htriangle : x ≤ y + z) (hy : y ^ 2 ≤ M * q)
    (hz : z ^ 2 ≤ K * x * Real.sqrt q) :
    coercivityEstimateConstant M K * x ^ 2 ≤ q := by
  apply coercivityEstimateConstant_mul_sq_le hx hq hM hK
  have hsum : x ^ 2 ≤ (y + z) ^ 2 :=
    (sq_le_sq₀ hx (hx.trans htriangle)).2 htriangle
  nlinarith [sq_nonneg (y - z)]

end GapFamily.Analytic
