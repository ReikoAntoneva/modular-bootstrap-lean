import BTZEntropy.Analytic.PartitionBound
import BTZEntropy.Analytic.PartitionSeries
import BTZEntropy.Analytic.DescendantThermal
import BTZEntropy.Comparison.ReciprocalSquare
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Uniform thermal bound for the partition product

The bound in this file is independent of the partition generating-function
identity. It supplies the analytic estimate needed for descendant multiplicities.
-/

noncomputable section

namespace BTZEntropy

private theorem partition_geometric_hasSum {x : ℝ} (hx : 0 < x) :
    HasSum (fun n : ℕ => Real.exp (-x) ^ (n + 1))
      (Real.exp (-x) / (1 - Real.exp (-x))) := by
  have hlt : Real.exp (-x) < 1 := by simpa using Real.exp_lt_one_iff.mpr (neg_neg_of_pos hx)
  simpa only [pow_succ, div_eq_mul_inv, mul_comm] using
    (hasSum_geometric_of_lt_one (Real.exp_pos (-x)).le hlt).mul_right (Real.exp (-x))

private theorem partition_geometric_bound {x : ℝ} (hx : 0 < x) :
    Real.exp (-x) / (1 - Real.exp (-x)) ≤ 1 / x := by
  have hlt : Real.exp (-x) < 1 := by simpa using Real.exp_lt_one_iff.mpr (neg_neg_of_pos hx)
  have hexp : x + 1 ≤ Real.exp x := Real.add_one_le_exp x
  have hmul : Real.exp x * Real.exp (-x) = 1 := by rw [← Real.exp_add]; simp
  apply (div_le_div_iff₀ (sub_pos.mpr hlt) hx).mpr
  nlinarith [mul_le_mul_of_nonneg_right hexp (Real.exp_pos (-x)).le]

private theorem partition_power_hasSum {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)
    (n : ℕ) :
    HasSum (fun k : ℕ => (q ^ (n + 1)) ^ (k + 1) / ((k : ℝ) + 1))
      (Real.log (partitionEulerFactor q n)) := by
  rw [partitionEulerFactor, Real.log_inv]
  exact Real.hasSum_pow_div_log_of_abs_lt_one (by
    rw [abs_of_nonneg (pow_nonneg hq0 _)]
    exact pow_lt_one₀ hq0 hq1 (by omega))

private theorem partition_log_column_bound {β : ℝ} (hβ : 0 < β)
    (s : Finset ℕ) (k : ℕ) :
    (∑ n ∈ s, (Real.exp (-β) ^ (n + 1)) ^ (k + 1) / ((k : ℝ) + 1)) ≤
      (1 / β) * (1 / ((k : ℝ) + 1) ^ 2) := by
  let x : ℝ := β * ((k : ℝ) + 1)
  have hx : 0 < x := mul_pos hβ (by positivity)
  have heq (n : ℕ) : (Real.exp (-β) ^ (n + 1)) ^ (k + 1) =
      Real.exp (-x) ^ (n + 1) := by
    simp only [← Real.exp_nat_mul]
    congr 1
    dsimp [x]
    push_cast
    ring
  simp_rw [heq]
  rw [← Finset.sum_div]
  have hsum : ∑ n ∈ s, Real.exp (-x) ^ (n + 1) ≤ 1 / x := by
    exact ((partition_geometric_hasSum hx).summable.sum_le_tsum s
      (fun n _ => by positivity)).trans
        ((partition_geometric_hasSum hx).tsum_eq.le.trans (partition_geometric_bound hx))
  calc
    (∑ n ∈ s, Real.exp (-x) ^ (n + 1)) / ((k : ℝ) + 1) ≤
        (1 / x) / ((k : ℝ) + 1) := by gcongr
    _ = (1 / β) * (1 / ((k : ℝ) + 1) ^ 2) := by dsimp [x]; field_simp

/-- The logarithm of any finite thermal Euler product is at most `2 / β`. -/
theorem sum_log_partitionEulerFactor_le {β : ℝ} (hβ : 0 < β) (s : Finset ℕ) :
    (∑ n ∈ s, Real.log (partitionEulerFactor (Real.exp (-β)) n)) ≤ 2 / β := by
  have hq0 := (Real.exp_pos (-β)).le
  have hq1 : Real.exp (-β) < 1 := Real.exp_lt_one_iff.mpr (neg_neg_of_pos hβ)
  have hseries := hasSum_sum (s := s) (fun n _ => partition_power_hasSum hq0 hq1 n)
  rw [← hseries.tsum_eq]
  calc
    _ ≤ ∑' k : ℕ, (1 / β) * (1 / ((k : ℝ) + 1) ^ 2) :=
      hseries.summable.tsum_le_tsum (partition_log_column_bound hβ s)
        (summable_reciprocal_square.mul_left (1 / β))
    _ = (1 / β) * ∑' k : ℕ, 1 / ((k : ℝ) + 1) ^ 2 := tsum_mul_left
    _ ≤ (1 / β) * 2 :=
      mul_le_mul_of_nonneg_left tsum_reciprocal_square_le_two (by positivity)
    _ = 2 / β := by ring

/-- Every finite thermal Euler product obeys a bound uniform in its cutoff. -/
theorem partitionEulerPartialProduct_thermal_le {β : ℝ} (hβ : 0 < β)
    (s : Finset ℕ) :
    ∏ n ∈ s, partitionEulerFactor (Real.exp (-β)) n ≤ Real.exp (2 / β) := by
  have hq0 := (Real.exp_pos (-β)).le
  have hq1 : Real.exp (-β) < 1 := Real.exp_lt_one_iff.mpr (neg_neg_of_pos hβ)
  calc
    _ = Real.exp (∑ n ∈ s, Real.log (partitionEulerFactor (Real.exp (-β)) n)) := by
      rw [Real.exp_sum]
      exact Finset.prod_congr rfl (fun n _ => (Real.exp_log
        (partitionEulerFactor_pos hq0 hq1 n)).symm)
    _ ≤ Real.exp (2 / β) := Real.exp_le_exp.mpr (sum_log_partitionEulerFactor_le hβ s)

/-- The full partition Euler product has an explicit `exp (2 / β)` bound. -/
theorem partitionEulerProduct_thermal_le {β : ℝ} (hβ : 0 < β) :
    ∏' n, partitionEulerFactor (Real.exp (-β)) n ≤ Real.exp (2 / β) := by
  have hq0 := (Real.exp_pos (-β)).le
  have hq1 : Real.exp (-β) < 1 := Real.exp_lt_one_iff.mpr (neg_neg_of_pos hβ)
  exact (multipliable_partitionEulerFactor hq0 hq1).tprod_le_of_prod_le
    (partitionEulerPartialProduct_thermal_le hβ)

/-- The actual chiral descendant partition function has the same explicit bound. -/
theorem partitionThermal_le_exp {β : ℝ} (hβ : 0 < β) :
    partitionThermal β ≤ Real.exp (2 / β) := by
  have hq0 := (Real.exp_pos (-β)).le
  have hq1 : Real.exp (-β) < 1 := Real.exp_lt_one_iff.mpr (neg_neg_of_pos hβ)
  have hexp (n : ℕ) : Real.exp (-β * (n : ℝ)) = Real.exp (-β) ^ n := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  simp only [partitionThermal, partitionThermalTerm, hexp]
  rw [tsum_partitionCount_mul_pow_eq_tprod hq0 hq1]
  exact partitionEulerProduct_thermal_le hβ

/-- Optimizing a thermal coefficient bound gives a subexponential estimate. -/
theorem le_exp_sqrt_of_thermal_bound {a : ℝ} (n : ℕ)
    (ha : ∀ β : ℝ, 0 < β → a * Real.exp (-β * n) ≤ Real.exp (2 / β)) :
    a ≤ Real.exp (3 * Real.sqrt ((n : ℝ) + 1)) := by
  let r := Real.sqrt ((n : ℝ) + 1)
  have hr : 0 < r := Real.sqrt_pos.mpr (by positivity)
  have hrsq : r ^ 2 = (n : ℝ) + 1 := Real.sq_sqrt (by positivity)
  have hn : (n : ℝ) / r ≤ r := by
    apply (div_le_iff₀ hr).mpr
    nlinarith
  have he : 2 / (1 / r) + (1 / r) * (n : ℝ) ≤ 3 * r := by
    simp only [one_div, div_inv_eq_mul]
    rw [mul_comm r⁻¹, ← div_eq_mul_inv]
    linarith
  calc
    a = (a * Real.exp (-(1 / r) * n)) * Real.exp ((1 / r) * n) := by
      rw [mul_assoc, ← Real.exp_add]
      simp
    _ ≤ Real.exp (2 / (1 / r)) * Real.exp ((1 / r) * n) :=
      mul_le_mul_of_nonneg_right (ha (1 / r) (by positivity)) (Real.exp_pos _).le
    _ = Real.exp (2 / (1 / r) + (1 / r) * n) := (Real.exp_add _ _).symm
    _ ≤ Real.exp (3 * r) := Real.exp_le_exp.mpr he

/-- A subexponential bound for each actual partition multiplicity. -/
theorem partitionCount_le_exp_sqrt (n : ℕ) :
    (partitionCount n : ℝ) ≤ Real.exp (3 * Real.sqrt ((n : ℝ) + 1)) := by
  apply le_exp_sqrt_of_thermal_bound
  intro β hβ
  have hq0 := (Real.exp_pos (-β)).le
  have hq1 : Real.exp (-β) < 1 := Real.exp_lt_one_iff.mpr (neg_neg_of_pos hβ)
  have hexp (k : ℕ) : Real.exp (-β * (k : ℝ)) = Real.exp (-β) ^ k := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hs := summable_partitionCount_mul_pow hq0 hq1
  have hterm : (partitionCount n : ℝ) * Real.exp (-β * (n : ℝ)) ≤
      partitionThermal β := by
    simp only [partitionThermal, partitionThermalTerm, hexp]
    simpa using hs.sum_le_tsum {n} (fun k _ => by positivity)
  exact hterm.trans (partitionThermal_le_exp hβ)

end BTZEntropy
