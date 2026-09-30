import Mathlib.Combinatorics.Enumerative.Partition.GenFun
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# The analytic value of one partition factor

The factor for parts of size `i + 1` has one coefficient in each degree
divisible by `i + 1`. Its real generating series is the geometric factor.
-/

noncomputable section

open scoped PowerSeries.WithPiTopology

namespace BTZEntropy

/-- The formal generating function for repeated parts of size `i + 1`. -/
def partitionFactor (i : ℕ) : PowerSeries ℝ :=
  1 + ∑' j : ℕ, (PowerSeries.X : PowerSeries ℝ) ^ ((i + 1) * (j + 1))

theorem summable_partitionFactor_monomial (i : ℕ) :
    Summable (fun j : ℕ => (PowerSeries.X : PowerSeries ℝ) ^ ((i + 1) * j)) := by
  simpa only [pow_mul] using
    (PowerSeries.WithPiTopology.summable_pow_of_constantCoeff_eq_zero
      (f := (PowerSeries.X : PowerSeries ℝ) ^ (i + 1)) (by simp))

theorem partitionFactor_eq_tsum (i : ℕ) :
    partitionFactor i = ∑' j : ℕ, (PowerSeries.X : PowerSeries ℝ) ^ ((i + 1) * j) := by
  simpa only [Nat.mul_zero, pow_zero, partitionFactor] using
    (summable_partitionFactor_monomial i).tsum_eq_zero_add.symm

theorem coeff_partitionFactor (i n : ℕ) :
    (partitionFactor i).coeff n = if i + 1 ∣ n then 1 else 0 := by
  rw [partitionFactor_eq_tsum,
    (summable_partitionFactor_monomial i).map_tsum _
      (PowerSeries.WithPiTopology.continuous_coeff _ _)]
  by_cases h : i + 1 ∣ n
  · rcases h with ⟨j, rfl⟩
    rw [tsum_eq_single j]
    · simp [PowerSeries.coeff_X_pow]
    · intro k hk
      have hne : (i + 1) * j ≠ (i + 1) * k := by
        intro h
        exact hk (Nat.eq_of_mul_eq_mul_left (by omega) h).symm
      simp [PowerSeries.coeff_X_pow, hne]
  · have hn (j : ℕ) : n ≠ (i + 1) * j := fun hn => h ⟨j, hn⟩
    simp [PowerSeries.coeff_X_pow, hn, h]

theorem partitionFactor_coeff_nonneg (i n : ℕ) :
    0 ≤ (partitionFactor i).coeff n := by
  rw [coeff_partitionFactor]
  split_ifs <;> norm_num

@[simp] theorem partitionFactor_constantCoeff (i : ℕ) :
    (partitionFactor i).constantCoeff = 1 := by
  simpa only [PowerSeries.coeff_zero_eq_constantCoeff, dvd_zero, ite_true] using
    coeff_partitionFactor i 0

theorem hasSum_partitionFactor (i : ℕ) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    HasSum (fun n => (partitionFactor i).coeff n * q ^ n) ((1 - q ^ (i + 1))⁻¹) := by
  have hinj : Function.Injective (fun j : ℕ => (i + 1) * j) := by
    intro j k h
    exact Nat.eq_of_mul_eq_mul_left (by omega) h
  apply (hinj.hasSum_iff ?_).mp
  · change HasSum (fun j => (partitionFactor i).coeff ((i + 1) * j) *
      q ^ ((i + 1) * j)) _
    simpa only [coeff_partitionFactor, dvd_mul_right,
      ite_true, one_mul, pow_mul] using
      hasSum_geometric_of_lt_one (pow_nonneg hq0 (i + 1))
        (pow_lt_one₀ hq0 hq1 (by omega : i + 1 ≠ 0))
  · intro n hn
    have hd : ¬ i + 1 ∣ n := by
      rintro ⟨j, hj⟩
      exact hn ⟨j, hj.symm⟩
    simp [coeff_partitionFactor, hd]

theorem hasProd_partitionFactor :
    HasProd partitionFactor (Nat.Partition.genFun (fun _ _ => (1 : ℝ))) := by
  change HasProd (fun i => 1 + ∑' j : ℕ,
    (PowerSeries.X : PowerSeries ℝ) ^ ((i + 1) * (j + 1))) _
  simpa only [one_smul] using
    Nat.Partition.hasProd_genFun (fun _ _ => (1 : ℝ))

end BTZEntropy
