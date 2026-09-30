import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Order

/-!
# Analytic bounds for the partition Euler product

The reciprocal Euler factors are multipliable throughout the real open unit
interval, including its zero endpoint. Their finite products have a single
uniform upper bound. This analytic fact does not assume the partition
generating-function identity.
-/

noncomputable section

namespace BTZEntropy

/-- The factor belonging to the positive part size `n + 1`. -/
def partitionEulerFactor (q : ℝ) (n : ℕ) : ℝ := (1 - q ^ (n + 1))⁻¹

private theorem partition_power_le {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)
    (n : ℕ) : q ^ (n + 1) ≤ q := by
  rw [pow_succ]
  simpa using mul_le_mul_of_nonneg_right (pow_le_one₀ hq0 hq1.le) hq0

theorem partitionEulerFactor_pos {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)
    (n : ℕ) : 0 < partitionEulerFactor q n := by
  exact inv_pos.mpr (sub_pos.mpr ((partition_power_le hq0 hq1 n).trans_lt hq1))

theorem one_le_partitionEulerFactor {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)
    (n : ℕ) : 1 ≤ partitionEulerFactor q n := by
  have hpos : 0 < 1 - q ^ (n + 1) :=
    sub_pos.mpr ((partition_power_le hq0 hq1 n).trans_lt hq1)
  simpa only [partitionEulerFactor, one_div] using
    one_le_one_div hpos (sub_le_self 1 (pow_nonneg hq0 (n + 1)))

/-- The excess of an Euler factor over one is bounded by a geometric series. -/
theorem summable_partitionEulerFactor_sub_one {q : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) :
    Summable (fun n : ℕ => partitionEulerFactor q n - 1) := by
  have hgeo : Summable (fun n : ℕ => q ^ (n + 1) / (1 - q)) := by
    simpa only [pow_succ] using
      ((summable_geometric_of_lt_one hq0 hq1).mul_right q).div_const (1 - q)
  refine Summable.of_nonneg_of_le
    (fun n => sub_nonneg.mpr (one_le_partitionEulerFactor hq0 hq1 n)) ?_ hgeo
  intro n
  have hpow := partition_power_le hq0 hq1 n
  have hden : 0 < 1 - q ^ (n + 1) := sub_pos.mpr (hpow.trans_lt hq1)
  calc
    partitionEulerFactor q n - 1 = q ^ (n + 1) / (1 - q ^ (n + 1)) := by
      unfold partitionEulerFactor
      field_simp
      ring
    _ ≤ q ^ (n + 1) / (1 - q) :=
      div_le_div_of_nonneg_left (pow_nonneg hq0 _) (sub_pos.mpr hq1) (by linarith)

/-- Convergence is established independently of the combinatorial identity. -/
theorem multipliable_partitionEulerFactor {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    Multipliable (partitionEulerFactor q) := by
  simpa only [add_sub_cancel] using
    Real.multipliable_one_add_of_summable
      (summable_partitionEulerFactor_sub_one hq0 hq1)

/-- Every finite product is bounded by the convergent infinite product. -/
theorem partitionEulerPartialProduct_le {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)
    (s : Finset ℕ) :
    ∏ n ∈ s, partitionEulerFactor q n ≤ ∏' n, partitionEulerFactor q n := by
  exact Multipliable.prod_le_tprod_of_nonneg
    (fun n _ => (partitionEulerFactor_pos hq0 hq1 n).le)
    (fun n _ => one_le_partitionEulerFactor hq0 hq1 n)
    (multipliable_partitionEulerFactor hq0 hq1)

/-- The same finite bound controls all natural-number initial products. -/
theorem partitionEulerPartialProduct_bounded {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    ∃ C : ℝ, ∀ N : ℕ, ∏ n ∈ Finset.range N, partitionEulerFactor q n ≤ C :=
  ⟨∏' n, partitionEulerFactor q n,
    fun N => partitionEulerPartialProduct_le hq0 hq1 (Finset.range N)⟩

theorem one_le_partitionEulerProduct {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    1 ≤ ∏' n, partitionEulerFactor q n := by
  simpa only [Finset.prod_empty] using
    partitionEulerPartialProduct_le hq0 hq1 ∅

/-- The convergent reciprocal product is the reciprocal of the usual Euler
product. Its nonvanishing follows from the proved lower bound. -/
theorem partitionEulerProduct_eq_inv_tprod {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    (∏' n, partitionEulerFactor q n) = (∏' n : ℕ, (1 - q ^ (n + 1)))⁻¹ := by
  have hnonzero : (∏' n, partitionEulerFactor q n) ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le zero_lt_one (one_le_partitionEulerProduct hq0 hq1))
  have hi := (multipliable_partitionEulerFactor hq0 hq1).hasProd.inv₀ hnonzero
  simp only [partitionEulerFactor, inv_inv] at hi
  rw [hi.tprod_eq, inv_inv]
  rfl

end BTZEntropy
