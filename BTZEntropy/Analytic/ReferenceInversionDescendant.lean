import BTZEntropy.Analytic.ComplexPartitionSeries
import BTZEntropy.Analytic.ComplexEulerBound
import Mathlib.Analysis.Analytic.IsolatedZeros

noncomputable section

open Filter Set
open scoped Topology

namespace BTZEntropy

/-- The real partition identity agrees with the complex Euler product on the
positive real segment of the unit disc. -/
theorem complexPartitionSeries_ofReal_eq {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    (∑' n : ℕ, (partitionCount n : ℂ) * (q : ℂ) ^ n) =
      (complexEulerProduct (q : ℂ))⁻¹ := by
  have hreal := hasSum_partitionCount_mul_pow hq0 hq1
  have hcast := hreal.map Complex.ofRealHom Complex.continuous_ofReal
  have hprod := (multipliable_partitionEulerFactor hq0 hq1).hasProd.inv₀
    (ne_of_gt (lt_of_lt_of_le zero_lt_one (one_le_partitionEulerProduct hq0 hq1)))
  have hprodcast := hprod.map Complex.ofRealHom Complex.continuous_ofReal
  simp only [Function.comp_def, Complex.ofRealHom_eq_coe, partitionEulerFactor, inv_inv, Complex.ofReal_sub, Complex.ofReal_one,
    Complex.ofReal_pow, Complex.ofReal_inv] at hprodcast
  have he := hprodcast.tprod_eq
  change complexEulerProduct (q : ℂ) = _ at he
  rw [he, inv_inv]
  simpa only [Function.comp_def, Complex.ofRealHom_eq_coe, Complex.ofReal_mul, Complex.ofReal_natCast, Complex.ofReal_pow] using hcast.tsum_eq

/-- The actual partition series evaluates to the reciprocal Euler product
throughout the complex unit disc, by analytic continuation of its real identity. -/
theorem complexPartitionSeries_eq_euler {q : ℂ} (hq : ‖q‖ < 1) :
    complexPartitionSeries q = (complexEulerProduct q)⁻¹ := by
  have hs : AnalyticOnNhd ℂ complexPartitionSeries (Metric.ball (0 : ℂ) 1) := by
    intro z hz
    exact analyticAt_complexPartitionSeries (by simpa using hz)
  have he : AnalyticOnNhd ℂ (fun z => (complexEulerProduct z)⁻¹)
      (Metric.ball (0 : ℂ) 1) := by
    intro z hz
    have hz' : ‖z‖ < 1 := by simpa using hz
    exact (analyticAt_complexEulerProduct hz').inv (complexEulerProduct_ne_zero hz')
  have hclosure : (0 : ℂ) ∈ closure
      ({z | complexPartitionSeries z = (complexEulerProduct z)⁻¹} \ {(0 : ℂ)}) := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    let r : ℝ := min (ε / 2) (1 / 2)
    have hr : 0 < r := lt_min (by positivity) (by norm_num)
    have hrε : r < ε := (min_le_left _ _).trans_lt (by linarith)
    have hr1 : r < 1 := (min_le_right _ _).trans_lt (by norm_num)
    refine ⟨(r : ℂ), ⟨?_, ?_⟩, ?_⟩
    · exact complexPartitionSeries_ofReal_eq hr.le hr1
    · simpa using (Complex.ofReal_ne_zero.mpr hr.ne')
    · simpa [Complex.dist_eq, abs_of_pos hr] using hrε
  exact hs.eqOn_of_preconnected_of_mem_closure he
    (convex_ball (0 : ℂ) 1).isPreconnected (by simp) hclosure (by simpa using hq)

/-- Absolute convergence and exact evaluation of the complex partition series. -/
theorem hasSum_complexPartitionSeries {q : ℂ} (hq : ‖q‖ < 1) :
    HasSum (fun n : ℕ => (partitionCount n : ℂ) * q ^ n)
      ((complexEulerProduct q)⁻¹) := by
  rw [← complexPartitionSeries_eq_euler hq]
  exact (summable_complexPartitionSeries hq).hasSum

/-- The complex thermal descendant sum converges in the full right half-plane. -/
theorem hasSum_complexPartitionThermal {z : ℂ} (hz : 0 < z.re) :
    HasSum (fun n : ℕ => (partitionCount n : ℂ) * Complex.exp (-z * n))
      ((complexEulerProduct (Complex.exp (-z)))⁻¹) := by
  have hq : ‖Complex.exp (-z)‖ < 1 := by
    rw [Complex.norm_exp, Complex.neg_re, Real.exp_lt_one_iff]
    linarith
  convert hasSum_complexPartitionSeries hq using 1
  funext n
  rw [← Complex.exp_nat_mul]
  congr 2
  ring

theorem summable_complexPartitionThermal {z : ℂ} (hz : 0 < z.re) :
    Summable (fun n : ℕ => (partitionCount n : ℂ) * Complex.exp (-z * n)) :=
  (hasSum_complexPartitionThermal hz).summable

/-- Both chiral descendant sums are combined as an actual absolutely convergent
sum over the two nonnegative levels. -/
theorem hasSum_complexDescendantPair {z : ℂ} (hz : 0 < z.re) :
    HasSum (fun v : ℕ × ℕ =>
      ((partitionCount v.1 * partitionCount v.2 : ℕ) : ℂ) *
        Complex.exp (-z * ((v.1 : ℂ) + v.2)))
      ((complexEulerProduct (Complex.exp (-z)))⁻¹ ^ 2) := by
  have h := hasSum_complexPartitionThermal hz
  have hp : Summable (fun v : ℕ × ℕ =>
      ((partitionCount v.1 : ℂ) * Complex.exp (-z * v.1)) *
      ((partitionCount v.2 : ℂ) * Complex.exp (-z * v.2))) :=
    summable_mul_of_summable_norm
      (f := fun n : ℕ => (partitionCount n : ℂ) * Complex.exp (-z * n))
      (g := fun n : ℕ => (partitionCount n : ℂ) * Complex.exp (-z * n))
      h.summable.norm h.summable.norm
  have hs := h.mul h hp
  convert hs using 1
  · funext v
    simp only [Nat.cast_mul, mul_add, Complex.exp_add]
    ring
  · ring

theorem tsum_complexPartitionThermal {z : ℂ} (hz : 0 < z.re) :
    (∑' n : ℕ, (partitionCount n : ℂ) * Complex.exp (-z * n)) =
      (complexEulerProduct (Complex.exp (-z)))⁻¹ :=
  (hasSum_complexPartitionThermal hz).tsum_eq

theorem summable_complexDescendantPair {z : ℂ} (hz : 0 < z.re) :
    Summable (fun v : ℕ × ℕ =>
      ((partitionCount v.1 * partitionCount v.2 : ℕ) : ℂ) *
        Complex.exp (-z * ((v.1 : ℂ) + v.2))) :=
  (hasSum_complexDescendantPair hz).summable

end BTZEntropy
