import BTZEntropy.Observable
import BTZEntropy.Analytic.PartitionBound
import BTZEntropy.Analytic.PartitionFactor
import Mathlib.Combinatorics.Enumerative.Partition.GenFun
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Analytic evaluation of the partition generating series

The bridge from the formal partition product to its convergent real value uses
nonnegative coefficients. Finite products have the usual Cauchy-product
evaluation. Their coefficient limits and uniformly bounded evaluations imply
summability of the limiting series, after which dominated convergence applies.
-/

noncomputable section

open Filter Finset
open scoped Topology PowerSeries.WithPiTopology

namespace BTZEntropy

private theorem coeff_mul_nonneg {f g : PowerSeries ℝ}
    (hf : ∀ n, 0 ≤ f.coeff n) (hg : ∀ n, 0 ≤ g.coeff n) (n : ℕ) :
    0 ≤ (f * g).coeff n := by
  rw [PowerSeries.coeff_mul]
  exact sum_nonneg fun x _ => mul_nonneg (hf x.1) (hg x.2)

private theorem coeff_mul_ge_left {f g : PowerSeries ℝ}
    (hf : ∀ n, 0 ≤ f.coeff n) (hg : ∀ n, 0 ≤ g.coeff n)
    (hg0 : g.coeff 0 = 1) (n : ℕ) : f.coeff n ≤ (f * g).coeff n := by
  rw [PowerSeries.coeff_mul]
  calc
    f.coeff n = f.coeff n * g.coeff 0 := by rw [hg0, mul_one]
    _ ≤ ∑ x ∈ antidiagonal n, f.coeff x.1 * g.coeff x.2 :=
      single_le_sum (s := antidiagonal n) (a := (n, 0))
        (fun x _ => mul_nonneg (hf x.1) (hg x.2)) (by simp)

private theorem hasSum_coeff_mul {f g : PowerSeries ℝ} {q a b : ℝ}
    (hf : HasSum (fun n => f.coeff n * q ^ n) a)
    (hg : HasSum (fun n => g.coeff n * q ^ n) b) :
    HasSum (fun n => (f * g).coeff n * q ^ n) (a * b) := by
  have hprod : Summable (fun x : ℕ × ℕ =>
      (f.coeff x.1 * q ^ x.1) * (g.coeff x.2 * q ^ x.2)) :=
    summable_mul_of_summable_norm
      (f := fun n => f.coeff n * q ^ n)
      (g := fun n => g.coeff n * q ^ n) hf.summable.norm hg.summable.norm
  have hs := summable_sum_mul_antidiagonal_of_summable_mul
    (f := fun n => f.coeff n * q ^ n)
    (g := fun n => g.coeff n * q ^ n) hprod
  have heq : (fun n => ∑ x ∈ antidiagonal n,
      (f.coeff x.1 * q ^ x.1) * (g.coeff x.2 * q ^ x.2)) =
      (fun n => (f * g).coeff n * q ^ n) := by
    funext n
    rw [PowerSeries.coeff_mul, sum_mul]
    apply sum_congr rfl
    intro x hx
    rw [← mem_antidiagonal.mp hx, pow_add]
    ring
  rw [heq] at hs
  convert hs.hasSum using 1
  rw [← heq, ← hf.summable.tsum_mul_tsum_eq_tsum_sum_antidiagonal hg.summable hprod,
    hf.tsum_eq, hg.tsum_eq]

private theorem coeff_prod_nonneg (f : ℕ → PowerSeries ℝ)
    (hf : ∀ i n, 0 ≤ (f i).coeff n) (N n : ℕ) :
    0 ≤ (∏ i ∈ range N, f i).coeff n := by
  induction N generalizing n with
  | zero =>
    simp only [range_zero, prod_empty, PowerSeries.coeff_one]
    split_ifs <;> norm_num
  | succ N ih =>
    rw [prod_range_succ]
    exact coeff_mul_nonneg ih (hf N) n

private theorem hasSum_coeff_prod (f : ℕ → PowerSeries ℝ) (v : ℕ → ℝ)
    {q : ℝ} (h : ∀ i, HasSum (fun n => (f i).coeff n * q ^ n) (v i)) (N : ℕ) :
    HasSum (fun n => (∏ i ∈ range N, f i).coeff n * q ^ n)
      (∏ i ∈ range N, v i) := by
  induction N with
  | zero =>
    convert (hasSum_ite_eq 0 (1 : ℝ)) using 1
    · funext n
      simp only [range_zero, prod_empty, PowerSeries.coeff_one]
      split_ifs with h <;> simp [h]
    · simp
  | succ N ih =>
    simpa only [prod_range_succ] using hasSum_coeff_mul ih (h N)

/-- A formal product with nonnegative coefficients and constant term one can
be evaluated at a nonnegative real argument whenever the evaluated factors
form a convergent, bounded product. -/
theorem hasSum_of_nonneg_formalProduct
    (f : ℕ → PowerSeries ℝ) (F : PowerSeries ℝ) (v : ℕ → ℝ) {q : ℝ}
    (hq : 0 ≤ q) (hnonneg : ∀ i n, 0 ≤ (f i).coeff n)
    (hconst : ∀ i, (f i).coeff 0 = 1) (hformal : HasProd f F)
    (heval : ∀ i, HasSum (fun n => (f i).coeff n * q ^ n) (v i))
    (hbound : ∃ C : ℝ, ∀ N, ∏ i ∈ range N, v i ≤ C)
    (hprod : Multipliable v) :
    HasSum (fun n => F.coeff n * q ^ n) (∏' i, v i) := by
  let p (N : ℕ) : PowerSeries ℝ := ∏ i ∈ range N, f i
  have hpnonneg (N n : ℕ) : 0 ≤ (p N).coeff n := coeff_prod_nonneg f hnonneg N n
  have hmono (n : ℕ) : Monotone (fun N => (p N).coeff n) := by
    apply monotone_nat_of_le_succ
    intro N
    dsimp only [p]
    rw [prod_range_succ]
    exact coeff_mul_ge_left (hpnonneg N) (hnonneg N) (hconst N) n
  have hcoeff (n : ℕ) : Tendsto (fun N => (p N).coeff n) atTop (𝓝 (F.coeff n)) :=
    (PowerSeries.WithPiTopology.continuous_coeff ℝ n).continuousAt.tendsto.comp
      hformal.tendsto_prod_nat
  have hFnonneg (n : ℕ) : 0 ≤ F.coeff n :=
    ge_of_tendsto (hcoeff n) (Eventually.of_forall fun N => hpnonneg N n)
  have hp_le (N n : ℕ) : (p N).coeff n ≤ F.coeff n :=
    (hmono n).ge_of_tendsto (hcoeff n) N
  have hevalp (N : ℕ) : HasSum (fun n => (p N).coeff n * q ^ n)
      (∏ i ∈ range N, v i) := hasSum_coeff_prod f v heval N
  obtain ⟨C, hC⟩ := hbound
  have hsum : Summable (fun n => F.coeff n * q ^ n) := by
    apply summable_of_sum_le (fun n => mul_nonneg (hFnonneg n) (pow_nonneg hq n))
    intro s
    have hlim : Tendsto (fun N => ∑ n ∈ s, (p N).coeff n * q ^ n) atTop
        (𝓝 (∑ n ∈ s, F.coeff n * q ^ n)) :=
      tendsto_finsetSum s (fun n _ => (hcoeff n).mul_const _)
    apply le_of_tendsto hlim
    apply Eventually.of_forall
    intro N
    exact ((hevalp N).summable.sum_le_tsum s
      (fun n _ => mul_nonneg (hpnonneg N n) (pow_nonneg hq n))).trans
      ((hevalp N).tsum_eq ▸ hC N)
  have ht := tendsto_tsum_of_dominated_convergence hsum
    (fun n => (hcoeff n).mul_const (q ^ n))
    (Eventually.of_forall (fun N n => show ‖(p N).coeff n * q ^ n‖ ≤ F.coeff n * q ^ n by
      rw [Real.norm_of_nonneg (mul_nonneg (hpnonneg N n) (pow_nonneg hq n))]
      exact mul_le_mul_of_nonneg_right (hp_le N n) (pow_nonneg hq n)))
  have heq : (∑' n, F.coeff n * q ^ n) = ∏' i, v i := by
    apply tendsto_nhds_unique _ hprod.hasProd.tendsto_prod_nat
    simpa only [(hevalp _).tsum_eq] using ht
  exact heq ▸ hsum.hasSum

/-- The combinatorial coefficient in the formal partition product is exactly
the Virasoro descendant multiplicity used by the full-state observable. -/
theorem coeff_partitionGenFun (n : ℕ) :
    (Nat.Partition.genFun (fun _ _ => (1 : ℝ))).coeff n = (partitionCount n : ℝ) := by
  simp [Nat.Partition.coeff_genFun, Finsupp.prod, partitionCount]

/-- Euler's generating function is a convergent real series on `0 ≤ q < 1`.
This follows from the proved formal combinatorial identity and analytic
control of finite Euler products. -/
theorem hasSum_partitionCount_mul_pow {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    HasSum (fun n => (partitionCount n : ℝ) * q ^ n)
      (∏' i : ℕ, (1 - q ^ (i + 1))⁻¹) := by
  have h := hasSum_of_nonneg_formalProduct partitionFactor
    (Nat.Partition.genFun (fun _ _ => (1 : ℝ))) (partitionEulerFactor q)
    hq0 partitionFactor_coeff_nonneg
    (fun i => by simpa only [PowerSeries.coeff_zero_eq_constantCoeff] using
      partitionFactor_constantCoeff i)
    hasProd_partitionFactor (fun i => hasSum_partitionFactor i hq0 hq1)
    (partitionEulerPartialProduct_bounded hq0 hq1)
    (multipliable_partitionEulerFactor hq0 hq1)
  simpa only [coeff_partitionGenFun, partitionEulerFactor] using h

theorem summable_partitionCount_mul_pow {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    Summable (fun n => (partitionCount n : ℝ) * q ^ n) :=
  (hasSum_partitionCount_mul_pow hq0 hq1).summable

theorem tsum_partitionCount_mul_pow_eq_tprod {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    (∑' n, (partitionCount n : ℝ) * q ^ n) = ∏' i : ℕ, (1 - q ^ (i + 1))⁻¹ :=
  (hasSum_partitionCount_mul_pow hq0 hq1).tsum_eq

theorem tsum_partitionCount_mul_pow_eq_inv_tprod {q : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) :
    (∑' n, (partitionCount n : ℝ) * q ^ n) = (∏' i : ℕ, (1 - q ^ (i + 1)))⁻¹ := by
  rw [tsum_partitionCount_mul_pow_eq_tprod hq0 hq1]
  exact partitionEulerProduct_eq_inv_tprod hq0 hq1

end BTZEntropy
