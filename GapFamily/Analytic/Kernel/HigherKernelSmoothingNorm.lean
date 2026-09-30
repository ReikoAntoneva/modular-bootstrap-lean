import GapFamily.Analytic.Kernel.LowBandOperator
import Mathlib.Data.Int.Interval
import Mathlib.Algebra.Order.Floor.Ring

/-! Finite row-norm estimates for the actual Hilbert direct sum. -/

noncomputable section

open scoped BigOperators

namespace GapFamily.Analytic

/-- The sum of component norms is bounded by the square root of the number of rows. -/
theorem piLp_two_sum_norm_le {ι : Type*} [Fintype ι] {β : ι → Type*}
    [∀ i, SeminormedAddCommGroup (β i)] (f : PiLp 2 β) :
    (∑ i, ‖f i‖) ≤ Real.sqrt (Fintype.card ι) * ‖f‖ := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (s := Finset.univ)
    (f := fun i => ‖f i‖) (g := fun _ : ι => (1 : ℝ))
  simp only [mul_one, one_pow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    ← PiLp.norm_sq_eq_of_L2] at hcs
  apply (sq_le_sq₀ (by positivity) (by positivity)).mp
  rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
  simpa only [mul_comm] using hcs

/-- The finite physical low-band row sum is controlled by its Hilbert norm. -/
theorem lowBandHilbert_sum_norm_le {ι : Type*} [Fintype ι]
    (j : ι → ℤ) (B : ℝ) (f : LowBandHilbert j B) :
    (∑ i, ‖f i‖) ≤ Real.sqrt (Fintype.card ι) * ‖f‖ :=
  piLp_two_sum_norm_le f

/-- Distinct integer spins in the physical low band have cardinality at most `5 B`. -/
theorem physicalLowBand_card_le {ι : Type*} [Fintype ι]
    (J : ι → ℤ) (hJ : Function.Injective J) {B : ℝ} (hB : 1 ≤ B)
    (hband : ∀ i, |(J i : ℝ)| < B) :
    (Fintype.card ι : ℝ) ≤ 5 * B := by
  classical
  have hceil : B ≤ (⌈B⌉ : ℝ) := Int.le_ceil B
  have hn : 0 ≤ ⌈B⌉ := by
    exact_mod_cast (show (0 : ℝ) ≤ (⌈B⌉ : ℝ) by linarith)
  have hmap : Set.MapsTo J (Finset.univ : Finset ι)
      (Finset.Icc (-⌈B⌉) ⌈B⌉) := by
    intro i hi
    simp only [Finset.mem_coe, Finset.mem_Icc]
    have hiband := abs_lt.mp (hband i)
    constructor
    · exact_mod_cast (show -(⌈B⌉ : ℝ) ≤ (J i : ℝ) by linarith)
    · exact_mod_cast (show (J i : ℝ) ≤ (⌈B⌉ : ℝ) by linarith)
  have hcard : Fintype.card ι ≤ (Finset.Icc (-⌈B⌉) ⌈B⌉).card := by
    simpa only [Finset.card_univ] using Finset.card_le_card_of_injOn J hmap hJ.injOn
  have hvalue : ((Finset.Icc (-⌈B⌉) ⌈B⌉).card : ℝ) =
      (⌈B⌉ : ℝ) + 1 - -(⌈B⌉ : ℝ) := by
    exact_mod_cast (Int.card_Icc_of_le (a := -⌈B⌉) (b := ⌈B⌉) (by omega))
  calc
    (Fintype.card ι : ℝ) ≤ ((Finset.Icc (-⌈B⌉) ⌈B⌉).card : ℝ) := by exact_mod_cast hcard
    _ = (⌈B⌉ : ℝ) + 1 - -(⌈B⌉ : ℝ) := hvalue
    _ ≤ 5 * B := by linarith [Int.ceil_lt_add_one B]

/-- Distinct physical spins yield a row-norm sum with a `sqrt B` cutoff factor. -/
theorem lowBandHilbert_sum_norm_le_physical {ι : Type*} [Fintype ι]
    (J : ι → ℤ) (hJ : Function.Injective J) {B : ℝ} (hB : 1 ≤ B)
    (hband : ∀ i, |(J i : ℝ)| < B) (f : LowBandHilbert J B) :
    (∑ i, ‖f i‖) ≤ Real.sqrt 5 * Real.sqrt B * ‖f‖ := by
  calc
    _ ≤ Real.sqrt (Fintype.card ι) * ‖f‖ := lowBandHilbert_sum_norm_le J B f
    _ ≤ Real.sqrt (5 * B) * ‖f‖ :=
      mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt (physicalLowBand_card_le J hJ hB hband))
        (norm_nonneg f)
    _ = Real.sqrt 5 * Real.sqrt B * ‖f‖ := by rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 5)]

end GapFamily.Analytic
