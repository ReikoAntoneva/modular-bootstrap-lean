import BTZEntropy.Comparison.MomentTest
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
# Uniform geometry of the smooth cell test

The normalized physical energy is a quadratic whose nonnegative nonconstant
coefficients sum to the physical cell width. Consequently, on a tail cell of
width at most one, both of its nonzero derivatives are bounded by two,
uniformly in the spin, charge, cell opening, and descendant translation.
-/

noncomputable section

open Set
open scoped ContDiff
open GapFamily.Construction

namespace BTZEntropy.Comparison

def cellLinearCoefficient (r L V : ℝ) : ℝ :=
  2 * rootCoord r L * cellCoordinateLength r L V

def cellQuadraticCoefficient (r L V : ℝ) : ℝ :=
  cellCoordinateLength r L V ^ 2

theorem cellLinearCoefficient_nonneg {r L V : ℝ} (_hr : r ≤ L) (hLV : L ≤ V) :
    0 ≤ cellLinearCoefficient r L V := by
  have hd : 0 ≤ cellCoordinateLength r L V :=
    sub_nonneg.mpr (Real.sqrt_le_sqrt (sub_le_sub_right hLV r))
  exact mul_nonneg (mul_nonneg (by norm_num) (rootCoord_nonneg r L)) hd

theorem cellQuadraticCoefficient_nonneg (r L V : ℝ) :
    0 ≤ cellQuadraticCoefficient r L V := sq_nonneg _

/-- The sum of the two nonconstant coefficients is exactly the physical
width; no inverse root-coordinate length enters the derivative bound. -/
theorem cellCoefficient_sum {r L V : ℝ} (hr : r ≤ L) (hLV : L ≤ V) :
    cellLinearCoefficient r L V + cellQuadraticCoefficient r L V = V - L := by
  have hsqL := Real.sq_sqrt (sub_nonneg.mpr hr)
  have hsqV := Real.sq_sqrt (sub_nonneg.mpr (hr.trans hLV))
  dsimp [cellLinearCoefficient, cellQuadraticCoefficient, cellCoordinateLength, rootCoord]
  nlinarith

theorem normalizedCellEnergy_eq_quadratic {r L V : ℝ} (hr : r ≤ L) (z : ℝ) :
    normalizedCellEnergy r L V z = L + cellLinearCoefficient r L V * z +
      cellQuadraticCoefficient r L V * z ^ 2 := by
  have hsqL := Real.sq_sqrt (sub_nonneg.mpr hr)
  dsimp [normalizedCellEnergy, energyCoord, cellLinearCoefficient,
    cellQuadraticCoefficient, rootCoord]
  nlinarith

theorem hasDerivAt_normalizedCellEnergy (r L V z : ℝ) :
    HasDerivAt (normalizedCellEnergy r L V)
      (cellLinearCoefficient r L V + 2 * cellQuadraticCoefficient r L V * z) z := by
  change HasDerivAt (fun x => r + (rootCoord r L + cellCoordinateLength r L V * x) ^ 2)
    _ z
  convert (((hasDerivAt_const z (rootCoord r L)).add
    ((hasDerivAt_id z).const_mul (cellCoordinateLength r L V))).pow 2).const_add r using 1 <;>
    dsimp [cellLinearCoefficient, cellQuadraticCoefficient] <;> ring

theorem deriv_normalizedCellEnergy (r L V : ℝ) :
    deriv (normalizedCellEnergy r L V) =
      fun z => cellLinearCoefficient r L V + 2 * cellQuadraticCoefficient r L V * z :=
  funext (fun z => (hasDerivAt_normalizedCellEnergy r L V z).deriv)

theorem iteratedDeriv_two_normalizedCellEnergy (r L V : ℝ) :
    iteratedDeriv 2 (normalizedCellEnergy r L V) =
      fun _ => 2 * cellQuadraticCoefficient r L V := by
  rw [show 2 = 1 + 1 by rfl, iteratedDeriv_succ, iteratedDeriv_one,
    deriv_normalizedCellEnergy]
  ext z
  simpa only [id_eq, mul_one] using (((hasDerivAt_id z).const_mul (2 * cellQuadraticCoefficient r L V)).const_add
    (cellLinearCoefficient r L V)).deriv

theorem iteratedDeriv_add_three_normalizedCellEnergy (r L V : ℝ) (n : ℕ) :
    iteratedDeriv (n + 3) (normalizedCellEnergy r L V) = 0 := by
  induction n with
  | zero =>
      rw [show 0 + 3 = 2 + 1 by rfl, iteratedDeriv_succ,
        iteratedDeriv_two_normalizedCellEnergy]
      ext z
      exact deriv_const z _
  | succ n ih =>
      rw [show n + 1 + 3 = (n + 3) + 1 by omega, iteratedDeriv_succ, ih]
      ext z
      exact deriv_const z _

/-- The first derivative is bounded on the full unit interval by twice the
physical width, including at cells whose lower endpoint is a spin opening. -/
theorem abs_deriv_normalizedCellEnergy_le {r L V z : ℝ}
    (hr : r ≤ L) (hLV : L ≤ V) (hz : z ∈ Icc (0 : ℝ) 1) :
    |deriv (normalizedCellEnergy r L V) z| ≤ 2 * (V - L) := by
  rw [deriv_normalizedCellEnergy]
  have ha := cellLinearCoefficient_nonneg hr hLV
  have hb := cellQuadraticCoefficient_nonneg r L V
  have hab := cellCoefficient_sum hr hLV
  rw [abs_of_nonneg (add_nonneg ha (mul_nonneg (mul_nonneg (by norm_num) hb) hz.1))]
  nlinarith [mul_le_mul_of_nonneg_left hz.2 hb]

theorem abs_iteratedDeriv_two_normalizedCellEnergy_le {r L V z : ℝ}
    (hr : r ≤ L) (hLV : L ≤ V) :
    |iteratedDeriv 2 (normalizedCellEnergy r L V) z| ≤ 2 * (V - L) := by
  rw [iteratedDeriv_two_normalizedCellEnergy, abs_of_nonneg (by
    exact mul_nonneg (by norm_num) (cellQuadraticCoefficient_nonneg r L V))]
  have ha := cellLinearCoefficient_nonneg hr hLV
  have hab := cellCoefficient_sum hr hLV
  linarith

theorem tailCell_abs_deriv_normalizedEnergy_le {j : ℤ} {L : ℝ} {k : ℕ}
    {q : ℝ → ℝ} (cell : TailCell j L k q) (hL : |(j : ℝ)| ≤ L)
    {z : ℝ} (hz : z ∈ Icc (0 : ℝ) 1) :
    |deriv (normalizedCellEnergy |(j : ℝ)| L cell.right) z| ≤ 2 :=
  (abs_deriv_normalizedCellEnergy_le hL (by linarith [cell.right_mem.1]) hz).trans
    (by linarith [cell.right_mem.2])

theorem tailCell_abs_iteratedDeriv_two_normalizedEnergy_le {j : ℤ} {L : ℝ}
    {k : ℕ} {q : ℝ → ℝ} (cell : TailCell j L k q) (hL : |(j : ℝ)| ≤ L) (z : ℝ) :
    |iteratedDeriv 2 (normalizedCellEnergy |(j : ℝ)| L cell.right) z| ≤ 2 :=
  (abs_iteratedDeriv_two_normalizedCellEnergy_le hL
    (by linarith [cell.right_mem.1])).trans (by linarith [cell.right_mem.2])

/-- Every positive-order derivative of a translated normalized energy is
bounded by `2^i` on a cell of physical width at most one. Translation includes
the descendant level and observation energy. -/
theorem norm_iteratedFDeriv_shiftedCellEnergy_le {r L V t z : ℝ}
    (hr : r ≤ L) (hLV : L ≤ V) (hwidth : V - L ≤ 1)
    (hz : z ∈ Icc (0 : ℝ) 1) {i : ℕ} (hi : 1 ≤ i) :
    ‖iteratedFDeriv ℝ i (fun x => t + normalizedCellEnergy r L V x) z‖ ≤ (2 : ℝ) ^ i := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_const_add hi,
    Real.norm_eq_abs]
  by_cases hi3 : 3 ≤ i
  · rw [show i = (i - 3) + 3 by omega, iteratedDeriv_add_three_normalizedCellEnergy]
    simp
  · interval_cases i
    · simpa only [iteratedDeriv_one, pow_one] using
        (abs_deriv_normalizedCellEnergy_le hr hLV hz).trans (by linarith)
    · have h := abs_iteratedDeriv_two_normalizedCellEnergy_le (z := z) hr hLV
      norm_num
      linarith

/-- The derivative bound depends on the fixed kernel and requested order.
It is uniform over every physical cell of width at most one and every real
translation; no derivative of the reference or error density occurs. -/
theorem exists_uniform_cellTest_derivative_bound (φ : SmoothKernel) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (r L V t z : ℝ), r ≤ L → L ≤ V → V - L ≤ 1 →
      z ∈ Icc (0 : ℝ) 1 →
      |iteratedDeriv n (fun x => φ (t + normalizedCellEnergy r L V x)) z| ≤ C := by
  obtain ⟨C, hC, hφ⟩ := φ.compactSupport.exists_bound_iteratedFDeriv
    (show ContDiff ℝ ∞ φ from φ.smooth) n
  refine ⟨(n.factorial : ℝ) * C * 2 ^ n, by positivity, ?_⟩
  intro r L V t z hr hLV hwidth hz
  have hs : ContDiff ℝ ∞ (fun x => t + normalizedCellEnergy r L V x) := by
    unfold normalizedCellEnergy energyCoord
    fun_prop
  have hb := norm_iteratedFDeriv_comp_le (show ContDiff ℝ ∞ φ from φ.smooth)
    hs (by simp : (n : ℕ∞ω) ≤ ∞) z
    (fun i hi => hφ i hi _) (D := 2)
    (fun i hi _ => norm_iteratedFDeriv_shiftedCellEnergy_le hr hLV hwidth hz hi)
  simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs,
    Function.comp_def] using hb

/-- A single constant controls every derivative through a prescribed finite
order, still uniformly over all cells and descendant translations. -/
theorem exists_uniform_cellTest_derivative_bound_up_to (φ : SmoothKernel) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ i ≤ n, ∀ (r L V t z : ℝ),
      r ≤ L → L ≤ V → V - L ≤ 1 → z ∈ Icc (0 : ℝ) 1 →
      |iteratedDeriv i (fun x => φ (t + normalizedCellEnergy r L V x)) z| ≤ C := by
  choose C hC hbound using exists_uniform_cellTest_derivative_bound φ
  refine ⟨∑ i ∈ Finset.range (n + 1), C i,
    Finset.sum_nonneg (fun i _ => hC i), ?_⟩
  intro i hi r L V t z hr hLV hwidth hz
  exact (hbound i r L V t z hr hLV hwidth hz).trans
    (Finset.single_le_sum (fun j _ => hC j) (Finset.mem_range.mpr (by omega)))

end BTZEntropy.Comparison
