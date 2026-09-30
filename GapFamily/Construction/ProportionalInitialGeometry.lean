import GapFamily.Construction.ProportionalParameter
import GapFamily.Construction.InitialCellDiskGeometry

/-! The initial Cauchy disk geometry for arbitrary real vacuum scale. -/

noncomputable section
open Real
namespace GapFamily.Construction

/-- All real-scale initial cells fit the same Cauchy disk ratio. -/
theorem proportional_initial_cell_cauchy_ratio_le {a r L V : ℝ} {s : ℕ}
    (ha : 0 < a) (hs : 1 ≤ s) (hr : 0 ≤ r)
    (hU : 1 ≤ proportionalCutoff a s) (hV : V ≤ proportionalCutoff a s + 1) :
    cellCoordinateLength r L V / (sqrt a / 100) ≤ 1 / initialRepairRatio s := by
  have hspos : (0 : ℝ) < s := by exact_mod_cast (show 0 < s by omega)
  have hρ : 0 < initialRepairRatio s := by unfold initialRepairRatio; positivity
  have hsqrt : sqrt a = (s : ℝ) * sqrt (proportionalCutoff a s) := by
    have heq : a = (s : ℝ) ^ 2 * proportionalCutoff a s := by
      unfold proportionalCutoff
      field_simp
    calc
      sqrt a = sqrt ((s : ℝ) ^ 2 * proportionalCutoff a s) := congrArg sqrt heq
      _ = _ := by rw [sqrt_mul (sq_nonneg _), sqrt_sq (Nat.cast_nonneg s)]
  apply (div_le_div_iff₀ (by positivity) hρ).mpr
  simp only [one_mul]
  calc
    _ = initialRepairRatio s * cellCoordinateLength r L V := by ring
    _ ≤ initialRepairRatio s * sqrt (2 * proportionalCutoff a s) :=
      mul_le_mul_of_nonneg_left (initial_cellCoordinateLength_le hr hU hV) hρ.le
    _ = sqrt a / 100 := by
      rw [sqrt_mul (show (0 : ℝ) ≤ 2 by norm_num), hsqrt]
      unfold initialRepairRatio
      have h2 : sqrt (2 : ℝ) ≠ 0 := by positivity
      field_simp

end GapFamily.Construction
