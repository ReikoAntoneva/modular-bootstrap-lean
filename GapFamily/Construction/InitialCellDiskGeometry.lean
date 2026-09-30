import GapFamily.Construction.InitialParameter
import GapFamily.Construction.InitialRepairLogGain
import GapFamily.Construction.CellCoordinateGeometry
import Mathlib.Tactic.FieldSimp

/-! The actual initial-cell square-root interval fits the Cauchy disk at the
frozen integer scale, with at least the ratio used in the numerical budget. -/

noncomputable section
open Real
namespace GapFamily.Construction

/-- Every allowed initial endpoint has square-root width at most `sqrt(2U)`. -/
theorem initial_cellCoordinateLength_le {r L V U : ℝ}
    (hr : 0 ≤ r) (hU : 1 ≤ U) (hV : V ≤ U + 1) :
    cellCoordinateLength r L V ≤ sqrt (2 * U) := by
  unfold cellCoordinateLength rootCoord
  have h := sqrt_le_sqrt (show V - r ≤ 2 * U by linarith)
  linarith [sqrt_nonneg (L - r)]

/-- The actual charge square root is `s sqrt U` on the integer schedule. -/
theorem initialParameter_sqrt_a (R s n : ℕ) :
    sqrt ((R * s ^ 2 * n : ℕ) : ℝ) = (s : ℝ) * sqrt ((R * n : ℕ) : ℝ) := by
  have heq : ((R * s ^ 2 * n : ℕ) : ℝ) = (s : ℝ)^2 * ((R * n : ℕ) : ℝ) := by
    push_cast
    ring
  rw [heq, sqrt_mul (sq_nonneg _), sqrt_sq (Nat.cast_nonneg _)]

/-- Multiplying the actual interval width by the guaranteed numerical ratio
fits twice the literal Cauchy radius `sqrt(a)/200`. -/
theorem initialRepairRatio_mul_cellCoordinateLength_le {R n : ℕ} (s : ℕ)
    (hR : 1 ≤ R) (hn : 1 ≤ n) {r L V : ℝ} (hr : 0 ≤ r)
    (hV : V ≤ ((R * n : ℕ) : ℝ) + 1) :
    initialRepairRatio s * cellCoordinateLength r L V ≤
      sqrt ((R * s ^ 2 * n : ℕ) : ℝ) / 100 := by
  have hU : (1 : ℝ) ≤ ((R * n : ℕ) : ℝ) := by
    exact_mod_cast (show 1 ≤ R * n by nlinarith)
  calc
    _ ≤ initialRepairRatio s * sqrt (2 * ((R * n : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_left (initial_cellCoordinateLength_le hr hU hV)
        (by unfold initialRepairRatio; positivity)
    _ = _ := by
      rw [sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), initialParameter_sqrt_a]
      unfold initialRepairRatio
      have h2 : sqrt (2 : ℝ) ≠ 0 := by positivity
      field_simp

/-- The exact Cauchy width ratio is bounded by the reciprocal of the frozen
ratio; all initial cells in all initial rows share this bound. -/
theorem initial_cell_cauchy_ratio_le {R n : ℕ} {s : ℕ}
    (hR : 1 ≤ R) (hn : 1 ≤ n) (hs : 1 ≤ s) {r L V : ℝ} (hr : 0 ≤ r)
    (hV : V ≤ ((R * n : ℕ) : ℝ) + 1) :
    cellCoordinateLength r L V / (sqrt ((R * s ^ 2 * n : ℕ) : ℝ) / 100) ≤
      1 / initialRepairRatio s := by
  have hρ : 0 < initialRepairRatio s := by
    unfold initialRepairRatio
    have hsreal : (0 : ℝ) < s := by exact_mod_cast (show 0 < s by omega)
    positivity
  have ha : (0 : ℝ) < ((R * s ^ 2 * n : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < R * s ^ 2 * n by positivity)
  apply (div_le_div_iff₀ (by positivity) hρ).mpr
  simpa only [one_mul, mul_comm] using
    initialRepairRatio_mul_cellCoordinateLength_le s hR hn hr hV

end GapFamily.Construction
