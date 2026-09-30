import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic

/-! Rounding a real clearing radius to the first integer repair layer.
Only the schedule is rounded; physical energies and the prescribed gap are
left unchanged. -/

noncomputable section

namespace GapFamily.Construction

/-- A real radius at least two has a natural floor at least half as large. -/
theorem half_le_floor_layerStart {x : ℝ} (hx : 2 ≤ x) :
    x / 2 ≤ (⌊x⌋₊ : ℝ) := by
  have := Nat.lt_floor_add_one x
  linarith

/-- With a radius larger than three and marker at least one, the first
integer tail layer is strictly above the marker. -/
theorem marker_lt_floor_layerStart {R b : ℝ} (hR : 3 < R) (hb : 1 ≤ b) :
    b < (⌊R * b⌋₊ : ℝ) := by
  have h := Nat.lt_floor_add_one (R * b)
  have hm := mul_lt_mul_of_pos_right hR (by linarith : 0 < b)
  linarith

theorem one_le_floor_layerStart {R b : ℝ} (hR : 3 < R) (hb : 1 ≤ b) :
    1 ≤ ⌊R * b⌋₊ := by
  have := marker_lt_floor_layerStart hR hb
  have h : (1 : ℝ) ≤ (⌊R * b⌋₊ : ℝ) := by linarith
  exact_mod_cast h

/-- The real-ray hypothesis needed by the tail-cell theorem survives flooring. -/
theorem ray_le_floor_layerStart {R κ a : ℝ} (hx : 2 ≤ R * (κ * a)) :
    (R * κ / 2) * a ≤ (⌊R * (κ * a)⌋₊ : ℝ) := by
  convert half_le_floor_layerStart hx using 1 <;> ring

end GapFamily.Construction
