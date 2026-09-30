import GapFamily.Construction.CellCoordinateGeometry
import GapFamily.Construction.TailReserve

/-!
# Quantitative shortest-cell reserve

The coordinate interval and its length are the actual square-root image of
`[L,L+1/2]`. The constants below are explicit sufficient losses from C3.
-/

open Set Real Filter
open scoped Topology

namespace GapFamily.Construction

/-- The C3 reserve has a uniform lower bound once its negative density part
uses at most half of the positive bracket. -/
theorem cell_reserve_algebra_lower_bound {S H t R d : ℝ}
    (hS : 0 ≤ S) (ht : 0 < t) (hR : 0 < R)
    (hd : 1 / (8*t) ≤ d) (hdom : 1048576*R*H ≤ S) :
    S/(268435456*t^2*R^2) ≤
      (2*S*t*d^2/(8192*R)-2*H/t)*d/(64*R) := by
  have htd : 1 ≤ 8*t*d := by
    simpa only [mul_comm] using (div_le_iff₀ (by positivity : 0 < 8*t)).mp hd
  have hsqd : 1 ≤ 64*(t*d)^2 := by nlinarith
  have hsqdS := mul_le_mul_of_nonneg_left hsqd hS
  have hb : S/(524288*t*R) ≤ 2*S*t*d^2/(8192*R)-2*H/t := by
    apply (div_le_iff₀ (by positivity : 0 < 524288*t*R)).mpr
    field_simp
    nlinarith
  have hb0 : 0 ≤ 2*S*t*d^2/(8192*R)-2*H/t := (by positivity : 0 ≤ S/(524288*t*R)).trans hb
  calc
    _ = (S/(524288*t*R))*(1/(8*t))/(64*R) := by field_simp; ring
    _ ≤ _ := div_le_div_of_nonneg_right
      (mul_le_mul hb hd (by positivity) hb0) (by positivity)

/-- The literal half-energy cell has a sufficient lower bound on its
coordinate length in terms of `sqrt L`, including the opening spin. -/
theorem shortest_cell_coordinate_length_lower {r L : ℝ}
    (hr : 0 ≤ r) (hrL : r ≤ L) (hL : 1 ≤ L) :
    1/(8*sqrt L) ≤ cellCoordinateLength r L (L+1/2) := by
  have hroot : sqrt (L+1) ≤ 2*sqrt L := by
    apply (sqrt_le_iff).mpr
    refine ⟨by positivity, ?_⟩
    nlinarith [sq_sqrt (show 0 ≤ L by linarith)]
  have h := (tail_cellCoordinateLength_bounds (V := L+1/2) hr hrL
    (by linarith) (by linarith)).1
  apply le_trans _ h
  apply div_le_div_of_nonneg_left zero_le_one (by positivity)
  linarith

/-- A quantitative physical shortest-cell C3 reserve. -/
theorem shortest_cell_reserve_lower_bound {r L c P H : ℝ} {k : ℕ}
    (hr : 0 ≤ r) (hrL : r ≤ L) (hL : 1 ≤ L) (hc : 0 ≤ c) (hP : 0 ≤ P)
    (hdom : 1048576*((k : ℝ)+1)^6*H ≤ c*P) :
    c*P/(268435456*L*((k : ℝ)+1)^12) ≤
      ((2*c*P*sqrt L)*(cellCoordinateLength r L (L+1/2))^2/
          (8192*((k : ℝ)+1)^6)-2*H/sqrt L)*
        cellCoordinateLength r L (L+1/2)/(64*((k : ℝ)+1)^6) := by
  have h := cell_reserve_algebra_lower_bound (mul_nonneg hc hP)
    (sqrt_pos.mpr (by linarith : 0 < L)) (show 0 < ((k : ℝ)+1)^6 by positivity)
    (shortest_cell_coordinate_length_lower hr hrL hL) hdom
  simpa only [sq_sqrt (show 0 ≤ L by linarith), ← pow_mul, mul_assoc] using h

end GapFamily.Construction
