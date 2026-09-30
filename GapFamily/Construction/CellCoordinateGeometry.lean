import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

/-! The literal square-root cell coordinate and the uniform tail-cell length estimate. -/

noncomputable section

open Set

namespace GapFamily.Construction

/-- Physical energy in the nonnegative square-root coordinate, with threshold `r`. -/
def energyCoord (r x : ℝ) : ℝ := r + x ^ 2

/-- The nonnegative square-root coordinate above threshold `r`. -/
def rootCoord (r E : ℝ) : ℝ := Real.sqrt (E - r)

/-- Length of the image of an energy interval under the square-root coordinate. -/
def cellCoordinateLength (r L V : ℝ) : ℝ := rootCoord r V - rootCoord r L

theorem rootCoord_nonneg (r E : ℝ) : 0 ≤ rootCoord r E := Real.sqrt_nonneg _

theorem continuous_energyCoord (r : ℝ) : Continuous (energyCoord r) := by
  unfold energyCoord
  fun_prop

theorem continuous_rootCoord (r : ℝ) : Continuous (rootCoord r) := by
  unfold rootCoord
  fun_prop

theorem rootCoord_lt_rootCoord (r : ℝ) {L V : ℝ} (hL : r ≤ L) (hLV : L < V) :
    rootCoord r L < rootCoord r V :=
  Real.sqrt_lt_sqrt (sub_nonneg.mpr hL) (sub_lt_sub_right hLV r)

@[simp]
theorem rootCoord_energyCoord (r : ℝ) {x : ℝ} (hx : 0 ≤ x) :
    rootCoord r (energyCoord r x) = x := by
  simp [rootCoord, energyCoord, Real.sqrt_sq hx]

@[simp]
theorem energyCoord_rootCoord (r : ℝ) {E : ℝ} (hE : r ≤ E) :
    energyCoord r (rootCoord r E) = E := by
  rw [energyCoord, rootCoord, Real.sq_sqrt (sub_nonneg.mpr hE)]
  ring

theorem energyCoord_mem_Ioo_iff (r : ℝ) {a b x : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hx : 0 ≤ x) :
    energyCoord r x ∈ Ioo (energyCoord r a) (energyCoord r b) ↔ x ∈ Ioo a b := by
  simp only [mem_Ioo, energyCoord, add_lt_add_iff_left, sq_lt_sq₀ ha hx, sq_lt_sq₀ hx hb]

theorem energyCoord_mem_Icc_iff (r : ℝ) {a b x : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hx : 0 ≤ x) :
    energyCoord r x ∈ Icc (energyCoord r a) (energyCoord r b) ↔ x ∈ Icc a b := by
  simp only [mem_Icc, energyCoord, add_le_add_iff_left, sq_le_sq₀ ha hx, sq_le_sq₀ hx hb]

theorem rootCoord_mem_Ioo_iff (r : ℝ) {L V E : ℝ}
    (hL : r ≤ L) (hV : r ≤ V) (hE : r ≤ E) :
    rootCoord r E ∈ Ioo (rootCoord r L) (rootCoord r V) ↔ E ∈ Ioo L V := by
  simpa only [energyCoord_rootCoord r hL, energyCoord_rootCoord r hV,
    energyCoord_rootCoord r hE] using
    (energyCoord_mem_Ioo_iff r (rootCoord_nonneg r L) (rootCoord_nonneg r V)
      (rootCoord_nonneg r E)).symm

theorem rootCoord_mem_Icc_iff (r : ℝ) {L V E : ℝ}
    (hL : r ≤ L) (hV : r ≤ V) (hE : r ≤ E) :
    rootCoord r E ∈ Icc (rootCoord r L) (rootCoord r V) ↔ E ∈ Icc L V := by
  simpa only [energyCoord_rootCoord r hL, energyCoord_rootCoord r hV,
    energyCoord_rootCoord r hE] using
    (energyCoord_mem_Icc_iff r (rootCoord_nonneg r L) (rootCoord_nonneg r V)
      (rootCoord_nonneg r E)).symm

/-- Every node in the closed root-coordinate interval maps back into the energy cell. -/
theorem energyCoord_mem_Icc (r : ℝ) {L V x : ℝ} (hL : r ≤ L) (hV : r ≤ V)
    (hx : x ∈ Icc (rootCoord r L) (rootCoord r V)) : energyCoord r x ∈ Icc L V := by
  have h := (energyCoord_mem_Icc_iff r (rootCoord_nonneg r L) (rootCoord_nonneg r V)
    ((rootCoord_nonneg r L).trans hx.1)).mpr hx
  simpa only [energyCoord_rootCoord r hL, energyCoord_rootCoord r hV] using h

theorem image_energyCoord_Icc (r : ℝ) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    energyCoord r '' Icc a b = Icc (energyCoord r a) (energyCoord r b) := by
  ext E
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (energyCoord_mem_Icc_iff r ha hb (ha.trans hx.1)).mpr hx
  · intro hE
    have hrE : r ≤ E := by
      have := hE.1
      dsimp [energyCoord] at this
      nlinarith [sq_nonneg a]
    refine ⟨rootCoord r E, ?_, energyCoord_rootCoord r hrE⟩
    apply (energyCoord_mem_Icc_iff r ha hb (rootCoord_nonneg r E)).mp
    simpa only [energyCoord_rootCoord r hrE] using hE

theorem image_energyCoord_Ioo (r : ℝ) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    energyCoord r '' Ioo a b = Ioo (energyCoord r a) (energyCoord r b) := by
  ext E
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (energyCoord_mem_Ioo_iff r ha hb (ha.trans hx.1.le)).mpr hx
  · intro hE
    have hrE : r ≤ E := by
      have := hE.1
      dsimp [energyCoord] at this
      nlinarith [sq_nonneg a]
    refine ⟨rootCoord r E, ?_, energyCoord_rootCoord r hrE⟩
    apply (energyCoord_mem_Ioo_iff r ha hb (rootCoord_nonneg r E)).mp
    simpa only [energyCoord_rootCoord r hrE] using hE

theorem image_rootCoord_Icc (r : ℝ) {L V : ℝ} (hL : r ≤ L) (hV : r ≤ V) :
    rootCoord r '' Icc L V = Icc (rootCoord r L) (rootCoord r V) := by
  ext x
  constructor
  · rintro ⟨E, hE, rfl⟩
    exact (rootCoord_mem_Icc_iff r hL hV (hL.trans hE.1)).mpr hE
  · intro hx
    refine ⟨energyCoord r x, energyCoord_mem_Icc r hL hV hx, ?_⟩
    exact rootCoord_energyCoord r ((rootCoord_nonneg r L).trans hx.1)

/-- The literal coordinate length has the source's uniform tail bounds, including spin openings. -/
theorem tail_cellCoordinateLength_bounds {r L V : ℝ}
    (hr : 0 ≤ r) (hrL : r ≤ L) (hlo : 1 / 2 ≤ V - L) (hhi : V - L ≤ 1) :
    1 / (4 * Real.sqrt (L + 1)) ≤ cellCoordinateLength r L V ∧
      cellCoordinateLength r L V ≤ 1 := by
  have hL : 0 ≤ L := hr.trans hrL
  have hLV : L ≤ V := by linarith
  have hrV : r ≤ V := hrL.trans hLV
  have ha : 0 ≤ Real.sqrt (L - r) := Real.sqrt_nonneg _
  have hb : 0 ≤ Real.sqrt (V - r) := Real.sqrt_nonneg _
  have ha2 := Real.sq_sqrt (sub_nonneg.mpr hrL)
  have hb2 := Real.sq_sqrt (sub_nonneg.mpr hrV)
  have hab : Real.sqrt (L - r) ≤ Real.sqrt (V - r) :=
    Real.sqrt_le_sqrt (sub_le_sub_right hLV r)
  have hd : 0 ≤ Real.sqrt (V - r) - Real.sqrt (L - r) := sub_nonneg.mpr hab
  have hcapA : Real.sqrt (L - r) ≤ Real.sqrt (L + 1) :=
    Real.sqrt_le_sqrt (by linarith)
  have hcapB : Real.sqrt (V - r) ≤ Real.sqrt (L + 1) :=
    Real.sqrt_le_sqrt (by linarith)
  have hcpos : 0 < Real.sqrt (L + 1) := Real.sqrt_pos.mpr (by linarith)
  dsimp [cellCoordinateLength, rootCoord]
  constructor
  · apply (div_le_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 4) hcpos)).mpr
    have hm := mul_le_mul_of_nonneg_left (add_le_add hcapB hcapA) hd
    nlinarith
  · have hdsq : (Real.sqrt (V - r) - Real.sqrt (L - r)) ^ 2 ≤ 1 := by
      nlinarith [mul_nonneg ha hd]
    exact (sq_le_sq₀ hd zero_le_one).mp (by simpa only [one_pow] using hdsq)

end GapFamily.Construction
