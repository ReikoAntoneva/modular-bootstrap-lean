import GapFamily.Construction.CellCoordinateIntegral

/-!
# Finite reference mass on a short physical cell

Above energy one the square-root coordinate removes the spin-edge singularity,
and its reference density is at most two. A physical cell of length at most one
therefore has reference mass at most two, uniformly in its integer spin.
-/

noncomputable section

open Set MeasureTheory Real
open GapFamily.Analytic

namespace GapFamily.Construction

theorem tailCell_coordinate_denominator_ge_one (j : ℤ) {L V x : ℝ}
    (hL : 1 ≤ L) (hj : |(j : ℝ)| ≤ L) (hLV : L ≤ V)
    (hx : x ∈ Icc (rootCoord |(j : ℝ)| L) (rootCoord |(j : ℝ)| V)) :
    1 ≤ sqrt (x ^ 2 + 2 * |(j : ℝ)|) := by
  have hE := (energyCoord_mem_Icc |(j : ℝ)| hj (hj.trans hLV) hx).1
  have hs : (1 : ℝ) ≤ x ^ 2 + 2 * |(j : ℝ)| := by
    dsimp [energyCoord] at hE
    linarith [abs_nonneg (j : ℝ)]
  simpa using sqrt_le_sqrt hs

/-- The transformed reference density is continuous even when the cell opens
at a nonzero-spin edge. Energy one excludes the scalar singularity. -/
theorem tailCell_coordinate_reference_continuousOn (j : ℤ) {L V : ℝ}
    (hL : 1 ≤ L) (hj : |(j : ℝ)| ≤ L) (hLV : L ≤ V) :
    ContinuousOn (cellCoordinateDensity j (fun _ => 1))
      (Icc (rootCoord |(j : ℝ)| L) (rootCoord |(j : ℝ)| V)) := by
  apply ContinuousOn.div continuousOn_const
    ((continuous_id.pow 2).add continuous_const).sqrt.continuousOn
  intro x hx
  exact ne_of_gt (lt_of_lt_of_le zero_lt_one
    (tailCell_coordinate_denominator_ge_one j hL hj hLV hx))

/-- The actual reference measure has finite mass on every bounded physical
cell whose lower endpoint is at least one. -/
theorem tailCell_reference_integrable_one (j : ℤ) {L V : ℝ}
    (hL : 1 ≤ L) (hj : |(j : ℝ)| ≤ L) (hLV : L ≤ V) :
    IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ioo L V) (referenceMeasure j) := by
  apply (cellCoordinateDensity_integrable_iff j hj hLV _).1
  exact (tailCell_coordinate_reference_continuousOn j hL hj hLV).integrableOn_Icc.mono_set
    Ioo_subset_Icc_self

theorem tailCell_reference_isFiniteMeasure (j : ℤ) {L V : ℝ}
    (hL : 1 ≤ L) (hj : |(j : ℝ)| ≤ L) (hLV : L ≤ V) :
    IsFiniteMeasure ((referenceMeasure j).restrict (Ioo L V)) := by
  exact (integrable_const_iff_isFiniteMeasure (by norm_num : (1 : ℝ) ≠ 0)).1
    (tailCell_reference_integrable_one j hL hj hLV)

/-- A square-root coordinate interval over a physical interval of length at
most one also has length at most one. -/
theorem tailCell_coordinate_length_le_one {r L V : ℝ}
    (hrL : r ≤ L) (hLV : L ≤ V) (hV : V ≤ L + 1) :
    rootCoord r V - rootCoord r L ≤ 1 := by
  have ha := rootCoord_nonneg r L
  have hb := rootCoord_nonneg r V
  have hab : rootCoord r L ≤ rootCoord r V :=
    sqrt_le_sqrt (sub_le_sub_right hLV r)
  have ha2 := sq_sqrt (sub_nonneg.mpr hrL)
  have hb2 := sq_sqrt (sub_nonneg.mpr (hrL.trans hLV))
  change sqrt (V - r) - sqrt (L - r) ≤ 1
  dsimp [rootCoord] at ha hb hab
  nlinarith [mul_nonneg ha (sub_nonneg.mpr hab)]

/-- Uniform reference mass bound for all spins, including an opening cell. -/
theorem tailCell_reference_mass_le_two (j : ℤ) {L V : ℝ}
    (hL : 1 ≤ L) (hj : |(j : ℝ)| ≤ L) (hLV : L ≤ V) (hV : V ≤ L + 1) :
    (referenceMeasure j).real (Ioo L V) ≤ 2 := by
  have hroot : rootCoord |(j : ℝ)| L ≤ rootCoord |(j : ℝ)| V :=
    sqrt_le_sqrt (sub_le_sub_right hLV _)
  have hi := (cellCoordinateDensity_intervalIntegrable_iff j hj hLV _).2
    (tailCell_reference_integrable_one j hL hj hLV)
  have he := intervalIntegral_cellCoordinateDensity j hj hLV (fun _ => 1)
  simp only [setIntegral_const, smul_eq_mul, mul_one] at he
  rw [← he]
  calc
    _ ≤ ∫ _x in (rootCoord |(j : ℝ)| L)..(rootCoord |(j : ℝ)| V), (2 : ℝ) := by
      apply intervalIntegral.integral_mono_on hroot hi intervalIntegrable_const
      intro x hx
      have hs := tailCell_coordinate_denominator_ge_one j hL hj hLV hx
      dsimp [cellCoordinateDensity]
      apply (div_le_iff₀ (by linarith : 0 < sqrt (x ^ 2 + 2 * |(j : ℝ)|))).2
      linarith
    _ = 2 * (rootCoord |(j : ℝ)| V - rootCoord |(j : ℝ)| L) := by
      rw [intervalIntegral.integral_const, smul_eq_mul, mul_comm]
    _ ≤ 2 := by linarith [tailCell_coordinate_length_le_one hj hLV hV]

/-- A bounded signed numerator has a uniform ordinary absolute-mass bound. -/
theorem tailCell_integral_abs_le (j : ℤ) {L V C : ℝ}
    (hL : 1 ≤ L) (hj : |(j : ℝ)| ≤ L) (hLV : L ≤ V) (hV : V ≤ L + 1)
    (hC : 0 ≤ C) {q : ℝ → ℝ}
    (hq : IntegrableOn q (Ioo L V) (referenceMeasure j))
    (hbound : ∀ E ∈ Ioo L V, |q E| ≤ C) :
    (∫ E in Ioo L V, |q E| ∂referenceMeasure j) ≤ 2 * C := by
  let _ := tailCell_reference_isFiniteMeasure j hL hj hLV
  calc
    _ ≤ ∫ _E in Ioo L V, C ∂referenceMeasure j :=
      setIntegral_mono_on hq.abs (integrable_const C) measurableSet_Ioo hbound
    _ = (referenceMeasure j).real (Ioo L V) * C := by
      rw [setIntegral_const, smul_eq_mul]
    _ ≤ 2 * C := mul_le_mul_of_nonneg_right
      (tailCell_reference_mass_le_two j hL hj hLV hV) hC

end GapFamily.Construction
