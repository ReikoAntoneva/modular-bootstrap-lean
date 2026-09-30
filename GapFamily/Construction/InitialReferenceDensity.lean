import GapFamily.Construction.CellCoordinateVacuum
import GapFamily.Construction.InitialCellPhysical

/-!
# Physical density estimates for the upper half of an initial cell

The initial left endpoint is `max b |j|`. A common upper-half coordinate
interval works for every endpoint between `U` and `W`, so the density and
negative-mass estimates can be fed directly to integer endpoint selection.
-/

noncomputable section

open Set MeasureTheory Real
open GapFamily.Analytic

namespace GapFamily.Construction

/-- Uniform upper-half geometry for every endpoint in the initial window. -/
theorem initialCell_upper_half_geometry {r b U W x : ℝ}
    (hr : 0 ≤ r) (hU : 0 < U) (hrU : r ≤ U / 16) (_hbU : b ≤ U / 16)
    (hUW : U ≤ W)
    (hx : x ∈ Icc ((rootCoord r (max b r) + rootCoord r U) / 2) (rootCoord r W)) :
    0 ≤ x ∧ U / 8 ≤ x ^ 2 ∧ U / 4 ≤ energyCoord r x ∧ energyCoord r x ≤ W := by
  have hrU' : r ≤ U := by linarith
  have hrW : r ≤ W := hrU'.trans hUW
  have hsU := Real.sq_sqrt (sub_nonneg.mpr hrU')
  have hsW := Real.sq_sqrt (sub_nonneg.mpr hrW)
  have hrootL := rootCoord_nonneg r (max b r)
  have hrootU := rootCoord_nonneg r U
  have hxhalf : rootCoord r U / 2 ≤ x := by linarith [hx.1]
  have hx0 : 0 ≤ x := by linarith
  have hxlo := (sq_le_sq₀ (by positivity : 0 ≤ rootCoord r U / 2) hx0).mpr hxhalf
  have hxhi := (sq_le_sq₀ hx0 (rootCoord_nonneg r W)).mpr hx.2
  change (sqrt (U - r)) ^ 2 = U - r at hsU
  change (sqrt (W - r)) ^ 2 = W - r at hsW
  dsimp [rootCoord] at hxlo hxhi
  dsimp [energyCoord]
  refine ⟨hx0, ?_, ?_, ?_⟩ <;> nlinarith

/-- The shortest initial cell already has coordinate length at least `sqrt U / 4`. -/
theorem initialCell_coordinate_length_lower {r b U : ℝ}
    (hr : 0 ≤ r) (hU : 0 < U) (hrU : r ≤ U / 16) (hbU : b ≤ U / 16) :
    sqrt U / 4 ≤ rootCoord r U - rootCoord r (max b r) := by
  have hL : max b r ≤ U / 16 := max_le hbU hrU
  have hrU' : r ≤ U := by linarith
  have hsU := Real.sq_sqrt hU.le
  have hleft : rootCoord r (max b r) ≤ sqrt U / 4 := by
    apply (Real.sqrt_le_left (by positivity)).mpr
    nlinarith
  have hright : sqrt U / 2 ≤ rootCoord r U := by
    apply (Real.le_sqrt (by positivity) (sub_nonneg.mpr hrU')).mpr
    nlinarith
  linarith

/-- The physical upper-half interval preserves half the vacuum exponent. -/
theorem initialCell_exponential_lower {a U E : ℝ}
    (ha : 0 ≤ a) (hU : 0 ≤ U) (hE : U / 4 ≤ E) :
    exp (4 * sqrt (a * U)) ≤ exp (8 * sqrt (a * E)) := by
  have hE0 : 0 ≤ E := by linarith
  have hsU := Real.sq_sqrt (mul_nonneg ha hU)
  have hsE := Real.sq_sqrt (mul_nonneg ha hE0)
  have hmul := mul_le_mul_of_nonneg_left hE ha
  have hs : sqrt (a * U) ≤ 2 * sqrt (a * E) := by
    apply (sq_le_sq₀ (sqrt_nonneg _) (by positivity)).mp
    nlinarith
  exact exp_le_exp.mpr (by linarith)

/-- A physical edge-times-exponential lower bound gives one constant density
bound on the common upper-half interval for the entire endpoint window. -/
theorem initialCell_coordinate_density_lower_of_edge_exponential
    (j : ℤ) {a b U W c : ℝ}
    (ha : 0 ≤ a) (hU : 0 < U) (hjU : |(j : ℝ)| ≤ U / 16)
    (hbU : b ≤ U / 16) (hUW : U ≤ W) (hc : 0 ≤ c)
    (q : ℝ → ℝ)
    (hq : ∀ E ∈ Icc (U / 4) W,
      c * (E ^ 2 - (j : ℝ) ^ 2) * exp (8 * sqrt (a * E)) ≤ q E) :
    ∀ x ∈ Icc ((rootCoord |(j : ℝ)| (max b |(j : ℝ)|) +
        rootCoord |(j : ℝ)| U) / 2) (rootCoord |(j : ℝ)| W),
      c * U * sqrt U / 8 * exp (4 * sqrt (a * U)) ≤ cellCoordinateDensity j q x := by
  intro x hx
  obtain ⟨hx0, hxsq, hElo, hEhi⟩ :=
    initialCell_upper_half_geometry (abs_nonneg (j : ℝ)) hU hjU hbU hUW hx
  have hE0 : 0 ≤ energyCoord |(j : ℝ)| x := by linarith
  have hedge : 0 ≤ (energyCoord |(j : ℝ)| x) ^ 2 - (j : ℝ) ^ 2 := by
    dsimp [energyCoord]
    nlinarith [sq_nonneg x, sq_abs (j : ℝ), abs_nonneg (j : ℝ)]
  have hnum : c * ((|(j : ℝ)| + x ^ 2) ^ 2 - |(j : ℝ)| ^ 2) *
      exp (4 * sqrt (a * U)) - 0 ≤ q (|(j : ℝ)| + x ^ 2) := by
    simpa only [energyCoord, sq_abs, sub_zero] using
      (mul_le_mul_of_nonneg_left (initialCell_exponential_lower ha hU.le hElo)
        (mul_nonneg hc hedge)).trans (hq _ ⟨hElo, hEhi⟩)
  have hraw := coordinate_density_quadratic_lower_bound
    (abs_nonneg (j : ℝ)) (show 0 < U / 4 by linarith) hElo hc
    (exp_nonneg _) (show (0 : ℝ) ≤ 0 by rfl) q hnum
  have hs : sqrt (U / 4) = sqrt U / 2 := by rw [sqrt_div hU.le]; norm_num
  simp only [mul_zero, zero_div, sub_zero, hs] at hraw
  change (2 * c * exp (4 * sqrt (a * U)) * (sqrt U / 2)) * x ^ 2 ≤
    cellCoordinateDensity j q x at hraw
  calc
    _ = (2 * c * exp (4 * sqrt (a * U)) * (sqrt U / 2)) * (U / 8) := by ring
    _ ≤ (2 * c * exp (4 * sqrt (a * U)) * (sqrt U / 2)) * x ^ 2 :=
      mul_le_mul_of_nonneg_left hxsq (by positivity)
    _ ≤ _ := hraw

/-- The common upper-half density times the shortest-cell coordinate length
has a pure exponential lower bound, with no endpoint-dependent premise. -/
theorem initialCell_density_length_lower {r a b U c : ℝ}
    (hr : 0 ≤ r) (hU : 1 ≤ U) (hrU : r ≤ U / 16) (hbU : b ≤ U / 16)
    (hc : 0 ≤ c) :
    c / 32 * exp (4 * sqrt (a * U)) ≤
      (c * U * sqrt U / 8 * exp (4 * sqrt (a * U))) *
        (rootCoord r U - rootCoord r (max b r)) := by
  have hU0 : 0 ≤ U := by linarith
  have hlength := initialCell_coordinate_length_lower hr (by linarith) hrU hbU
  calc
    _ ≤ c / 32 * exp (4 * sqrt (a * U)) * U ^ 2 :=
      le_mul_of_one_le_right (by positivity) (by nlinarith)
    _ = (c * U * sqrt U / 8 * exp (4 * sqrt (a * U))) * (sqrt U / 4) := by
      ring_nf
      rw [Real.sq_sqrt hU0]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hlength (by positivity)

/-- Every ordinarily integrable physical numerator has finite negative mass
in the same reference measure used by initial endpoint selection. -/
theorem initialCell_negativePart_integrable (j : ℤ) {L W : ℝ}
    (q : ℝ → ℝ) (hq : IntegrableOn q (Ioo L W) (referenceMeasure j)) :
    IntegrableOn (fun E => max (-q E) 0) (Ioo L W) (referenceMeasure j) :=
  hq.neg.pos_part

/-- An ordinary nonnegative error majorant bounds the actual physical
negative mass, and hence the transported initial-cell negative mass. -/
theorem initialCell_negative_mass_le_of_lower_bound (j : ℤ) {L W : ℝ}
    (hL : |(j : ℝ)| ≤ L) (hLW : L ≤ W) (q g : ℝ → ℝ)
    (hq : IntegrableOn q (Ioo L W) (referenceMeasure j))
    (hg : IntegrableOn g (Ioo L W) (referenceMeasure j))
    (hg0 : ∀ᵐ E ∂(referenceMeasure j).restrict (Ioo L W), 0 ≤ g E)
    (hlower : ∀ᵐ E ∂(referenceMeasure j).restrict (Ioo L W), -g E ≤ q E) :
    initialCellNegativeMass (rootCoord |(j : ℝ)| L) (rootCoord |(j : ℝ)| W)
      (cellCoordinateDensity j q) ≤ ∫ E in Ioo L W, g E ∂referenceMeasure j := by
  rw [initialCellNegativeMass_coordinate_eq j hL hLW]
  apply integral_mono_ae (initialCell_negativePart_integrable j q hq) hg
  filter_upwards [hg0, hlower] with E h0 hl
  exact max_le (by linarith) h0

/-- Positivity above one fixed threshold makes the initial negative mass
independent of the chosen endpoint beyond that threshold. -/
theorem initialCell_negative_mass_eq_cutoff (j : ℤ) {L Z W : ℝ}
    (hLZ : L ≤ Z) (hZW : Z ≤ W) (q : ℝ → ℝ)
    (hpositive : ∀ E, Z < E → 0 ≤ q E) :
    (∫ E in Ioo L W, max (-q E) 0 ∂referenceMeasure j) =
      ∫ E in Ioo L Z, max (-q E) 0 ∂referenceMeasure j := by
  rw [← integral_Ioc_eq_integral_Ioo, ← Ioc_union_Ioc_eq_Ioc hLZ hZW]
  rw [integral_union_eq_left_of_forall measurableSet_Ioc]
  · exact integral_Ioc_eq_integral_Ioo
  · intro E hE
    exact max_eq_right (neg_nonpos.mpr (hpositive E hE.1))

/-- Only the compact low-energy part can contribute negative mass once the
physical numerator is nonnegative beyond the fixed reference threshold. -/
theorem initialCell_negative_mass_le_cutoff_abs (j : ℤ) {L Z W : ℝ}
    (hL : |(j : ℝ)| ≤ L) (hLZ : L ≤ Z) (hZW : Z ≤ W)
    (q : ℝ → ℝ) (hq : IntegrableOn q (Ioo L Z) (referenceMeasure j))
    (hpositive : ∀ E, Z < E → 0 ≤ q E) :
    initialCellNegativeMass (rootCoord |(j : ℝ)| L) (rootCoord |(j : ℝ)| W)
      (cellCoordinateDensity j q) ≤ ∫ E in Ioo L Z, ‖q E‖ ∂referenceMeasure j := by
  rw [initialCellNegativeMass_coordinate_eq j hL (hLZ.trans hZW),
    initialCell_negative_mass_eq_cutoff j hLZ hZW q hpositive]
  apply integral_mono_ae (initialCell_negativePart_integrable j q hq) hq.norm
  exact Filter.Eventually.of_forall fun E => max_le (neg_le_abs (q E)) (norm_nonneg _)

end GapFamily.Construction
