import GapFamily.Analytic.Foundation.ReferenceMeasure
import GapFamily.Construction.CellCoordinateGeometry
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Ordinary mass transport in the square-root cell coordinate

The change of variables is literal: `E = |j| + x²`. All integrability
statements use the physical reference measure or ordinary Lebesgue measure.
The density may have either sign.
-/

noncomputable section

open Set MeasureTheory Real
open GapFamily.Analytic

namespace GapFamily.Construction

/-- Signed physical density after the literal substitution `E = |j| + x²`. -/
def cellCoordinateDensity (j : ℤ) (q : ℝ → ℝ) (x : ℝ) : ℝ :=
  2 * q (energyCoord |(j : ℝ)| x) / sqrt (x ^ 2 + 2 * |(j : ℝ)|)

theorem referenceMeasure_restrict_Ioo (j : ℤ) {L V : ℝ} (hL : |(j : ℝ)| ≤ L) :
    (referenceMeasure j).restrict (Ioo L V) =
      (volume.restrict (Ioo L V)).withDensity
        (fun E => ENNReal.ofReal (referenceDensity j E)) := by
  rw [referenceMeasure, restrict_withDensity measurableSet_Ioo,
    Measure.restrict_restrict_of_subset]
  intro E hE
  exact hL.trans_lt hE.1

/-- Ordinary physical integrability is exactly weighted Lebesgue integrability. -/
theorem integrableOn_referenceMeasure_Ioo_iff (j : ℤ) {L V : ℝ}
    (hL : |(j : ℝ)| ≤ L) (q : ℝ → ℝ) :
    IntegrableOn q (Ioo L V) (referenceMeasure j) ↔
      IntegrableOn (fun E => referenceDensity j E * q E) (Ioo L V) := by
  rw [IntegrableOn, referenceMeasure_restrict_Ioo j hL,
    integrable_withDensity_iff_integrable_smul'
      (measurable_referenceDensity j).ennreal_ofReal
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (referenceDensity_nonneg j _), smul_eq_mul, IntegrableOn]

theorem integral_referenceMeasure_Ioo (j : ℤ) {L V : ℝ}
    (hL : |(j : ℝ)| ≤ L) (q : ℝ → ℝ) :
    (∫ E in Ioo L V, q E ∂referenceMeasure j) =
      ∫ E in Ioo L V, referenceDensity j E * q E := by
  rw [referenceMeasure_restrict_Ioo j hL,
    integral_withDensity_eq_integral_toReal_smul
      (measurable_referenceDensity j).ennreal_ofReal
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (referenceDensity_nonneg j _), smul_eq_mul]

/-- The positive-coordinate Jacobian cancels the physical edge singularity exactly. -/
theorem cellCoordinate_jacobian_density (j : ℤ) {x : ℝ} (hx : 0 < x) (q : ℝ → ℝ) :
    (2 * x) * (referenceDensity j (|(j : ℝ)| + x ^ 2) * q (|(j : ℝ)| + x ^ 2)) =
      2 * q (|(j : ℝ)| + x ^ 2) / sqrt (x ^ 2 + 2 * |(j : ℝ)|) := by
  have hs : (|(j : ℝ)| + x ^ 2) ^ 2 - (j : ℝ) ^ 2 =
      x ^ 2 * (x ^ 2 + 2 * |(j : ℝ)|) := by
    nlinarith [sq_abs (j : ℝ)]
  have hpos : 0 < x ^ 2 + 2 * |(j : ℝ)| := by
    nlinarith [sq_pos_of_pos hx, abs_nonneg (j : ℝ)]
  simp only [referenceDensity, hs, Real.sqrt_mul (sq_nonneg x), Real.sqrt_sq hx.le]
  field_simp [hx.ne', (sqrt_pos.mpr hpos).ne']

theorem cellCoordinate_hasDerivAt (r x : ℝ) :
    HasDerivAt (energyCoord r) (2 * x) x := by
  change HasDerivAt (fun y : ℝ => r + y ^ 2) (2 * x) x
  convert ((hasDerivAt_id x).pow 2).const_add r using 1 <;> simp

theorem cellCoordinate_monotoneOn (r L V : ℝ) :
    MonotoneOn (energyCoord r) (Ioo (rootCoord r L) (rootCoord r V)) := by
  intro x hx y hy hxy
  have hx0 := (rootCoord_nonneg r L).trans hx.1.le
  have hy0 := (rootCoord_nonneg r L).trans hy.1.le
  dsimp [energyCoord]
  nlinarith [(sq_le_sq₀ hx0 hy0).mpr hxy]

/-- Genuine ordinary integrability is equivalent in the energy and cell coordinates. -/
theorem cellCoordinateDensity_integrable_iff (j : ℤ) {L V : ℝ}
    (hL : |(j : ℝ)| ≤ L) (hLV : L ≤ V) (q : ℝ → ℝ) :
    IntegrableOn (cellCoordinateDensity j q)
      (Ioo (rootCoord |(j : ℝ)| L) (rootCoord |(j : ℝ)| V)) ↔
      IntegrableOn q (Ioo L V) (referenceMeasure j) := by
  rw [integrableOn_referenceMeasure_Ioo_iff j hL]
  have hi := integrableOn_image_iff_integrableOn_deriv_smul_of_monotoneOn
    (f := energyCoord |(j : ℝ)|) (f' := fun x => 2 * x) measurableSet_Ioo
    (fun x _ => (cellCoordinate_hasDerivAt |(j : ℝ)| x).hasDerivWithinAt)
    (cellCoordinate_monotoneOn |(j : ℝ)| L V)
    (fun E => referenceDensity j E * q E)
  rw [image_energyCoord_Ioo _ (rootCoord_nonneg _ _) (rootCoord_nonneg _ _),
    energyCoord_rootCoord _ hL, energyCoord_rootCoord _ (hL.trans hLV)] at hi
  refine (integrableOn_congr_fun ?_ measurableSet_Ioo).trans hi.symm
  intro x hx
  exact (cellCoordinate_jacobian_density j
    ((rootCoord_nonneg _ _).trans_lt hx.1) q).symm

/-- Equality of the ordinary signed mass integrals under the square-root coordinate. -/
theorem integral_cellCoordinateDensity (j : ℤ) {L V : ℝ}
    (hL : |(j : ℝ)| ≤ L) (hLV : L ≤ V) (q : ℝ → ℝ) :
    (∫ x in Ioo (rootCoord |(j : ℝ)| L) (rootCoord |(j : ℝ)| V),
      cellCoordinateDensity j q x) = ∫ E in Ioo L V, q E ∂referenceMeasure j := by
  rw [integral_referenceMeasure_Ioo j hL]
  have hi := integral_image_eq_integral_deriv_smul_of_monotoneOn
    (f := energyCoord |(j : ℝ)|) (f' := fun x => 2 * x) measurableSet_Ioo
    (fun x _ => (cellCoordinate_hasDerivAt |(j : ℝ)| x).hasDerivWithinAt)
    (cellCoordinate_monotoneOn |(j : ℝ)| L V)
    (fun E => referenceDensity j E * q E)
  rw [image_energyCoord_Ioo _ (rootCoord_nonneg _ _) (rootCoord_nonneg _ _),
    energyCoord_rootCoord _ hL, energyCoord_rootCoord _ (hL.trans hLV)] at hi
  refine (setIntegral_congr_fun measurableSet_Ioo ?_).trans hi.symm
  intro x hx
  exact (cellCoordinate_jacobian_density j
    ((rootCoord_nonneg _ _).trans_lt hx.1) q).symm

theorem cellCoordinateDensity_intervalIntegrable_iff (j : ℤ) {L V : ℝ}
    (hL : |(j : ℝ)| ≤ L) (hLV : L ≤ V) (q : ℝ → ℝ) :
    IntervalIntegrable (cellCoordinateDensity j q) volume
      (rootCoord |(j : ℝ)| L) (rootCoord |(j : ℝ)| V) ↔
      IntegrableOn q (Ioo L V) (referenceMeasure j) := by
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le
    (show rootCoord |(j : ℝ)| L ≤ rootCoord |(j : ℝ)| V from
      sqrt_le_sqrt (sub_le_sub_right hLV _))]
  exact cellCoordinateDensity_integrable_iff j hL hLV q

/-- The cell's interval integral is its ordinary physical signed mass. -/
theorem intervalIntegral_cellCoordinateDensity (j : ℤ) {L V : ℝ}
    (hL : |(j : ℝ)| ≤ L) (hLV : L ≤ V) (q : ℝ → ℝ) :
    (∫ x in (rootCoord |(j : ℝ)| L)..(rootCoord |(j : ℝ)| V),
      cellCoordinateDensity j q x) = ∫ E in Ioo L V, q E ∂referenceMeasure j := by
  rw [intervalIntegral.integral_of_le
    (show rootCoord |(j : ℝ)| L ≤ rootCoord |(j : ℝ)| V from
      sqrt_le_sqrt (sub_le_sub_right hLV _)), integral_Ioc_eq_integral_Ioo]
  exact integral_cellCoordinateDensity j hL hLV q

theorem cellCoordinateDensity_mul_rootCoord (j : ℤ) (q φ : ℝ → ℝ)
    {x : ℝ} (hx : 0 ≤ x) :
    cellCoordinateDensity j (fun E => q E * φ (rootCoord |(j : ℝ)| E)) x =
      cellCoordinateDensity j q x * φ x := by
  simp only [cellCoordinateDensity, rootCoord_energyCoord _ hx]
  ring

/-- Arbitrary real multipliers, including signed polynomial moments, have the same integrability. -/
theorem cellCoordinateDensity_mul_integrable_iff (j : ℤ) {L V : ℝ}
    (hL : |(j : ℝ)| ≤ L) (hLV : L ≤ V) (q φ : ℝ → ℝ) :
    IntegrableOn (fun x => cellCoordinateDensity j q x * φ x)
      (Ioo (rootCoord |(j : ℝ)| L) (rootCoord |(j : ℝ)| V)) ↔
      IntegrableOn (fun E => q E * φ (rootCoord |(j : ℝ)| E))
        (Ioo L V) (referenceMeasure j) := by
  refine (integrableOn_congr_fun ?_ measurableSet_Ioo).trans
    (cellCoordinateDensity_integrable_iff j hL hLV _)
  intro x hx
  exact (cellCoordinateDensity_mul_rootCoord j q φ
    ((rootCoord_nonneg _ _).trans hx.1.le)).symm

/-- Every ordinary signed moment is transported by the actual coordinate map. -/
theorem integral_cellCoordinateDensity_mul (j : ℤ) {L V : ℝ}
    (hL : |(j : ℝ)| ≤ L) (hLV : L ≤ V) (q φ : ℝ → ℝ) :
    (∫ x in Ioo (rootCoord |(j : ℝ)| L) (rootCoord |(j : ℝ)| V),
      cellCoordinateDensity j q x * φ x) =
      ∫ E in Ioo L V, q E * φ (rootCoord |(j : ℝ)| E) ∂referenceMeasure j := by
  refine (setIntegral_congr_fun measurableSet_Ioo ?_).trans
    (integral_cellCoordinateDensity j hL hLV _)
  intro x hx
  exact (cellCoordinateDensity_mul_rootCoord j q φ
    ((rootCoord_nonneg _ _).trans hx.1.le)).symm

theorem cellCoordinateDensity_mul_intervalIntegrable_iff (j : ℤ) {L V : ℝ}
    (hL : |(j : ℝ)| ≤ L) (hLV : L ≤ V) (q φ : ℝ → ℝ) :
    IntervalIntegrable (fun x => cellCoordinateDensity j q x * φ x) volume
      (rootCoord |(j : ℝ)| L) (rootCoord |(j : ℝ)| V) ↔
      IntegrableOn (fun E => q E * φ (rootCoord |(j : ℝ)| E))
        (Ioo L V) (referenceMeasure j) := by
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le
    (show rootCoord |(j : ℝ)| L ≤ rootCoord |(j : ℝ)| V from
      sqrt_le_sqrt (sub_le_sub_right hLV _))]
  exact cellCoordinateDensity_mul_integrable_iff j hL hLV q φ

/-- Interval-integral form for polynomial moments used by the cell quadrature. -/
theorem intervalIntegral_cellCoordinateDensity_mul (j : ℤ) {L V : ℝ}
    (hL : |(j : ℝ)| ≤ L) (hLV : L ≤ V) (q φ : ℝ → ℝ) :
    (∫ x in (rootCoord |(j : ℝ)| L)..(rootCoord |(j : ℝ)| V),
      cellCoordinateDensity j q x * φ x) =
      ∫ E in Ioo L V, q E * φ (rootCoord |(j : ℝ)| E) ∂referenceMeasure j := by
  rw [intervalIntegral.integral_of_le
    (show rootCoord |(j : ℝ)| L ≤ rootCoord |(j : ℝ)| V from
      sqrt_le_sqrt (sub_le_sub_right hLV _)), integral_Ioc_eq_integral_Ioo]
  exact integral_cellCoordinateDensity_mul j hL hLV q φ

end GapFamily.Construction
