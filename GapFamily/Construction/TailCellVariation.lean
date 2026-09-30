import GapFamily.Construction.CellCoordinateMeasure
import Mathlib.MeasureTheory.VectorMeasure.WithDensityVec

/-!
# Total variation of a signed tail-cell residual

The continuum being replaced may have either sign. Its integer mass controls
the atomic count, while its absolute mass controls the residual variation.
-/

noncomputable section

open MeasureTheory Set
open scoped BigOperators Classical ENNReal
open GapFamily.Analytic

namespace GapFamily.Construction

/-- The total variation of a prescribed list of unit atoms is its list length,
including repeated nodes. -/
theorem unitAtomSignedMeasure_variation_univ {N : ℕ} (node : Fin N → ℝ) :
    (unitAtomSignedMeasure node).variation.real univ = (N : ℝ) := by
  have hupper : (unitAtomSignedMeasure node).variation univ ≤ (N : ℝ≥0∞) := by
    have h := VectorMeasure.variation_finsetSum_le Finset.univ
      (fun i => (Measure.dirac (node i)).toSignedMeasure)
    have hu := h univ
    simpa [unitAtomSignedMeasure, Measure.variation_toSignedMeasure] using hu
  have hupperReal : (unitAtomSignedMeasure node).variation.real univ ≤ (N : ℝ) := by
    simpa only [Measure.real, ENNReal.toReal_natCast] using
      ENNReal.toReal_mono (by finiteness : (N : ℝ≥0∞) ≠ ∞) hupper
  have hlower := VectorMeasure.norm_measure_le_variation
    (μ := unitAtomSignedMeasure node) (E := univ)
    (ne_top_of_le_ne_top (by finiteness) hupper)
  have hmass : unitAtomSignedMeasure node univ = (N : ℝ) := by
    simp [unitAtomSignedMeasure_apply node MeasurableSet.univ]
  rw [hmass, Real.norm_of_nonneg (Nat.cast_nonneg N)] at hlower
  exact le_antisymm hupperReal hlower

/-- The actual signed continuum has total variation equal to its absolute
ordinary physical mass. -/
theorem cellSignedDensity_variation_univ (j : ℤ) (L V : ℝ) {q : ℝ → ℝ}
    (hq : Integrable q ((referenceMeasure j).restrict (Ioo L V))) :
    (((referenceMeasure j).restrict (Ioo L V)).withDensityᵥ q).variation.real univ =
      ∫ E in Ioo L V, |q E| ∂referenceMeasure j := by
  rw [Measure.real, Measure.variation_withDensityᵥ hq,
    withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← integral_norm_eq_lintegral_enorm hq.aestronglyMeasurable]
  simp only [Real.norm_eq_abs]

/-- A residual is bounded by the atom count plus the absolute continuum mass. -/
theorem cellResidualMeasure_variation_le {N : ℕ} (j : ℤ) (L V : ℝ)
    {q : ℝ → ℝ} (node : Fin N → ℝ)
    (hq : Integrable q ((referenceMeasure j).restrict (Ioo L V))) :
    (cellResidualMeasure j L V q node).variation.real univ ≤
      (N : ℝ) + ∫ E in Ioo L V, |q E| ∂referenceMeasure j := by
  have h := VectorMeasure.variation_sub_le
    (μ := unitAtomSignedMeasure node)
    (ν := ((referenceMeasure j).restrict (Ioo L V)).withDensityᵥ q)
  have hatom : (unitAtomSignedMeasure node).variation univ ≠ ∞ := by
    have hb := (VectorMeasure.variation_finsetSum_le Finset.univ
      (fun i => (Measure.dirac (node i)).toSignedMeasure)) univ
    apply ne_top_of_le_ne_top (show (N : ℝ≥0∞) ≠ ∞ by finiteness)
    simpa [unitAtomSignedMeasure, Measure.variation_toSignedMeasure] using hb
  have hdensity :
      (((referenceMeasure j).restrict (Ioo L V)).withDensityᵥ q).variation univ ≠ ∞ := by
    rw [Measure.variation_withDensityᵥ hq, withDensity_apply _ MeasurableSet.univ,
      Measure.restrict_univ]
    exact hq.hasFiniteIntegral.ne
  have hfinite : ((unitAtomSignedMeasure node).variation +
      (((referenceMeasure j).restrict (Ioo L V)).withDensityᵥ q).variation) univ ≠ ∞ := by
    simpa only [Measure.add_apply] using ENNReal.add_ne_top.mpr ⟨hatom, hdensity⟩
  have hr := ENNReal.toReal_mono hfinite (h univ)
  change (cellResidualMeasure j L V q node).variation.real univ ≤
    ((unitAtomSignedMeasure node).variation +
      (((referenceMeasure j).restrict (Ioo L V)).withDensityᵥ q).variation).real univ at hr
  rw [measureReal_add_apply hatom hdensity, unitAtomSignedMeasure_variation_univ,
    cellSignedDensity_variation_univ j L V hq] at hr
  exact hr

/-- Matching the signed mass gives the valid factor-two absolute-mass bound,
without assuming that the continuum density is nonnegative. -/
theorem cellResidualMeasure_variation_le_twice_abs_mass {N : ℕ}
    (j : ℤ) (L V : ℝ) {q : ℝ → ℝ} (node : Fin N → ℝ)
    (hq : Integrable q ((referenceMeasure j).restrict (Ioo L V)))
    (hmass : (∫ E in Ioo L V, q E ∂referenceMeasure j) = (N : ℝ)) :
    (cellResidualMeasure j L V q node).variation.real univ ≤
      2 * ∫ E in Ioo L V, |q E| ∂referenceMeasure j := by
  have hmass_le : (N : ℝ) ≤ ∫ E in Ioo L V, |q E| ∂referenceMeasure j := by
    rw [← hmass]
    exact integral_mono hq hq.abs (fun E => le_abs_self (q E))
  exact (cellResidualMeasure_variation_le j L V node hq).trans (by linarith)

end GapFamily.Construction
