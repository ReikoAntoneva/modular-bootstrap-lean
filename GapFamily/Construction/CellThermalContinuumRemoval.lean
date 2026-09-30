import GapFamily.Analytic.Foundation.ReferenceMeasure
import Mathlib.MeasureTheory.VectorMeasure.WithDensity

/-!
# Exact thermal continuum removal on one cell

The density vanishes pointwise on the half-open cell `[L,V)` and is unchanged
at its right endpoint. The physical reference measure has no endpoint atom,
so the removed ordinary signed measure is exactly the thermal density on
`(L,V)`. Global thermal integrability implies all local integrability used here.
-/

noncomputable section
namespace GapFamily.Construction
open Set Filter MeasureTheory
open Analytic

/-- Remove the continuum on the half-open cell, retaining its right endpoint. -/
def removeCellDensity (L V : ℝ) (q : ℝ → ℝ) : ℝ → ℝ :=
  (Ico L V)ᶜ.indicator q

theorem removeCellDensity_of_mem {L V E : ℝ} (q : ℝ → ℝ) (hE : E ∈ Ico L V) :
    removeCellDensity L V q E = 0 := by
  simp [removeCellDensity, hE]

theorem removeCellDensity_of_not_mem {L V E : ℝ} (q : ℝ → ℝ) (hE : E ∉ Ico L V) :
    removeCellDensity L V q E = q E := by
  simp [removeCellDensity, hE]

/-- A genuine cell removes the left endpoint pointwise. -/
theorem removeCellDensity_left {L V : ℝ} (q : ℝ → ℝ) (hLV : L < V) :
    removeCellDensity L V q L = 0 :=
  removeCellDensity_of_mem q ⟨le_rfl, hLV⟩

/-- The right endpoint remains available to the next cell. -/
@[simp] theorem removeCellDensity_right (L V : ℝ) (q : ℝ → ℝ) :
    removeCellDensity L V q V = q V :=
  removeCellDensity_of_not_mem q (by simp)

/-- The two cell conventions give the exact same restricted physical measure. -/
theorem referenceMeasure_restrict_Ico_eq_Ioo (j : ℤ) (L V : ℝ) :
    (referenceMeasure j).restrict (Ico L V) = (referenceMeasure j).restrict (Ioo L V) :=
  restrict_Ioo_eq_restrict_Ico.symm

/-- Thermal multiplication commutes pointwise with removing the cell. -/
theorem thermal_removeCellDensity_eq_indicator (L V t : ℝ) (q : ℝ → ℝ) :
    (fun E => Real.exp (-t * E) * removeCellDensity L V q E) =
      (Ico L V)ᶜ.indicator (fun E => Real.exp (-t * E) * q E) := by
  funext E
  by_cases hE : E ∈ Ico L V <;> simp [removeCellDensity, hE]

/-- Removal preserves ordinary thermal integrability at any real temperature
for which that integrability has already been proved. -/
theorem integrable_thermal_removeCellDensity (j : ℤ) (L V t : ℝ) {q : ℝ → ℝ}
    (hq : Integrable (fun E => Real.exp (-t * E) * q E) (referenceMeasure j)) :
    Integrable (fun E => Real.exp (-t * E) * removeCellDensity L V q E)
      (referenceMeasure j) := by
  rw [thermal_removeCellDensity_eq_indicator]
  exact hq.indicator measurableSet_Ico.compl

/-- The removed thermal continuum is an ordinary local density. -/
theorem integrableOn_thermal_density_cell (j : ℤ) (L V t : ℝ) {q : ℝ → ℝ}
    (hq : Integrable (fun E => Real.exp (-t * E) * q E) (referenceMeasure j)) :
    IntegrableOn (fun E => Real.exp (-t * E) * q E) (Ioo L V) (referenceMeasure j) :=
  hq.integrableOn

/-- On a bounded cell the inverse thermal weight is bounded, so even the
untilted signed continuum density is ordinarily integrable. -/
theorem integrableOn_density_of_thermal_integrable {μ : Measure ℝ}
    {t : ℝ} {q : ℝ → ℝ} (hq : Integrable (fun E => Real.exp (-t * E) * q E) μ)
    (L V : ℝ) : IntegrableOn q (Ioo L V) μ := by
  have hi : IntegrableOn (fun E => (Real.exp (-t * E) * q E) * Real.exp (t * E))
      (Ioo L V) μ :=
    hq.integrableOn.mul_continuousOn_of_subset (by fun_prop)
      measurableSet_Ioo isCompact_Icc Ioo_subset_Icc_self
  apply hi.congr
  filter_upwards [] with E
  calc
    (Real.exp (-t * E) * q E) * Real.exp (t * E) =
        (Real.exp (-t * E) * Real.exp (t * E)) * q E := by ring
    _ = q E := by rw [← Real.exp_add]; simp

private theorem restricted_density_eq_indicator (μ : Measure ℝ) (s : Set ℝ)
    (hs : MeasurableSet s) (f : ℝ → ℝ) (hf : Integrable f (μ.restrict s)) :
    (μ.restrict s).withDensityᵥ f = μ.withDensityᵥ (s.indicator f) := by
  ext t ht
  rw [withDensityᵥ_apply hf ht,
    withDensityᵥ_apply ((integrable_indicator_iff hs).mpr hf) ht,
    setIntegral_indicator hs, Measure.restrict_restrict ht]

/-- Literal continuum removal subtracts exactly the old cell's ordinary
thermal signed density. The endpoint convention contributes no atom. -/
theorem thermal_removeCellDensity_withDensity (j : ℤ) (L V t : ℝ) {q : ℝ → ℝ}
    (hq : Integrable (fun E => Real.exp (-t * E) * q E) (referenceMeasure j)) :
    (referenceMeasure j).withDensityᵥ
        (fun E => Real.exp (-t * E) * removeCellDensity L V q E) =
      (referenceMeasure j).withDensityᵥ (fun E => Real.exp (-t * E) * q E) -
        ((referenceMeasure j).restrict (Ioo L V)).withDensityᵥ
          (fun E => Real.exp (-t * E) * q E) := by
  rw [thermal_removeCellDensity_eq_indicator, Set.indicator_compl,
    withDensityᵥ_sub hq (hq.indicator measurableSet_Ico),
    ← restricted_density_eq_indicator (referenceMeasure j) (Ico L V) measurableSet_Ico
      (fun E => Real.exp (-t * E) * q E) hq.restrict,
    referenceMeasure_restrict_Ico_eq_Ioo]

end GapFamily.Construction
