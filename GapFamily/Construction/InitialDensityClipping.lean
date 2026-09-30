import GapFamily.Construction.CellThermalContinuumRemoval
import GapFamily.Construction.MarkerReferenceDensityOutput

/-!
# Clipping the initial continuum density

A density already zero below the old cutoff can be clipped at a later cutoff
by removing the intervening half-open cell. An exterior correction that vanishes
below the new cutoff commutes with this clipping, including at both endpoints.
-/

noncomputable section

namespace GapFamily.Construction

open Set Filter MeasureTheory Analytic

/-- A pointwise low gap identifies clipping with half-open cell removal. -/
theorem clippedDensity_eq_removeCellDensity_add (L V B : ℝ) (q r : ℝ → ℝ)
    (e : ℝ) (hq : e < L → q e = 0) (hr : e < B → r e = 0) (hVB : V ≤ B) :
    (if e < V then 0 else q e + r e) = removeCellDensity L V q e + r e := by
  by_cases heV : e < V
  · rw [ite_eq_left heV, hr (heV.trans_le hVB), add_zero]
    by_cases hLe : L ≤ e
    · exact (removeCellDensity_of_mem q ⟨hLe, heV⟩).symm
    · rw [removeCellDensity_of_not_mem q (by simp [hLe]), hq (lt_of_not_ge hLe)]
  · rw [ite_eq_right heV, removeCellDensity_of_not_mem q (by simp [heV])]

/-- The clipping identity holds under an almost-everywhere old low gap.
No endpoint atomlessness is needed because the removed cell is half-open. -/
theorem clippedDensity_ae_eq_removeCellDensity_add (μ : Measure ℝ)
    (L V B : ℝ) (q r : ℝ → ℝ)
    (hq : ∀ᵐ e ∂μ, e < L → q e = 0)
    (hr : ∀ e, e < B → r e = 0) (hVB : V ≤ B) :
    (fun e => if e < V then 0 else q e + r e) =ᵐ[μ]
      (fun e => removeCellDensity L V q e + r e) := by
  filter_upwards [hq] with e he
  exact clippedDensity_eq_removeCellDensity_add L V B q r e he (hr e) hVB

/-- A restricted-measure low gap supplies the same clipping identity. -/
theorem clippedDensity_ae_eq_removeCellDensity_add_of_restrict (μ : Measure ℝ)
    (L V B : ℝ) (q r : ℝ → ℝ)
    (hq : q =ᵐ[μ.restrict (Iio L)] 0)
    (hr : ∀ e, e < B → r e = 0) (hVB : V ≤ B) :
    (fun e => if e < V then 0 else q e + r e) =ᵐ[μ]
      (fun e => removeCellDensity L V q e + r e) := by
  apply clippedDensity_ae_eq_removeCellDensity_add μ L V B q r _ hr hVB
  exact (ae_restrict_iff' measurableSet_Iio).mp hq

/-- At the initial edge, clipping changes no existing density almost everywhere. -/
theorem clippedDensity_ae_eq_add (μ : Measure ℝ) (L : ℝ) (q r : ℝ → ℝ)
    (hq : ∀ᵐ e ∂μ, e < L → q e = 0)
    (hr : ∀ᵐ e ∂μ, e < L → r e = 0) :
    (fun e => if e < L then 0 else q e + r e) =ᵐ[μ] (fun e => q e + r e) := by
  filter_upwards [hq, hr] with e hqe hre
  by_cases he : e < L <;> simp [he, hqe, hre]

/-- The actual reference density vanishes below the larger of its cutoff and
the physical spin edge. -/
theorem canonicalMarkerReferenceDensity_ae_eq_zero_below_max (a b : ℝ)
    (ha : 2 ≤ a) (hb : 1 ≤ b) (j : ℤ) :
    ∀ᵐ e ∂referenceMeasure j, e < max b |(j : ℝ)| →
      canonicalMarkerReferenceDensity a b ha hb j e = 0 := by
  have hgap : ∀ᵐ e ∂referenceMeasure j, e < b →
      canonicalMarkerReferenceDensity a b ha hb j e = 0 :=
    (ae_restrict_iff' measurableSet_Iio).mp
      (canonicalMarkerReferenceDensity_ae_eq_zero_below_cutoff a b ha hb j)
  filter_upwards [hgap, referenceMeasure_ae_above_edge j] with e he hedge hmax
  exact he ((lt_max_iff.mp hmax).resolve_right (not_lt.mpr hedge.le))

end GapFamily.Construction
