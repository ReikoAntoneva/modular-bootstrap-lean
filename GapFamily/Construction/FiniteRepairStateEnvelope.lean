import GapFamily.Construction.FiniteRepairState
import GapFamily.Construction.ThermalEnvelope

/-! The error estimate on unprocessed continuum and the cleared-state
invariant imply the actual global envelope required by thermal convergence. -/

noncomputable section
open Set MeasureTheory Real
open GapFamily.Analytic
namespace GapFamily.Construction.FiniteRepairState

/-- The actual stored continuum is bounded by the fixed positive envelope at
every physical energy, including already-cleared regions. -/
theorem abs_numerator_le_tailEnvelope (s : FiniteRepairState) {a : ℝ}
    (ha : 2 ≤ a) (hc : s.Cleared)
    (herror : ∀ (j : ℤ) (E : ℝ), |(j : ℝ)| ≤ E → s.front j ≤ E →
      |s.numerator j E - vacuumLeading a E j| ≤ exp (7 * sqrt (a * E)))
    (j : ℤ) (E : ℝ) (hphysical : |(j : ℝ)| ≤ E) :
    |s.numerator j E| ≤ tailEnvelopeNumerator a E j := by
  by_cases hfront : E < s.front j
  · rw [hc j E hphysical hfront, abs_zero]
    exact tailEnvelopeNumerator_nonneg a E j ha hphysical
  · have h := herror j E hphysical (le_of_not_gt hfront)
    have hpos := vacuumLeading_nonneg a E j ha hphysical
    calc
      |s.numerator j E| = |(s.numerator j E - vacuumLeading a E j) + vacuumLeading a E j| := by
        congr 1
        ring
      _ ≤ |s.numerator j E - vacuumLeading a E j| + |vacuumLeading a E j| := abs_add_le _ _
      _ ≤ tailEnvelopeNumerator a E j := by
        rw [abs_of_nonneg hpos]
        unfold tailEnvelopeNumerator
        linarith

/-- Any proved subunit cumulative error coefficient implies the same fixed
thermal envelope, without imposing a vacuum comparison on cleared regions. -/
theorem abs_numerator_le_tailEnvelope_of_budget (s : FiniteRepairState) {a ε : ℝ}
    (ha : 2 ≤ a) (hc : s.Cleared) (hε : ε ≤ 1)
    (herror : ∀ (j : ℤ) (E : ℝ), |(j : ℝ)| ≤ E → s.front j ≤ E →
      |s.numerator j E - vacuumLeading a E j| ≤ ε * exp (7 * sqrt (a * E)))
    (j : ℤ) (E : ℝ) (hphysical : |(j : ℝ)| ≤ E) :
    |s.numerator j E| ≤ tailEnvelopeNumerator a E j := by
  apply s.abs_numerator_le_tailEnvelope ha hc _ j E hphysical
  intro J e he hf
  exact (herror J e he hf).trans (by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hε (exp_nonneg _))

/-- The pointwise physical bound is precisely the restricted ordinary
measure premise of the concrete permanent-spectrum convergence endpoint. -/
theorem ae_abs_numerator_le_tailEnvelope (s : FiniteRepairState) {a : ℝ}
    (ha : 2 ≤ a) (hc : s.Cleared)
    (herror : ∀ (j : ℤ) (E : ℝ), |(j : ℝ)| ≤ E → s.front j ≤ E →
      |s.numerator j E - vacuumLeading a E j| ≤ exp (7 * sqrt (a * E)))
    (T : ℝ) (j : ℤ) :
    ∀ᵐ E ∂(referenceMeasure j).restrict (Ici (max T |(j : ℝ)|)),
      |s.numerator j E| ≤ (1 : ℝ) * tailEnvelopeNumerator a E j := by
  filter_upwards [ae_restrict_mem measurableSet_Ici] with E hE
  simpa only [one_mul] using
    s.abs_numerator_le_tailEnvelope ha hc herror j E ((le_max_right _ _).trans hE)

end GapFamily.Construction.FiniteRepairState
