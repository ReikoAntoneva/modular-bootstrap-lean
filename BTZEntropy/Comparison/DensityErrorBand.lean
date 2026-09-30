import GapFamily.Construction.TailCellReference
import GapFamily.Analytic.Kernel.HigherKernelResponseMoment
import Mathlib.Data.Int.Interval

/-!
# Reference mass on a bounded physical band

The first reference moment controls the ordinary mass above energy one, even
when the lower endpoint coincides with a nonzero spin edge. The resulting
bound is independent of the spin and is suitable for summing density errors.
-/

noncomputable section

open Set MeasureTheory
open GapFamily.Analytic GapFamily.Construction
open scoped BigOperators

namespace BTZEntropy

/-- Every bounded physical band starting above energy one has finite reference
mass. Empty bands are included. -/
theorem referenceBand_isFiniteMeasure (j : ℤ) {L V : ℝ}
    (hL : 1 ≤ L) (hj : |(j : ℝ)| ≤ L) :
    IsFiniteMeasure ((referenceMeasure j).restrict (Ioo L V)) := by
  by_cases hLV : L ≤ V
  · exact tailCell_reference_isFiniteMeasure j hL hj hLV
  · simp [Ioo_eq_empty_of_le (le_of_not_ge hLV)]
    infer_instance

/-- Above energy one, reference mass is bounded by the upper energy, uniformly
in the spin. The integrable first moment also handles the square-root edge. -/
theorem referenceBand_mass_le (j : ℤ) {L V : ℝ}
    (hL : 1 ≤ L) (hj : |(j : ℝ)| ≤ L) (hV : 0 ≤ V) :
    (referenceMeasure j).real (Ioo L V) ≤ V := by
  by_cases hLV : L ≤ V
  · let _ := referenceBand_isFiniteMeasure j hL hj (V := V)
    have hsub : Ioo L V ⊆ Ioo |(j : ℝ)| V :=
      fun E hE => ⟨lt_of_le_of_lt hj hE.1, hE.2⟩
    have hi : IntegrableOn (fun E : ℝ => E) (Ioo L V) (referenceMeasure j) :=
      (show IntegrableOn (fun E : ℝ => E) (Ioo |(j : ℝ)| V)
        (referenceMeasure j) from lowBand_energy_integrable j V).mono_set hsub
    calc
      _ = ∫ _E in Ioo L V, (1 : ℝ) ∂referenceMeasure j := by simp
      _ ≤ ∫ E in Ioo L V, E ∂referenceMeasure j := by
        apply setIntegral_mono_on (integrable_const 1) hi measurableSet_Ioo
        intro E hE
        exact hL.trans hE.1.le
      _ ≤ ∫ E in Ioo |(j : ℝ)| V, E ∂referenceMeasure j := by
        apply setIntegral_mono_set (lowBand_energy_integrable j V)
        · filter_upwards [ae_restrict_mem measurableSet_Ioo] with E hE
          exact (abs_nonneg (j : ℝ)).trans hE.1.le
        · exact Filter.Eventually.of_forall hsub
      _ = Real.sqrt (V ^ 2 - (j : ℝ) ^ 2) :=
        lowBand_integral_energy j (hj.trans hLV)
      _ ≤ V := (Real.sqrt_le_left hV).mpr (by nlinarith [sq_nonneg (j : ℝ)])
  · simp [Ioo_eq_empty_of_le (le_of_not_ge hLV), hV]

/-- The spin-dependent lower endpoint used by the density comparison produces
a finite ordinary reference measure. -/
theorem densityErrorBand_isFiniteMeasure (j : ℤ) {T V : ℝ} (hT : 1 ≤ T) :
    IsFiniteMeasure ((referenceMeasure j).restrict (Ioo (max T |(j : ℝ)|) V)) :=
  referenceBand_isFiniteMeasure j (hT.trans (le_max_left _ _)) (le_max_right _ _)

/-- A uniform reference-mass estimate for the actual comparison band. -/
theorem densityErrorBand_mass_le (j : ℤ) {T V : ℝ} (hT : 1 ≤ T) (hV : 0 ≤ V) :
    (referenceMeasure j).real (Ioo (max T |(j : ℝ)|) V) ≤ V :=
  referenceBand_mass_le j (hT.trans (le_max_left _ _)) (le_max_right _ _) hV

/-- The integer spin window contains exactly `2 * N + 1` rows. -/
theorem densityErrorBand_sum_const (N : ℕ) (A : ℝ) :
    (∑ _j ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), A) = (2 * (N : ℝ) + 1) * A := by
  have hcard : ((Finset.Icc (-(N : ℤ)) (N : ℤ)).card : ℝ) = 2 * (N : ℝ) + 1 := by
    have h : ((Finset.Icc (-(N : ℤ)) (N : ℤ)).card : ℝ) =
        (N : ℝ) + 1 - -(N : ℝ) := by
      exact_mod_cast Int.card_Icc_of_le (a := -(N : ℤ)) (b := (N : ℤ)) (by omega)
    linarith
  simp only [Finset.sum_const, nsmul_eq_mul, hcard]

end BTZEntropy
