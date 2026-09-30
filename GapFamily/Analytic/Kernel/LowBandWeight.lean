import GapFamily.Analytic.Transform.LaplaceWeight
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Mathlib.MeasureTheory.Function.LpSeminorm.SMul

/-!
# Low-band zero extension in the weighted physical row

The polynomial energy weight is bounded on each open low band. Consequently
every low-band `L²(dω_j)` vector, extended by zero, belongs to the weighted
space used in the controlled Laplace-test density argument.
-/

namespace GapFamily.Analytic

open MeasureTheory
open scoped ENNReal

/-- Multiplication by `(1+E)²` implements the energy-space weight. -/
theorem energySpaceMeasure_eLpNorm_eq (j : ℤ) {f : ℝ → ℂ}
    (hf : AEStronglyMeasurable f (referenceMeasure j)) :
    eLpNorm f 2 (energySpaceMeasure j) =
      eLpNorm (fun E : ℝ => (((1 + E) ^ 2 : ℝ) : ℂ) * f E) 2 (referenceMeasure j) := by
  have hq : Measurable (fun E : ℝ => (((1 + E) ^ 2 : ℝ) : ℂ)) := by fun_prop
  have hw : (fun E : ℝ => ‖(((1 + E) ^ 2 : ℝ) : ℂ)‖ₑ ^ 2) =
      (fun E : ℝ => ENNReal.ofReal ((1 + E) ^ 4)) := by
    funext E
    rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (sq_nonneg _), ← ENNReal.ofReal_pow (sq_nonneg _)]
    congr 1
    ring
  rw [eLpNorm_mul_eq_withDensity_sq _ hq hf]
  rw [hw]
  rfl

/-- Zero extension from the open physical band has the explicit weighted
`L²` bound. No finiteness of scalar reference mass is asserted. -/
theorem eLpNorm_lowBand_zeroExtension_le (j : ℤ) (B : ℝ) {f : ℝ → ℂ}
    (hf : AEStronglyMeasurable f
      ((referenceMeasure j).restrict (Set.Ioo |(j : ℝ)| B))) :
    eLpNorm ((Set.Ioo |(j : ℝ)| B).indicator f) 2 (energySpaceMeasure j) ≤
      ENNReal.ofReal ((1 + |B|) ^ 2) *
        eLpNorm f 2 ((referenceMeasure j).restrict (Set.Ioo |(j : ℝ)| B)) := by
  let F : ℝ → ℂ := (Set.Ioo |(j : ℝ)| B).indicator f
  have hF : AEStronglyMeasurable F (referenceMeasure j) :=
    (aestronglyMeasurable_indicator_iff measurableSet_Ioo).2 hf
  have hq : Measurable (fun E : ℝ => (((1 + E) ^ 2 : ℝ) : ℂ)) := by fun_prop
  rw [energySpaceMeasure_eLpNorm_eq j hF]
  calc
    eLpNorm (fun E : ℝ => (((1 + E) ^ 2 : ℝ) : ℂ) * F E) 2 (referenceMeasure j) ≤
        eLpNorm (fun E : ℝ => (((1 + |B|) ^ 2 : ℝ) : ℂ) * F E) 2
          (referenceMeasure j) := by
      apply eLpNorm_mono (hq.aestronglyMeasurable.mul hF)
      intro E
      by_cases hE : E ∈ Set.Ioo |(j : ℝ)| B
      · have hE0 : 0 ≤ E := (abs_nonneg (j : ℝ)).trans hE.1.le
        have hEB : 1 + E ≤ 1 + |B| := by linarith [hE.2, le_abs_self B]
        have hpow : (1 + E) ^ 2 ≤ (1 + |B|) ^ 2 :=
          pow_le_pow_left₀ (by positivity) hEB 2
        have hnE : ‖(((1 + E) ^ 2 : ℝ) : ℂ)‖ = (1 + E) ^ 2 := by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        have hnB : ‖(((1 + |B|) ^ 2 : ℝ) : ℂ)‖ = (1 + |B|) ^ 2 := by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        simp only [Pi.mul_apply, norm_mul, hnE, hnB]
        exact mul_le_mul_of_nonneg_right hpow (norm_nonneg _)
      · simp [F, Set.indicator_of_notMem hE]
    _ = ENNReal.ofReal ((1 + |B|) ^ 2) *
        eLpNorm f 2 ((referenceMeasure j).restrict (Set.Ioo |(j : ℝ)| B)) := by
      change eLpNorm ((((1 + |B|) ^ 2 : ℝ) : ℂ) • F) 2 (referenceMeasure j) = _
      rw [eLpNorm_const_smul]
      rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (sq_nonneg _)]
      rw [eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_Ioo]

/-- Every low-band Hilbert vector extends to the actual weighted physical row. -/
theorem memLp_lowBand_zeroExtension (j : ℤ) (B : ℝ) {f : ℝ → ℂ}
    (hf : MemLp f 2 ((referenceMeasure j).restrict (Set.Ioo |(j : ℝ)| B))) :
    MemLp ((Set.Ioo |(j : ℝ)| B).indicator f) 2 (energySpaceMeasure j) := by
  exact (eLpNorm_lowBand_zeroExtension_le j B hf.aestronglyMeasurable).trans_lt
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hf.eLpNorm_lt_top)

end GapFamily.Analytic
