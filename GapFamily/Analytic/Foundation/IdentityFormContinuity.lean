import GapFamily.Analytic.Foundation.WeightedMoment

/-!
# Continuity of the identity part of the physical energy form

The energy weight is at least one on the support of the reference measure.
Thus weighted `L²` membership controls the actual unweighted square integral,
including its difference between two tests.
-/

noncomputable section

namespace GapFamily.Analytic

open MeasureTheory Real

/-- The actual weighted energy measure dominates the physical reference measure. -/
theorem referenceMeasure_le_energySpaceMeasure (j : ℤ) :
    referenceMeasure j ≤ energySpaceMeasure j := by
  change referenceMeasure j ≤
    (referenceMeasure j).withDensity (fun E : ℝ => ENNReal.ofReal ((1 + E) ^ 4))
  calc
    referenceMeasure j = (referenceMeasure j).withDensity 1 := withDensity_one.symm
    _ ≤ _ := by
      apply withDensity_mono
      filter_upwards [referenceMeasure_ae_above_edge j] with E hE
      have hE0 : 0 ≤ E := (abs_nonneg (j : ℝ)).trans hE.le
      have hw : 1 ≤ (1 + E) ^ 4 := one_le_pow₀ (by linarith)
      simpa only [Pi.one_apply, ← ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hw

/-- Every weighted energy test belongs to the actual unweighted physical `L²` row. -/
theorem memLp_referenceMeasure_of_energySpace (j : ℤ) {f : ℝ → ℂ}
    (hf : MemLp f 2 (energySpaceMeasure j)) : MemLp f 2 (referenceMeasure j) :=
  MemLp.mono_measure (referenceMeasure_le_energySpaceMeasure j) hf

theorem eLpNorm_referenceMeasure_le_energySpace (j : ℤ) (f : ℝ → ℂ) :
    eLpNorm f 2 (referenceMeasure j) ≤ eLpNorm f 2 (energySpaceMeasure j) :=
  eLpNorm_mono_measure f (referenceMeasure_le_energySpaceMeasure j)

/-- The ordinary `L²` size is bounded by the finite weighted energy size. -/
theorem eLpNorm_referenceMeasure_toReal_le (j : ℤ) {f : ℝ → ℂ}
    (hf : MemLp f 2 (energySpaceMeasure j)) :
    (eLpNorm f 2 (referenceMeasure j)).toReal ≤
      (eLpNorm f 2 (energySpaceMeasure j)).toReal :=
  ENNReal.toReal_mono hf.eLpNorm_ne_top (eLpNorm_referenceMeasure_le_energySpace j f)

/-- No totalized integral is used as a substitute for square integrability. -/
theorem identityForm_integrable (j : ℤ) {f : ℝ → ℂ}
    (hf : MemLp f 2 (energySpaceMeasure j)) :
    Integrable (fun E => ‖f E‖ ^ 2) (referenceMeasure j) := by
  have href := memLp_referenceMeasure_of_energySpace j hf
  exact (memLp_two_iff_integrable_sq_norm href.aestronglyMeasurable).mp href

/-- The identity contribution is the square of the genuine unweighted `L²` size. -/
theorem reference_integral_norm_sq_eq_eLpNorm_sq (j : ℤ) {f : ℝ → ℂ}
    (hf : MemLp f 2 (referenceMeasure j)) :
    (∫ E, ‖f E‖ ^ 2 ∂referenceMeasure j) =
      (eLpNorm f 2 (referenceMeasure j)).toReal ^ 2 := by
  have hsqrt : sqrt (∫ E, ‖f E‖ ^ 2 ∂referenceMeasure j) =
      (eLpNorm f 2 (referenceMeasure j)).toReal := by
    rw [MemLp.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num) hf]
    norm_num only [ENNReal.toReal_ofNat, Real.rpow_two]
    rw [← sqrt_eq_rpow, ENNReal.toReal_ofReal (sqrt_nonneg _)]
  rw [← hsqrt, sq_sqrt (integral_nonneg (fun E => sq_nonneg ‖f E‖))]

theorem identityForm_le_weighted_norm_sq (j : ℤ) {f : ℝ → ℂ}
    (hf : MemLp f 2 (energySpaceMeasure j)) :
    (∫ E, ‖f E‖ ^ 2 ∂referenceMeasure j) ≤
      (eLpNorm f 2 (energySpaceMeasure j)).toReal ^ 2 := by
  rw [reference_integral_norm_sq_eq_eLpNorm_sq j
    (memLp_referenceMeasure_of_energySpace j hf)]
  exact pow_le_pow_left₀ ENNReal.toReal_nonneg (eLpNorm_referenceMeasure_toReal_le j hf) 2

/-- Reverse triangle inequality for actual finite weighted energy sizes. -/
theorem energy_eLpNorm_toReal_sub_abs_le (j : ℤ) {f g : ℝ → ℂ}
    (hf : MemLp f 2 (energySpaceMeasure j))
    (hg : MemLp g 2 (energySpaceMeasure j)) :
    |(eLpNorm f 2 (energySpaceMeasure j)).toReal -
      (eLpNorm g 2 (energySpaceMeasure j)).toReal| ≤
        (eLpNorm (f - g) 2 (energySpaceMeasure j)).toReal := by
  simpa only [← MemLp.toLp_sub, Lp.norm_toLp] using
    abs_norm_sub_norm_le (hf.toLp f) (hg.toLp g)

/-- Approximation in weighted `L²` also controls the sizes of the approximants. -/
theorem energy_eLpNorm_toReal_le_add (j : ℤ) {f g : ℝ → ℂ}
    (hf : MemLp f 2 (energySpaceMeasure j))
    (hg : MemLp g 2 (energySpaceMeasure j)) :
    (eLpNorm f 2 (energySpaceMeasure j)).toReal ≤
      (eLpNorm g 2 (energySpaceMeasure j)).toReal +
        (eLpNorm (f - g) 2 (energySpaceMeasure j)).toReal := by
  have h := (le_abs_self _).trans (energy_eLpNorm_toReal_sub_abs_le j hf hg)
  linarith

/-- The identity row is continuous on bounded sets in the actual weighted norm. -/
theorem identityForm_sub_abs_le (j : ℤ) {f g : ℝ → ℂ}
    (hf : MemLp f 2 (energySpaceMeasure j))
    (hg : MemLp g 2 (energySpaceMeasure j)) :
    |(∫ E, ‖f E‖ ^ 2 ∂referenceMeasure j) -
      (∫ E, ‖g E‖ ^ 2 ∂referenceMeasure j)| ≤
        ((eLpNorm f 2 (energySpaceMeasure j)).toReal +
          (eLpNorm g 2 (energySpaceMeasure j)).toReal) *
            (eLpNorm (f - g) 2 (energySpaceMeasure j)).toReal := by
  have hfr := memLp_referenceMeasure_of_energySpace j hf
  have hgr := memLp_referenceMeasure_of_energySpace j hg
  have hd : |(eLpNorm f 2 (referenceMeasure j)).toReal -
      (eLpNorm g 2 (referenceMeasure j)).toReal| ≤
        (eLpNorm (f - g) 2 (referenceMeasure j)).toReal := by
    simpa only [← MemLp.toLp_sub, Lp.norm_toLp] using
      abs_norm_sub_norm_le (hfr.toLp f) (hgr.toLp g)
  rw [reference_integral_norm_sq_eq_eLpNorm_sq j hfr,
    reference_integral_norm_sq_eq_eLpNorm_sq j hgr,
    sq_sub_sq, abs_mul, abs_of_nonneg (add_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)]
  calc
    _ ≤ ((eLpNorm f 2 (referenceMeasure j)).toReal +
          (eLpNorm g 2 (referenceMeasure j)).toReal) *
            (eLpNorm (f - g) 2 (referenceMeasure j)).toReal :=
      mul_le_mul_of_nonneg_left hd (by positivity)
    _ ≤ _ := by
      exact mul_le_mul
        (add_le_add (eLpNorm_referenceMeasure_toReal_le j hf)
          (eLpNorm_referenceMeasure_toReal_le j hg))
        (eLpNorm_referenceMeasure_toReal_le j (hf.sub hg)) (by positivity) (by positivity)

/-- Weighted approximation makes the weighted sizes converge as real numbers. -/
theorem energy_eLpNorm_toReal_tendsto (j : ℤ) {F : ℕ → ℝ → ℂ} {f : ℝ → ℂ}
    (hF : ∀ n, MemLp (F n) 2 (energySpaceMeasure j))
    (hf : MemLp f 2 (energySpaceMeasure j))
    (herror : Filter.Tendsto
      (fun n => (eLpNorm (F n - f) 2 (energySpaceMeasure j)).toReal)
      Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n => (eLpNorm (F n) 2 (energySpaceMeasure j)).toReal)
      Filter.atTop (nhds (eLpNorm f 2 (energySpaceMeasure j)).toReal) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simp only [Real.norm_eq_abs]
  exact squeeze_zero (fun _ => abs_nonneg _)
    (fun n => energy_eLpNorm_toReal_sub_abs_le j (hF n) hf) herror

/-- The actual identity contribution passes to limits of weighted `L²` tests. -/
theorem identityForm_tendsto (j : ℤ) {F : ℕ → ℝ → ℂ} {f : ℝ → ℂ}
    (hF : ∀ n, MemLp (F n) 2 (energySpaceMeasure j))
    (hf : MemLp f 2 (energySpaceMeasure j))
    (herror : Filter.Tendsto
      (fun n => (eLpNorm (F n - f) 2 (energySpaceMeasure j)).toReal)
      Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n => ∫ E, ‖F n E‖ ^ 2 ∂referenceMeasure j)
      Filter.atTop (nhds (∫ E, ‖f E‖ ^ 2 ∂referenceMeasure j)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simp only [Real.norm_eq_abs]
  apply squeeze_zero (fun _ => abs_nonneg _)
    (fun n => identityForm_sub_abs_le j (hF n) hf)
  simpa only [mul_zero] using
    ((energy_eLpNorm_toReal_tendsto j hF hf herror).add_const
      (eLpNorm f 2 (energySpaceMeasure j)).toReal).mul herror

end GapFamily.Analytic
