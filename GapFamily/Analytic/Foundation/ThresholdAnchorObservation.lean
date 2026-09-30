import GapFamily.Analytic.Foundation.ThresholdAnchorBand
import GapFamily.Analytic.Kernel.FullKernelObservation

/-!
# Observation on the exact threshold anchor band

The coordinate `E = B t²` maps the observation interval into `[2B,3B]`.
The scalar reference Jacobian is `2/t`, which is at least one there.
-/

noncomputable section

open MeasureTheory Real Set

namespace GapFamily.Analytic

theorem scalarAnchorCoordinate_mem {B t : ℝ} (hB : 0 < B)
    (ht : t ∈ Icc (sqrt 2) (sqrt 3)) : B * t ^ 2 ∈ scalarAnchorBand B := by
  have ht0 : 0 ≤ t := (sqrt_nonneg 2).trans ht.1
  have h2 : (2 : ℝ) ≤ t ^ 2 := by
    simpa only [sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)] using
      (sq_le_sq₀ (sqrt_nonneg 2) ht0).mpr ht.1
  have h3 : t ^ 2 ≤ (3 : ℝ) := by
    simpa only [sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)] using
      (sq_le_sq₀ ht0 (sqrt_nonneg 3)).mpr ht.2
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left h2 hB.le]
  · nlinarith [mul_le_mul_of_nonneg_left h3 hB.le]

/-- The exact ordinary scalar square mass on the high band. -/
theorem scalarAnchorSquareMass_eq_integral (B : ℝ) (hB : 0 < B) (ζ : ℝ → ℝ) :
    scalarAnchorSquareMass B ζ =
      ∫ E in scalarAnchorBand B, (1 / E) * ζ E ^ 2 := by
  rw [scalarAnchorSquareMass, scalarAnchorReference_eq B hB,
    integral_withDensity_eq_integral_toReal_smul
      (by fun_prop : Measurable (fun E : ℝ => ENNReal.ofReal (1 / E)))
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem (measurableSet_scalarAnchorBand B)] with E hE
  have hE0 : 0 < E := by linarith [hE.1]
  simp only [smul_eq_mul, ENNReal.toReal_ofReal (by positivity : 0 ≤ 1 / E)]

private theorem scalarAnchor_jacobian_lower {B t : ℝ} (hB : 0 < B)
    (ht : t ∈ Ioo (sqrt 2) (sqrt 3)) :
    (1 : ℝ) ≤ (2 * B * t) * referenceDensity 0 (observationEnergy 0 B t) := by
  have ht0 : 0 < t := (sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).trans ht.1
  have ht2 : t ≤ 2 := ht.2.le.trans ((sqrt_le_left (by norm_num : (0 : ℝ) ≤ 2)).mpr
    (by norm_num))
  have he : observationEnergy 0 B t = B * t ^ 2 := by simp [observationEnergy]
  rw [he, referenceDensity_zero (by positivity), mul_one_div]
  apply (le_div_iff₀ (by positivity : 0 < B * t ^ 2)).mpr
  nlinarith [mul_nonneg (show 0 ≤ B * t by positivity) (sub_nonneg.mpr ht2)]

/-- Coordinate observation is integrable using only continuity on the exact
anchor band; no global regularity of the scalar response is needed. -/
theorem scalarAnchor_observation_intervalIntegrable (B : ℝ) (hB : 0 < B)
    (ζ : ℝ → ℝ) (hζ : ContinuousOn ζ (scalarAnchorBand B)) :
    IntervalIntegrable (fun t : ℝ => ζ (B * t ^ 2) ^ 2) volume (sqrt 2) (sqrt 3) := by
  have hc : ContinuousOn (fun t : ℝ => ζ (B * t ^ 2) ^ 2) (Icc (sqrt 2) (sqrt 3)) :=
    (hζ.comp (by fun_prop) (fun t ht => scalarAnchorCoordinate_mem hB ht)).pow 2
  exact ContinuousOn.intervalIntegrable_of_Icc (sqrt_le_sqrt (by norm_num)) hc

/-- The exact high-band scalar square mass dominates its coordinate observation.
The sharp elementary comparison has constant one because `2/t ≥ 1`. -/
theorem integral_scalarAnchor_observation_le (B : ℝ) (hB : 0 < B)
    (ζ : ℝ → ℝ) (hζ : ContinuousOn ζ (scalarAnchorBand B)) :
    (∫ t in sqrt 2..sqrt 3, ζ (B * t ^ 2) ^ 2) ≤ scalarAnchorSquareMass B ζ := by
  have hab : sqrt (2 : ℝ) ≤ sqrt 3 := sqrt_le_sqrt (by norm_num)
  have hsub : observationEnergy 0 B '' Ioo (sqrt 2) (sqrt 3) ⊆ scalarAnchorBand B := by
    rintro E ⟨t, ht, rfl⟩
    simpa only [observationEnergy, Int.cast_zero, abs_zero, zero_add] using
      scalarAnchorCoordinate_mem hB ⟨ht.1.le, ht.2.le⟩
  have hw : IntegrableOn (fun E => referenceDensity 0 E * ζ E ^ 2) (scalarAnchorBand B) := by
    have hc : ContinuousOn (fun E : ℝ => (1 / E) * ζ E ^ 2) (scalarAnchorBand B) := by
      apply ContinuousOn.mul _ (hζ.pow 2)
      exact continuousOn_const.div continuousOn_id (fun E hE => by
        have hE0 : 0 < E := by linarith [hE.1]
        exact hE0.ne')
    apply (hc.integrableOn_compact (isCompact_scalarAnchorBand B)).congr_fun _
      (measurableSet_scalarAnchorBand B)
    intro E hE
    have hE0 : 0 ≤ E := by linarith [hE.1]
    dsimp only
    rw [referenceDensity_zero hE0]
  have hderiv : ∀ t ∈ Ioo (sqrt 2) (sqrt 3), HasDerivWithinAt
      (observationEnergy 0 B) (2 * B * t) (Ioo (sqrt 2) (sqrt 3)) t :=
    fun t _ => (observationEnergy_hasDerivAt 0 B t).hasDerivWithinAt
  have hmono := observationEnergy_monotoneOn 0 hB.le
  have hjac := (integrableOn_image_iff_integrableOn_deriv_smul_of_monotoneOn
    measurableSet_Ioo hderiv hmono (fun E => referenceDensity 0 E * ζ E ^ 2)).1
      (hw.mono_set hsub)
  have heq := integral_image_eq_integral_deriv_smul_of_monotoneOn
    measurableSet_Ioo hderiv hmono (fun E => referenceDensity 0 E * ζ E ^ 2)
  simp only [smul_eq_mul] at hjac heq
  have hcomp : IntegrableOn (fun t => ζ (observationEnergy 0 B t) ^ 2)
      (Ioo (sqrt 2) (sqrt 3)) := by
    simpa only [observationEnergy, Int.cast_zero, abs_zero, zero_add] using
      (intervalIntegrable_iff_integrableOn_Ioo_of_le hab).1
        (scalarAnchor_observation_intervalIntegrable B hB ζ hζ)
  rw [intervalIntegral.integral_of_le hab, integral_Ioc_eq_integral_Ioo]
  calc
    _ = ∫ t in Ioo (sqrt 2) (sqrt 3), ζ (observationEnergy 0 B t) ^ 2 := by
      simp only [observationEnergy, Int.cast_zero, abs_zero, zero_add]
    _ ≤ ∫ t in Ioo (sqrt 2) (sqrt 3),
        (2 * B * t) * (referenceDensity 0 (observationEnergy 0 B t) *
          ζ (observationEnergy 0 B t) ^ 2) := by
      apply integral_mono_ae hcomp hjac
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
      have h := mul_le_mul_of_nonneg_right (scalarAnchor_jacobian_lower hB ht)
        (sq_nonneg (ζ (observationEnergy 0 B t)))
      nlinarith only [h]
    _ = ∫ E in observationEnergy 0 B '' Ioo (sqrt 2) (sqrt 3),
        referenceDensity 0 E * ζ E ^ 2 := heq.symm
    _ ≤ ∫ E in scalarAnchorBand B, referenceDensity 0 E * ζ E ^ 2 :=
      setIntegral_mono_set hw
        (Filter.Eventually.of_forall fun E => mul_nonneg (referenceDensity_nonneg 0 E)
          (sq_nonneg (ζ E)))
        (Filter.Eventually.of_forall fun _ hE => hsub hE)
    _ = scalarAnchorSquareMass B ζ := by
      rw [scalarAnchorSquareMass_eq_integral B hB ζ]
      apply setIntegral_congr_fun (measurableSet_scalarAnchorBand B)
      intro E hE
      dsimp only
      rw [referenceDensity_zero (by linarith [hE.1])]

end GapFamily.Analytic
