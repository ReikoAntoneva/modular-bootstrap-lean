import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Tactic.FunProp
import GapFamily.Analytic.Foundation.ReferenceEdge

/-!
# The physical reference measure

The continuous output in spin `j` is measured against
`dE / sqrt(E^2-j^2)` on the open physical half-line. The scalar endpoint
is controlled by the actual finite Laplace difference regularizer.
-/

noncomputable section

open Real Set MeasureTheory

namespace GapFamily.Analytic

/-- The finite height difference that regularizes the scalar endpoint. -/
def laplaceRegularizer (E : ℝ) : ℝ := exp (-E) * (1 - exp (-E))

/-- The polynomially weighted square used for controlled Laplace approximation. -/
def laplaceWeight (E : ℝ) : ℝ := laplaceRegularizer E ^ 2 * (1 + E) ^ 4

/-- The density of the physical spin reference measure with respect to Lebesgue measure. -/
def referenceDensity (j : ℤ) (E : ℝ) : ℝ := 1 / sqrt (E ^ 2 - (j : ℝ) ^ 2)

/-- The scalar origin and the nonzero-spin edge are excluded from the reference measure. -/
def referenceMeasure (j : ℤ) : Measure ℝ :=
  (volume.restrict (Ioi |(j : ℝ)|)).withDensity
    (fun E => ENNReal.ofReal (referenceDensity j E))

/-- The actual weighted measure whose finiteness permits polynomial approximation. -/
def laplaceReferenceMeasure (j : ℤ) : Measure ℝ :=
  (referenceMeasure j).withDensity (fun E => ENNReal.ofReal (laplaceWeight E))

theorem continuous_laplaceRegularizer : Continuous laplaceRegularizer := by
  unfold laplaceRegularizer
  fun_prop

theorem continuous_laplaceWeight : Continuous laplaceWeight := by
  exact (continuous_laplaceRegularizer.pow 2).mul ((continuous_const.add continuous_id).pow 4)

theorem measurable_referenceDensity (j : ℤ) : Measurable (referenceDensity j) := by
  unfold referenceDensity
  fun_prop

theorem referenceDensity_nonneg (j : ℤ) (E : ℝ) : 0 ≤ referenceDensity j E := by
  exact one_div_nonneg.mpr (sqrt_nonneg _)

theorem laplaceWeight_nonneg (E : ℝ) : 0 ≤ laplaceWeight E := by
  unfold laplaceWeight
  positivity

theorem laplaceRegularizer_pos {E : ℝ} (hE : 0 < E) : 0 < laplaceRegularizer E := by
  exact mul_pos (exp_pos _) (sub_pos.mpr (by simpa using exp_lt_one_iff.mpr (neg_neg_of_pos hE)))

theorem laplaceRegularizer_sq_le_exp {E : ℝ} (hE : 0 ≤ E) :
    laplaceRegularizer E ^ 2 ≤ exp (-E) := by
  have ha : 0 ≤ exp (-E) := (exp_pos _).le
  have ha1 : exp (-E) ≤ 1 := exp_le_one_iff.mpr (neg_nonpos.mpr hE)
  dsimp [laplaceRegularizer]
  nlinarith [sq_nonneg (exp (-E)), sq_nonneg (1 - exp (-E)),
    mul_nonneg (show 0 ≤ exp (-E) ^ 2 by positivity)
      (show 0 ≤ 1 - (1 - exp (-E)) ^ 2 by nlinarith)]

theorem laplaceRegularizer_sq_le_energy_mul_exp {E : ℝ} (hE : 0 ≤ E) :
    laplaceRegularizer E ^ 2 ≤ E * exp (-E) := by
  have ha : 0 ≤ exp (-E) := (exp_pos _).le
  have ha1 : exp (-E) ≤ 1 := exp_le_one_iff.mpr (neg_nonpos.mpr hE)
  have hb : 1 - exp (-E) ≤ E := by linarith [add_one_le_exp (-E)]
  have hb0 : 0 ≤ 1 - exp (-E) := sub_nonneg.mpr ha1
  have hb1 : 1 - exp (-E) ≤ 1 := by linarith
  have hbsq : (1 - exp (-E)) ^ 2 ≤ E := by nlinarith
  have hasq : exp (-E) ^ 2 ≤ exp (-E) := by nlinarith
  dsimp [laplaceRegularizer]
  rw [mul_pow]
  exact (mul_le_mul hasq hbsq (sq_nonneg _) ha).trans_eq (mul_comm _ _)

theorem referenceDensity_zero {E : ℝ} (hE : 0 ≤ E) : referenceDensity 0 E = 1 / E := by
  simp [referenceDensity, Real.sqrt_sq hE]

/-- Any fixed natural power is integrable under a positive exponential tilt. -/
theorem integrableOn_pow_mul_exp_neg (n : ℕ) :
    IntegrableOn (fun E : ℝ => E ^ n * exp (-E)) (Ioi 0) := by
  simpa only [Real.rpow_natCast, Real.rpow_one] using
    (integrableOn_rpow_mul_exp_neg_rpow (s := (n : ℝ)) (p := 1)
      (lt_of_lt_of_le (by norm_num : (-1 : ℝ) < 0) (Nat.cast_nonneg n)) zero_lt_one)

theorem integrableOn_polynomialWeight_exp_neg :
    IntegrableOn (fun E : ℝ => exp (-E) * (1 + E) ^ 4) (Ioi 0) := by
  have h0 := integrableOn_pow_mul_exp_neg 0
  have h1 := integrableOn_pow_mul_exp_neg 1
  have h2 := integrableOn_pow_mul_exp_neg 2
  have h3 := integrableOn_pow_mul_exp_neg 3
  have h4 := integrableOn_pow_mul_exp_neg 4
  convert h0.add ((h1.const_mul 4).add ((h2.const_mul 6).add ((h3.const_mul 4).add h4))) using 1
  ext E
  simp only [Pi.add_apply]
  ring

/-- At the scalar origin the finite Laplace difference cancels the `dE/E` singularity. -/
theorem scalar_regularized_reference_integrable :
    IntegrableOn (fun E => laplaceWeight E * referenceDensity 0 E) (Ioi 0) := by
  apply integrableOn_polynomialWeight_exp_neg.mono'
  · exact ((continuous_laplaceWeight.measurable.mul
      (measurable_referenceDensity 0)).aestronglyMeasurable)
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with E hE
    change 0 < E at hE
    rw [Real.norm_of_nonneg (mul_nonneg (laplaceWeight_nonneg E)
      (referenceDensity_nonneg 0 E)), referenceDensity_zero hE.le]
    have h := laplaceRegularizer_sq_le_energy_mul_exp hE.le
    dsimp [laplaceWeight]
    rw [← mul_div_assoc, mul_one]
    apply (div_le_iff₀ hE).mpr
    nlinarith [mul_le_mul_of_nonneg_right h (pow_nonneg (by linarith : 0 ≤ 1 + E) 4)]

/-- Beyond a unit distance from the spin edge the reference density is bounded by one. -/
theorem referenceDensity_le_one {j : ℤ} {E : ℝ} (hE : |(j : ℝ)| + 1 ≤ E) :
    referenceDensity j E ≤ 1 := by
  have hj : 0 ≤ |(j : ℝ)| := abs_nonneg _
  have hsq : (1 : ℝ) ≤ E ^ 2 - (j : ℝ) ^ 2 := by
    nlinarith [sq_abs (j : ℝ)]
  have hsqrt : 1 ≤ sqrt (E ^ 2 - (j : ℝ) ^ 2) := by
    simpa using sqrt_le_sqrt hsq
  exact (div_le_one (by linarith : 0 < sqrt (E ^ 2 - (j : ℝ) ^ 2))).mpr hsqrt

theorem regularized_reference_tail_integrable (j : ℤ) :
    IntegrableOn (fun E => laplaceWeight E * referenceDensity j E)
      (Ioi (|(j : ℝ)| + 1)) := by
  have hs : Ioi (|(j : ℝ)| + 1) ⊆ Ioi (0 : ℝ) := by
    intro E hE
    have hj := abs_nonneg (j : ℝ)
    change |(j : ℝ)| + 1 < E at hE
    change 0 < E
    linarith
  apply (integrableOn_polynomialWeight_exp_neg.mono_set hs).mono'
  · exact (continuous_laplaceWeight.measurable.mul
      (measurable_referenceDensity j)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with E hE
    have hE0 : 0 ≤ E := (hs hE).le
    rw [Real.norm_of_nonneg (mul_nonneg (laplaceWeight_nonneg E)
      (referenceDensity_nonneg j E))]
    calc
      laplaceWeight E * referenceDensity j E ≤ laplaceWeight E * 1 :=
        mul_le_mul_of_nonneg_left (referenceDensity_le_one hE.le) (laplaceWeight_nonneg E)
      _ ≤ exp (-E) * (1 + E) ^ 4 := by
        rw [mul_one]
        exact mul_le_mul_of_nonneg_right (laplaceRegularizer_sq_le_exp hE0) (by positivity)

/-- The weighted regularized reference density is ordinarily integrable in every spin. -/
theorem regularized_reference_integrable (j : ℤ) :
    IntegrableOn (fun E => laplaceWeight E * referenceDensity j E) (Ioi |(j : ℝ)|) := by
  by_cases hj : j = 0
  · simpa [hj] using scalar_regularized_reference_integrable
  have hr : 0 < |(j : ℝ)| := abs_pos.mpr (by exact_mod_cast hj)
  have hedge : IntegrableOn (fun E => laplaceWeight E * referenceDensity j E)
      (Ioo |(j : ℝ)| (|(j : ℝ)| + 2)) := by
    simpa only [referenceDensity, mul_one_div, sq_abs] using
      (nonzero_edge_continuous_numerator_integrableOn (B := |(j : ℝ)| + 2) hr
        continuous_laplaceWeight.continuousOn)
  apply (hedge.union (regularized_reference_tail_integrable j)).mono_set
  intro E hE
  by_cases he : E < |(j : ℝ)| + 2
  · exact Or.inl ⟨hE, he⟩
  · exact Or.inr (by change |(j : ℝ)| + 1 < E; linarith)

/-- The weighted measure is the actual product density against restricted Lebesgue measure. -/
theorem laplaceReferenceMeasure_eq_withDensity (j : ℤ) :
    laplaceReferenceMeasure j =
      (volume.restrict (Ioi |(j : ℝ)|)).withDensity
        (fun E => ENNReal.ofReal (laplaceWeight E * referenceDensity j E)) := by
  unfold laplaceReferenceMeasure referenceMeasure
  rw [← withDensity_mul _ (measurable_referenceDensity j).ennreal_ofReal
    continuous_laplaceWeight.measurable.ennreal_ofReal]
  congr 1
  ext E
  rw [Pi.mul_apply, mul_comm (laplaceWeight E), ENNReal.ofReal_mul (referenceDensity_nonneg j E)]

/-- The regularized weighted reference measure is finite for every integer spin. -/
instance instIsFiniteMeasureLaplaceReferenceMeasure (j : ℤ) :
    IsFiniteMeasure (laplaceReferenceMeasure j) := by
  rw [laplaceReferenceMeasure_eq_withDensity]
  apply isFiniteMeasure_withDensity
  apply (lintegral_ofReal_ne_top_iff_integrable
    (continuous_laplaceWeight.measurable.mul
      (measurable_referenceDensity j)).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun E => mul_nonneg
      (laplaceWeight_nonneg E) (referenceDensity_nonneg j E)))).mpr
  exact regularized_reference_integrable j

/-- The same statement in the reference measure used by the physical kernel. -/
theorem laplaceWeight_integrable_referenceMeasure (j : ℤ) :
    Integrable laplaceWeight (referenceMeasure j) := by
  rw [referenceMeasure,
    integrable_withDensity_iff_integrable_smul'
      (measurable_referenceDensity j).ennreal_ofReal
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simpa only [ENNReal.toReal_ofReal (referenceDensity_nonneg j _), smul_eq_mul, mul_comm,
    IntegrableOn]
    using regularized_reference_integrable j

/-- Expanded volume-integral formulation, including the scalar sector. -/
theorem laplaceRegularizer_weighted_integrableOn (j : ℤ) :
    IntegrableOn (fun E => laplaceRegularizer E ^ 2 * (1 + E) ^ 4 /
      sqrt (E ^ 2 - (j : ℝ) ^ 2)) (Ioi |(j : ℝ)|) := by
  simpa only [laplaceWeight, referenceDensity, mul_one_div]
    using regularized_reference_integrable j

instance instNullSingletonClassReferenceMeasure (j : ℤ) :
    NullSingletonClass (referenceMeasure j) := by
  unfold referenceMeasure
  infer_instance

instance instSigmaFiniteReferenceMeasure (j : ℤ) : SigmaFinite (referenceMeasure j) := by
  unfold referenceMeasure
  infer_instance

instance instNullSingletonClassLaplaceReferenceMeasure (j : ℤ) :
    NullSingletonClass (laplaceReferenceMeasure j) := by
  unfold laplaceReferenceMeasure
  infer_instance

/-- Almost every reference-measure point is strictly above its spin edge. -/
theorem referenceMeasure_ae_above_edge (j : ℤ) :
    ∀ᵐ E ∂referenceMeasure j, |(j : ℝ)| < E := by
  exact (withDensity_absolutelyContinuous _ _).ae_le
    (ae_restrict_mem measurableSet_Ioi)

/-- The multiplier used in the density transfer never vanishes almost everywhere. -/
theorem laplaceRegularizer_ae_pos (j : ℤ) :
    ∀ᵐ E ∂referenceMeasure j, 0 < laplaceRegularizer E := by
  filter_upwards [referenceMeasure_ae_above_edge j] with E hE
  exact laplaceRegularizer_pos ((abs_nonneg _).trans_lt hE)

/-- The finite weighted measure has the same open physical support. -/
theorem laplaceReferenceMeasure_ae_above_edge (j : ℤ) :
    ∀ᵐ E ∂laplaceReferenceMeasure j, |(j : ℝ)| < E := by
  exact (withDensity_absolutelyContinuous _ _).ae_le
    (referenceMeasure_ae_above_edge j)

/-- In the scalar sector the ordinary reference measure is precisely `dE/E`. -/
theorem referenceMeasure_zero :
    referenceMeasure 0 = (volume.restrict (Ioi (0 : ℝ))).withDensity
      (fun E => ENNReal.ofReal (1 / E)) := by
  simp only [referenceMeasure, Int.cast_zero, abs_zero]
  apply withDensity_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with E hE
  rw [referenceDensity_zero hE.le]

end GapFamily.Analytic
