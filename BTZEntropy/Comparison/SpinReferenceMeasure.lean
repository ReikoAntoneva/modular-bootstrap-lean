import BTZEntropy.Comparison.SpinPoisson
import BTZEntropy.Analytic.ReferenceInversionAnalytic
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-!
# The actual integer-spin primary reference measure

Each physical spin measure is embedded in the spin-energy product and the
countable sum retains every integer spin, including zero. The leading vacuum
numerator is its weight. All thermal integrability statements are proved from
the existing physical reference transform and absolute Fourier summability.
-/

noncomputable section

open MeasureTheory GapFamily.Analytic
open scoped FourierTransform

namespace BTZEntropy

/-- The disjoint union of the actual physical energy measures at integer spin. -/
def spinReferenceMeasure : Measure (ℤ × ℝ) :=
  Measure.sum fun j : ℤ => (referenceMeasure j).map (fun E => (j, E))

instance instSFiniteSpinReferenceMeasure : SFinite spinReferenceMeasure := by
  unfold spinReferenceMeasure
  infer_instance

/-- Nonnegative energy, agreeing almost everywhere with the physical energy coordinate. -/
def spinReferenceEnergy (q : ℤ × ℝ) : ℝ := max 0 q.2

/-- The actual four-seed denominator-one numerator. -/
def spinReferenceWeight (a : ℝ) (q : ℤ × ℝ) : ℝ := vacuumLeading a q.2 q.1

theorem measurable_spinReferenceEnergy : Measurable spinReferenceEnergy :=
  measurable_const.max measurable_snd

theorem spinReferenceEnergy_nonneg (q : ℤ × ℝ) : 0 ≤ spinReferenceEnergy q :=
  le_max_left _ _

theorem measurable_spinReferenceWeight (a : ℝ) : Measurable (spinReferenceWeight a) := by
  apply measurable_from_prod_countable_right
  intro j
  unfold spinReferenceWeight vacuumLeading
  simp only [vacuumHigherTerm_zero_factor]
  apply Continuous.measurable
  apply Complex.continuous_re.comp
  apply Continuous.mul
  · apply continuous_const.mul
    exact (cosRoot_continuous.comp (by fun_prop)).sub (cosRoot_continuous.comp (by fun_prop))
  · exact (cosRoot_continuous.comp (by fun_prop)).sub (cosRoot_continuous.comp (by fun_prop))

theorem spinReferenceMeasure_ae_above_edge :
    ∀ᵐ q ∂spinReferenceMeasure, |(q.1 : ℝ)| < q.2 := by
  apply Measure.ae_sum_iff.mpr
  intro j
  apply (ae_map_iff (by fun_prop : Measurable fun E : ℝ => (j, E)).aemeasurable
    (measurableSet_lt (by fun_prop) measurable_snd)).mpr
  exact referenceMeasure_ae_above_edge j

theorem spinReferenceEnergy_ae_eq :
    spinReferenceEnergy =ᵐ[spinReferenceMeasure] (fun q => q.2) := by
  filter_upwards [spinReferenceMeasure_ae_above_edge] with q hq
  exact max_eq_right ((abs_nonneg _).trans hq.le)

theorem spinReferenceWeight_nonneg {a : ℝ} (ha : 2 ≤ a) :
    ∀ᵐ q ∂spinReferenceMeasure, 0 ≤ spinReferenceWeight a q := by
  filter_upwards [spinReferenceMeasure_ae_above_edge] with q hq
  exact vacuumLeading_nonneg a q.2 q.1 ha hq.le

private theorem realThermal_cast (a y e : ℝ) (j : ℤ) :
    Complex.exp (-2 * (Real.pi : ℂ) * (y : ℂ) * (e : ℂ)) * (vacuumLeading a e j : ℂ) =
      ((vacuumLeading a e j * Real.exp (-2 * Real.pi * y * e) : ℝ) : ℂ) := by
  push_cast
  rw [mul_comm]

private theorem integrable_realThermal {a y : ℝ} (ha : 2 ≤ a) (hy : 0 < y) (j : ℤ) :
    Integrable (fun e => vacuumLeading a e j * Real.exp (-2 * Real.pi * y * e))
      (referenceMeasure j) := by
  have h := (integrable_vacuumLeadingThermal ha hy j).re
  simpa only [realThermal_cast, RCLike.re_to_complex, Complex.ofReal_re] using h

private theorem summable_integral_realThermal {a y : ℝ} (ha : 2 ≤ a) (hy : 0 < y) :
    Summable (fun j : ℤ => ∫ e, vacuumLeading a e j * Real.exp (-2 * Real.pi * y * e)
      ∂referenceMeasure j) := by
  have hs := ((summable_fourier_spinImageKernel hy a).mapL Complex.reCLM).div_const (Real.sqrt y)
  apply hs.congr
  intro j
  rw [fourier_spinImageKernel_eq_reference ha hy]
  simp only [realThermal_cast, integral_complex_ofReal, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero, Complex.reCLM_apply]
  exact mul_div_cancel_left₀ _ (ne_of_gt (Real.sqrt_pos.2 hy))

private theorem realThermal_nonneg_ae {a y : ℝ} (ha : 2 ≤ a) (j : ℤ) :
    ∀ᵐ e ∂referenceMeasure j, 0 ≤ vacuumLeading a e j * Real.exp (-2 * Real.pi * y * e) := by
  filter_upwards [referenceMeasure_ae_above_edge j] with e he
  exact mul_nonneg (vacuumLeading_nonneg a e j ha he.le) (Real.exp_pos _).le

private theorem integrable_spinReferenceThermal_y {a y : ℝ} (ha : 2 ≤ a) (hy : 0 < y) :
    Integrable (fun q => spinReferenceWeight a q *
      Real.exp (-2 * Real.pi * y * spinReferenceEnergy q)) spinReferenceMeasure := by
  have hm : Measurable (fun q => spinReferenceWeight a q *
      Real.exp (-2 * Real.pi * y * spinReferenceEnergy q)) :=
    (measurable_spinReferenceWeight a).mul
      ((measurable_const.mul measurable_spinReferenceEnergy).exp)
  have heq (j : ℤ) : (fun e => spinReferenceWeight a (j, e) *
      Real.exp (-2 * Real.pi * y * spinReferenceEnergy (j, e))) =ᵐ[referenceMeasure j]
        (fun e => vacuumLeading a e j * Real.exp (-2 * Real.pi * y * e)) := by
    filter_upwards [referenceMeasure_ae_above_edge j] with e he
    simp only [spinReferenceWeight, spinReferenceEnergy,
      max_eq_right ((abs_nonneg _).trans he.le)]
  apply integrable_sum_measure
  · intro j
    apply (integrable_map_measure hm.aestronglyMeasurable
      (by fun_prop : Measurable fun E : ℝ => (j, E)).aemeasurable).mpr
    exact (integrable_realThermal ha hy j).congr (heq j).symm
  · apply (summable_integral_realThermal ha hy).congr
    intro j
    rw [integral_map (by fun_prop : Measurable fun E : ℝ => (j, E)).aemeasurable
      hm.norm.aestronglyMeasurable]
    apply integral_congr_ae
    filter_upwards [heq j, realThermal_nonneg_ae (y := y) ha j] with e he hn
    rw [he, Real.norm_of_nonneg hn]

/-- Every positive thermal moment of the actual integer-spin reference is finite. -/
theorem integrable_spinReferenceThermal {a β : ℝ} (ha : 2 ≤ a) (hβ : 0 < β) :
    Integrable (fun q => spinReferenceWeight a q * Real.exp (-β * spinReferenceEnergy q))
      spinReferenceMeasure := by
  have hy : 0 < β / (2 * Real.pi) := div_pos hβ (by positivity)
  convert integrable_spinReferenceThermal_y ha hy using 1
  ext q
  congr 2
  field_simp

/-- The positive real restriction of the genuine weighted Laplace transform is
exactly the spin sum used by Poisson summation. -/
theorem weightedComplexLaplace_spinReference_real {a y : ℝ} (ha : 2 ≤ a) (hy : 0 < y) :
    weightedComplexLaplace spinReferenceMeasure spinReferenceEnergy (spinReferenceWeight a)
      ((2 * Real.pi * y : ℝ) : ℂ) = integerSpinReferenceThermal a y := by
  let f : ℤ × ℝ → ℂ := fun q => (spinReferenceWeight a q : ℂ) *
    Complex.exp (-((2 * Real.pi * y : ℝ) : ℂ) * spinReferenceEnergy q)
  have hm : Measurable f := by
    exact (Complex.measurable_ofReal.comp (measurable_spinReferenceWeight a)).mul
      (Complex.measurable_exp.comp (measurable_const.mul
        (Complex.measurable_ofReal.comp measurable_spinReferenceEnergy)))
  have hf : Integrable f spinReferenceMeasure := by
    convert (integrable_spinReferenceThermal_y ha hy).ofReal using 1
    ext q
    dsimp [f]
    push_cast
    congr 2
    ring
  change (∫ q, f q ∂spinReferenceMeasure) = _
  unfold spinReferenceMeasure at hf ⊢
  rw [integral_sum_measure hf]
  unfold integerSpinReferenceThermal
  apply tsum_congr
  intro j
  rw [integral_map (by fun_prop : Measurable fun E : ℝ => (j, E)).aemeasurable
    hm.aestronglyMeasurable]
  apply integral_congr_ae
  filter_upwards [referenceMeasure_ae_above_edge j] with e he
  dsimp [f, spinReferenceEnergy, spinReferenceWeight]
  rw [max_eq_right ((abs_nonneg _).trans he.le), mul_comm]
  congr 2
  push_cast
  ring

/-- The physical integer-spin primary count with the specified smoothing kernel. -/
def integerSpinPrimarySmoothCount (φ : SmoothKernel) (a E : ℝ) : ℝ :=
  weightedSmoothCount φ spinReferenceMeasure spinReferenceEnergy (spinReferenceWeight a) E

/-- The complex thermal transform of that same primary reference distribution. -/
def integerSpinPrimaryComplexTransform (a : ℝ) (z : ℂ) : ℂ :=
  weightedComplexLaplace spinReferenceMeasure spinReferenceEnergy (spinReferenceWeight a) z

theorem analyticOnNhd_integerSpinPrimaryComplexTransform {a : ℝ} (ha : 2 ≤ a) :
    AnalyticOnNhd ℂ (integerSpinPrimaryComplexTransform a) {z : ℂ | 0 < z.re} :=
  analyticOnNhd_weightedComplexLaplace measurable_spinReferenceEnergy
    (measurable_spinReferenceWeight a)
    (Filter.Eventually.of_forall spinReferenceEnergy_nonneg)
    (fun _ hβ => integrable_spinReferenceThermal ha hβ)

theorem integerSpinPrimaryComplexTransform_real {a y : ℝ} (ha : 2 ≤ a) (hy : 0 < y) :
    integerSpinPrimaryComplexTransform a ((2 * Real.pi * y : ℝ) : ℂ) =
      integerSpinReferenceThermal a y :=
  weightedComplexLaplace_spinReference_real ha hy

theorem integerSpinPrimarySmoothCount_nonneg (φ : SmoothKernel) {a : ℝ}
    (ha : 2 ≤ a) (E : ℝ) : 0 ≤ integerSpinPrimarySmoothCount φ a E := by
  apply integral_nonneg_of_ae
  filter_upwards [spinReferenceWeight_nonneg ha] with q hq
  exact mul_nonneg hq (φ.nonneg _)

/-- The primary reference count has a genuine inverse-contour representation. -/
theorem integerSpinPrimarySmoothCount_eq_contour (φ : SmoothKernel) {a β : ℝ}
    (ha : 2 ≤ a) (hβ : 0 < β) (E : ℝ) :
    (integerSpinPrimarySmoothCount φ a E : ℂ) =
      (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ,
        Complex.exp (saddleContour β t * E) * complexKernelTransform φ (saddleContour β t) *
          integerSpinPrimaryComplexTransform a (saddleContour β t) :=
  weightedSmoothCount_eq_contour φ β E spinReferenceEnergy (spinReferenceWeight a)
    measurable_spinReferenceEnergy (measurable_spinReferenceWeight a)
    (integrable_spinReferenceThermal ha hβ)

end BTZEntropy
