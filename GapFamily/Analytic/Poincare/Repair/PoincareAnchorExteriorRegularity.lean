import GapFamily.Analytic.Poincare.Repair.PoincareAnchorExteriorOutput
import GapFamily.Analytic.Kernel.FullKernelSignedResponseContinuity

/-! Ordinary regularity of the actual anchor numerator. Its scalar high-band
indicator is retained, so continuity is asserted away from the two genuine
band endpoints. Ordinary local integrability includes the scalar threshold. -/
noncomputable section
namespace GapFamily.Analytic
open MeasureTheory Set Real

/-- The actual zero-extended scalar numerator is a measurable ordinary function. -/
theorem stronglyMeasurable_actualScalarAnchorNumerator
    {ι : Type*} [Fintype ι] (J : ι → ℤ) (B : ℝ) (hB : 0 ≤ B) :
    StronglyMeasurable (scalarAnchorNumerator B (scalarAnchorResponsePhysical J B hB)) := by
  unfold scalarAnchorNumerator scalarAnchorBandDensity
  exact ((continuous_scalarAnchorResponsePhysical J B hB).div_const _).stronglyMeasurable.indicator
    (measurableSet_scalarAnchorBand B)

/-- The two closed-band endpoints are the only possible indicator discontinuities. -/
theorem continuousAt_actualScalarAnchorNumerator
    {ι : Type*} [Fintype ι] (J : ι → ℤ) (B : ℝ) (hB : 0 ≤ B)
    (e : ℝ) (he2 : e ≠ 2 * B) (he3 : e ≠ 3 * B) :
    ContinuousAt (scalarAnchorNumerator B (scalarAnchorResponsePhysical J B hB)) e := by
  unfold scalarAnchorNumerator
  apply (show Continuous (scalarAnchorBandDensity B (scalarAnchorResponsePhysical J B hB)) from
    (continuous_scalarAnchorResponsePhysical J B hB).div_const _).continuousOn.continuousAt_indicator
  simpa only [scalarAnchorBand, frontier_Icc (by linarith : 2 * B ≤ 3 * B),
    mem_insert_iff, mem_singleton_iff, not_or] using And.intro he2 he3

/-- The complete actual exterior anchor is globally strongly measurable. -/
theorem stronglyMeasurable_canonicalAnchorExteriorNumerator (B : ℝ) (hB : 1 ≤ B) (j : ℤ) :
    StronglyMeasurable (canonicalAnchorExteriorNumerator B hB j) := by
  unfold canonicalAnchorExteriorNumerator
  have hresp := (Complex.continuous_re.comp (continuous_correctedSignedResponse
    (fun J : lowBandSpinSet B => canonicalLocalAnchorInput B hB J)
    (fun J : lowBandSpinSet B => (J : ℤ)) j (3 * B)
    (fun J => canonicalLocalAnchorInput_physicalSupport B hB J))).stronglyMeasurable
  by_cases hj : j = 0
  · simpa only [ite_eq_left hj, Pi.add_def, Function.comp_def] using!
      (stronglyMeasurable_actualScalarAnchorNumerator
        (fun J : lowBandSpinSet B => (J : ℤ)) B (zero_le_one.trans hB)).add hresp
  · simpa only [ite_eq_right hj, zero_add, Function.comp_def] using hresp

/-- The actual numerator is continuous away from the retained band endpoints. -/
theorem continuousAt_canonicalAnchorExteriorNumerator (B : ℝ) (hB : 1 ≤ B)
    (j : ℤ) (e : ℝ) (he2 : e ≠ 2 * B) (he3 : e ≠ 3 * B) :
    ContinuousAt (canonicalAnchorExteriorNumerator B hB j) e := by
  unfold canonicalAnchorExteriorNumerator
  have hresp := (Complex.continuous_re.comp (continuous_correctedSignedResponse
    (fun J : lowBandSpinSet B => canonicalLocalAnchorInput B hB J)
    (fun J : lowBandSpinSet B => (J : ℤ)) j (3 * B)
    (fun J => canonicalLocalAnchorInput_physicalSupport B hB J))).continuousAt (x := e)
  by_cases hj : j = 0
  · simpa only [ite_eq_left hj, Pi.add_def, Function.comp_def] using!
      (continuousAt_actualScalarAnchorNumerator
        (fun J : lowBandSpinSet B => (J : ℤ)) B (zero_le_one.trans hB) e he2 he3).add hresp
  · simpa only [ite_eq_right hj, zero_add, Function.comp_def] using hresp

/-- On every finite physical row segment the actual anchor has ordinary mass,
including the scalar row with its infinite total reference mass near zero. -/
theorem integrableOn_canonicalAnchorExteriorNumerator (B : ℝ) (hB : 1 ≤ B)
    (j : ℤ) (D : ℝ) :
    IntegrableOn (canonicalAnchorExteriorNumerator B hB j)
      (Ioo |(j : ℝ)| D) (referenceMeasure j) := by
  have hresp := (correctedSignedResponse_integrable_lowBand
    (fun J : lowBandSpinSet B => canonicalLocalAnchorInput B hB J)
    (fun J : lowBandSpinSet B => (J : ℤ)) j (3 * B) D
    (fun J => canonicalLocalAnchorInput_physicalSupport B hB J)).re
  change Integrable (fun e => (if j = 0 then scalarAnchorNumerator B
    (scalarAnchorResponsePhysical (fun J : lowBandSpinSet B => (J : ℤ)) B
      (zero_le_one.trans hB)) e else 0) +
    (correctedSignedResponse (fun J : lowBandSpinSet B => canonicalLocalAnchorInput B hB J)
      Subtype.val j e).re) ((referenceMeasure j).restrict (Ioo |(j : ℝ)| D))
  by_cases hj : j = 0
  · subst j
    have hhigh := (scalarAnchorNumerator_integrable B (by linarith)
      (scalarAnchorResponsePhysical (fun J : lowBandSpinSet B => (J : ℤ)) B
        (zero_le_one.trans hB))
      (continuous_scalarAnchorResponsePhysical _ B (zero_le_one.trans hB)).continuousOn).integrableOn
        (s := Ioo |((0 : ℤ) : ℝ)| D)
    simpa only [IntegrableOn, ite_true, Pi.add_def, RCLike.re_eq_complex_re] using! hhigh.add hresp
  · simpa only [ite_eq_right hj, zero_add, RCLike.re_eq_complex_re] using hresp

/-- Every physical cell inside a finite row segment inherits ordinary integrability. -/
theorem integrableOn_canonicalAnchorExteriorNumerator_of_subset (B : ℝ) (hB : 1 ≤ B)
    (j : ℤ) (D : ℝ) {s : Set ℝ} (hs : s ⊆ Ioo |(j : ℝ)| D) :
    IntegrableOn (canonicalAnchorExteriorNumerator B hB j) s (referenceMeasure j) :=
  (integrableOn_canonicalAnchorExteriorNumerator B hB j D).mono_set hs

end GapFamily.Analytic
