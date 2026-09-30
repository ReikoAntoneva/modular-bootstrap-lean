import GapFamily.Analytic.Poincare.Repair.PoincareExteriorReconstruction
import GapFamily.Analytic.Poincare.Repair.PoincareAnchorExteriorRegularity
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-! Ordinary regularity of the actual repaired exterior numerator. The kernel
response is continuous; the normalized scalar-band term retains its literal
indicator. All integrability statements use the actual physical row measure. -/
noncomputable section
namespace GapFamily.Analytic
open MeasureTheory Set Real

variable (ν : ℤ → SignedMeasure ℝ) (B : ℝ) (hB : 1 ≤ B)
  (hν : ∀ J ∈ lowBandSpinSet B, ∀ᵐ E ∂(ν J).variation,
    |(J : ℝ)| ≤ E ∧ E ≤ 3 * B)

include hν

/-- The actual numerator agrees almost everywhere with its ordinary
continuous-response and high-band-density formula. -/
theorem canonicalRepairExteriorNumerator_ae_eq (j : ℤ) :
    canonicalRepairExteriorNumerator ν B hB j =ᵐ[referenceMeasure j]
      (fun e => correctedSignedResponse (fun J : LowBandSpin B => ν J) Subtype.val j e -
        correctedSignedResponse (fun J : LowBandSpin B =>
          canonicalLocalInverseInput ν B hB hν J) Subtype.val j e +
        (finiteSignedThresholdMass (lowBandSpinSet B)
          (canonicalLocalInverseInput ν B hB hν) : ℂ) *
          (canonicalAnchorExteriorNumerator B hB j e : ℂ)) := by
  filter_upwards [referenceMeasure_ae_above_edge j] with e he
  exact canonicalRepairExteriorNumerator_eq ν B hB hν j e he.le

/-- Zero extension from the physical open row is strongly measurable as an
actual function, not merely as an almost-everywhere equivalence class. -/
theorem stronglyMeasurable_indicator_canonicalRepairExteriorNumerator (j : ℤ) :
    StronglyMeasurable ((Ioi |(j : ℝ)|).indicator
      (canonicalRepairExteriorNumerator ν B hB j)) := by
  have hfirst := (continuous_correctedSignedResponse (fun J : LowBandSpin B => ν J)
    (fun J : LowBandSpin B => (J : ℤ)) j (3 * B)
    (fun J => hν J J.property)).stronglyMeasurable
  have hsecond := (continuous_correctedSignedResponse (fun J : LowBandSpin B =>
    canonicalLocalInverseInput ν B hB hν J) (fun J : LowBandSpin B => (J : ℤ)) j (3 * B)
    (fun J => canonicalLocalInverseInput_physicalSupport ν B hB hν J)).stronglyMeasurable
  have hanchor := Complex.continuous_ofReal.comp_stronglyMeasurable
    (stronglyMeasurable_canonicalAnchorExteriorNumerator B hB j)
  have hp := (hfirst.sub hsecond).add (hanchor.const_mul
    (finiteSignedThresholdMass (lowBandSpinSet B) (canonicalLocalInverseInput ν B hB hν) : ℂ))
  convert hp.indicator (s := Ioi |(j : ℝ)|) measurableSet_Ioi using 1
  ext e
  by_cases he : e ∈ Ioi |(j : ℝ)|
  · simp only [indicator_of_mem he]
    exact canonicalRepairExteriorNumerator_eq ν B hB hν j e he.le
  · simp only [indicator_of_notMem he]

/-- The physical real density has an everywhere measurable zero extension. -/
theorem measurable_indicator_re_canonicalRepairExteriorNumerator (j : ℤ) :
    Measurable ((Ioi |(j : ℝ)|).indicator
      (fun e => (canonicalRepairExteriorNumerator ν B hB j e).re)) := by
  have h := Complex.measurable_re.comp
    (stronglyMeasurable_indicator_canonicalRepairExteriorNumerator ν B hB hν j).measurable
  change Measurable (fun e => if e ∈ Ioi |(j : ℝ)| then
    (canonicalRepairExteriorNumerator ν B hB j e).re else 0)
  simpa only [Function.comp_def, indicator, apply_ite, Complex.zero_re] using h

/-- The repaired numerator is an ordinary measurable function for the actual
reference measure, without discarding the direct scalar band density. -/
theorem aestronglyMeasurable_canonicalRepairExteriorNumerator (j : ℤ) :
    AEStronglyMeasurable (canonicalRepairExteriorNumerator ν B hB j) (referenceMeasure j) := by
  have hfirst := (continuous_correctedSignedResponse (fun J : LowBandSpin B => ν J)
    (fun J : LowBandSpin B => (J : ℤ)) j (3 * B)
    (fun J => hν J J.property)).stronglyMeasurable
  have hsecond := (continuous_correctedSignedResponse (fun J : LowBandSpin B =>
    canonicalLocalInverseInput ν B hB hν J) (fun J : LowBandSpin B => (J : ℤ)) j (3 * B)
    (fun J => canonicalLocalInverseInput_physicalSupport ν B hB hν J)).stronglyMeasurable
  have hanchor := Complex.continuous_ofReal.comp_stronglyMeasurable
    (stronglyMeasurable_canonicalAnchorExteriorNumerator B hB j)
  have hp := (hfirst.sub hsecond).add (hanchor.const_mul
    (finiteSignedThresholdMass (lowBandSpinSet B) (canonicalLocalInverseInput ν B hB hν) : ℂ))
  exact hp.aestronglyMeasurable.congr (canonicalRepairExteriorNumerator_ae_eq ν B hB hν j).symm

/-- Ordinary finite-band integrability holds up to the physical threshold. -/
theorem integrableOn_canonicalRepairExteriorNumerator (j : ℤ) (D : ℝ) :
    IntegrableOn (canonicalRepairExteriorNumerator ν B hB j)
      (Ioo |(j : ℝ)| D) (referenceMeasure j) := by
  have hfirst := correctedSignedResponse_integrable_lowBand (fun J : LowBandSpin B => ν J)
    (fun J : LowBandSpin B => (J : ℤ)) j (3 * B) D (fun J => hν J J.property)
  have hsecond := correctedSignedResponse_integrable_lowBand (fun J : LowBandSpin B =>
    canonicalLocalInverseInput ν B hB hν J) (fun J : LowBandSpin B => (J : ℤ)) j (3 * B) D
    (fun J => canonicalLocalInverseInput_physicalSupport ν B hB hν J)
  have hanchor : IntegrableOn (fun e => (canonicalAnchorExteriorNumerator B hB j e : ℂ))
      (Ioo |(j : ℝ)| D) (referenceMeasure j) :=
    (integrableOn_canonicalAnchorExteriorNumerator B hB j D).ofReal
  have hp := (hfirst.sub hsecond).add (hanchor.const_mul
    (finiteSignedThresholdMass (lowBandSpinSet B) (canonicalLocalInverseInput ν B hB hν) : ℂ))
  exact hp.congr (canonicalRepairExteriorNumerator_ae_eq ν B hB hν j).symm.restrict

/-- The real density used in spectral output has the same ordinary local mass. -/
theorem integrableOn_re_canonicalRepairExteriorNumerator (j : ℤ) (D : ℝ) :
    IntegrableOn (fun e => (canonicalRepairExteriorNumerator ν B hB j e).re)
      (Ioo |(j : ℝ)| D) (referenceMeasure j) := by
  simpa only [RCLike.re_eq_complex_re] using
    (integrableOn_canonicalRepairExteriorNumerator ν B hB hν j D).re

/-- Every bounded physical cell inherits the actual real density's integrability. -/
theorem integrableOn_re_canonicalRepairExteriorNumerator_of_subset
    (j : ℤ) (D : ℝ) {s : Set ℝ} (hs : s ⊆ Ioo |(j : ℝ)| D) :
    IntegrableOn (fun e => (canonicalRepairExteriorNumerator ν B hB j e).re)
      s (referenceMeasure j) :=
  (integrableOn_re_canonicalRepairExteriorNumerator ν B hB hν j D).mono_set hs

/-- The density is locally integrable on the complete physical open row. -/
theorem locallyIntegrableOn_re_canonicalRepairExteriorNumerator (j : ℤ) :
    LocallyIntegrableOn (fun e => (canonicalRepairExteriorNumerator ν B hB j e).re)
      (Ioi |(j : ℝ)|) (referenceMeasure j) := by
  intro e he
  refine ⟨Ioo |(j : ℝ)| (e + 1), ?_,
    integrableOn_re_canonicalRepairExteriorNumerator ν B hB hν j (e + 1)⟩
  exact mem_nhdsWithin_of_mem_nhds (Ioo_mem_nhds he (by linarith))

/-- On physical open rows only the retained scalar-band endpoints can obstruct
continuity of the actual repaired numerator. -/
theorem continuousAt_canonicalRepairExteriorNumerator
    (j : ℤ) (e : ℝ) (he : |(j : ℝ)| < e) (he2 : e ≠ 2 * B) (he3 : e ≠ 3 * B) :
    ContinuousAt (canonicalRepairExteriorNumerator ν B hB j) e := by
  have hfirst := continuous_correctedSignedResponse (fun J : LowBandSpin B => ν J)
    (fun J : LowBandSpin B => (J : ℤ)) j (3 * B) (fun J => hν J J.property)
  have hsecond := continuous_correctedSignedResponse (fun J : LowBandSpin B =>
    canonicalLocalInverseInput ν B hB hν J) (fun J : LowBandSpin B => (J : ℤ)) j (3 * B)
    (fun J => canonicalLocalInverseInput_physicalSupport ν B hB hν J)
  have hanchor := continuousAt_canonicalAnchorExteriorNumerator B hB j e he2 he3
  have hanchorC : ContinuousAt (fun x => (canonicalAnchorExteriorNumerator B hB j x : ℂ)) e :=
    Complex.continuous_ofReal.continuousAt.comp hanchor
  have hp := ((hfirst.continuousAt (x := e)).sub (hsecond.continuousAt (x := e))).add
    (hanchorC.const_mul
      (finiteSignedThresholdMass (lowBandSpinSet B) (canonicalLocalInverseInput ν B hB hν) : ℂ))
  apply hp.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds he] with x hx
  exact canonicalRepairExteriorNumerator_eq ν B hB hν j x hx.le

omit hν

/-- Finite actual repair steps remain ordinarily integrable on every physical
finite cell, as required by the iterative density construction. -/
theorem integrableOn_finset_re_canonicalRepairExteriorNumerator
    {κ : Type*} (s : Finset κ) (ν : κ → ℤ → SignedMeasure ℝ)
    (B : κ → ℝ) (hB : ∀ k, 1 ≤ B k)
    (hν : ∀ k, ∀ J ∈ lowBandSpinSet (B k), ∀ᵐ E ∂(ν k J).variation,
      |(J : ℝ)| ≤ E ∧ E ≤ 3 * B k) (j : ℤ) (D : ℝ) :
    IntegrableOn (fun e => ∑ k ∈ s, (canonicalRepairExteriorNumerator (ν k) (B k) (hB k) j e).re)
      (Ioo |(j : ℝ)| D) (referenceMeasure j) :=
  integrable_finsetSum s fun k _ =>
    integrableOn_re_canonicalRepairExteriorNumerator (ν k) (B k) (hB k) (hν k) j D

end GapFamily.Analytic
