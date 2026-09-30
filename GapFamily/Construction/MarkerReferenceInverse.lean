import GapFamily.Construction.MarkerReferenceRhs
import GapFamily.Analytic.Kernel.FullKernelInverseCancellation

/-!
# The actual marker reference inverse

Applying the actual low-band inverse to the negative vacuum-plus-marker source
gives ordinary signed measures. Their continuum response cancels that source
as a measure, including at the physical endpoints.
-/

noncomputable section

open MeasureTheory Set

namespace GapFamily.Construction

open Analytic

variable {ι : Type*} [Fintype ι]

/-- The actual Hilbert inverse of the vacuum-plus-marker source. -/
def markerReferenceInverse (J : ι → ℤ) (a b : ℝ) (ha : 2 ≤ a) (hb : 0 ≤ b) :
    LowBandHilbert J b :=
  Ring.inverse (correctedLowBandIdentityPlus J b) (markerReferenceRhsHilbert J a b ha hb)

theorem markerReferenceInverse_real (J : ι → ℤ) (a b : ℝ) (ha : 2 ≤ a) (hb : 0 ≤ b)
    (hunit : IsUnit (correctedLowBandIdentityPlus J b)) :
    LowBandIsReal J b (markerReferenceInverse J a b ha hb) :=
  (markerReferenceRhsHilbert_real J a b ha hb).correctedLowBandInverse J b hunit

theorem markerReferenceInverse_integrable (J : ι → ℤ) (a b : ℝ)
    (ha : 2 ≤ a) (hb : 0 ≤ b) (hunit : IsUnit (correctedLowBandIdentityPlus J b)) (i : ι) :
    Integrable (markerReferenceInverse J a b ha hb i)
      ((referenceMeasure (J i)).restrict (Ioo |(J i : ℝ)| b)) :=
  correctedLowBandInverse_integrable J b hb hunit _
    (markerReferenceRhsHilbert_integrable J a b ha hb) i

/-- Ordinary signed density measures of the actual inverse. -/
def markerReferenceInverseMeasure (J : ι → ℤ) (a b : ℝ) (ha : 2 ≤ a) (hb : 0 ≤ b)
    (hunit : IsUnit (correctedLowBandIdentityPlus J b)) (i : ι) : SignedMeasure ℝ :=
  correctedLowBandInverseSignedMeasure J b hb hunit (markerReferenceRhsHilbert J a b ha hb)
    (markerReferenceRhsHilbert_integrable J a b ha hb) i

theorem markerReferenceInverseMeasure_apply (J : ι → ℤ) (a b : ℝ)
    (ha : 2 ≤ a) (hb : 0 ≤ b) (hunit : IsUnit (correctedLowBandIdentityPlus J b))
    (i : ι) (s : Set ℝ) (hs : MeasurableSet s) :
    markerReferenceInverseMeasure J a b ha hb hunit i s =
      ∫ e in s, (markerReferenceInverse J a b ha hb i e).re
        ∂(referenceMeasure (J i)).restrict (Ioo |(J i : ℝ)| b) :=
  correctedLowBandInverseSignedMeasure_apply J b hb hunit _ _ i s hs

@[simp] theorem markerReferenceInverseMeasure_singleton (J : ι → ℤ) (a b : ℝ)
    (ha : 2 ≤ a) (hb : 0 ≤ b) (hunit : IsUnit (correctedLowBandIdentityPlus J b))
    (i : ι) (e : ℝ) : markerReferenceInverseMeasure J a b ha hb hunit i {e} = 0 :=
  correctedLowBandInverseSignedMeasure_singleton J b hb hunit _ _ i e

theorem markerReferenceInverseMeasure_ae_mem (J : ι → ℤ) (a b : ℝ)
    (ha : 2 ≤ a) (hb : 0 ≤ b) (hunit : IsUnit (correctedLowBandIdentityPlus J b)) (i : ι) :
    ∀ᵐ e ∂(markerReferenceInverseMeasure J a b ha hb hunit i).variation,
      e ∈ Ioo |(J i : ℝ)| b :=
  correctedLowBandInverseSignedMeasure_ae_mem J b hb hunit _ _ i

theorem markerReferenceInverseMeasure_ae_physical (J : ι → ℤ) (a b : ℝ)
    (ha : 2 ≤ a) (hb : 0 ≤ b) (hunit : IsUnit (correctedLowBandIdentityPlus J b)) (i : ι) :
    ∀ᵐ e ∂(markerReferenceInverseMeasure J a b ha hb hunit i).variation,
      |(J i : ℝ)| ≤ e ∧ e ≤ b :=
  correctedLowBandInverseSignedMeasure_ae_physical J b hb hunit _ _ i

theorem markerReferenceInverseMeasure_restrict_self (J : ι → ℤ) (a b : ℝ)
    (ha : 2 ≤ a) (hb : 0 ≤ b) (hunit : IsUnit (correctedLowBandIdentityPlus J b)) (i : ι) :
    (markerReferenceInverseMeasure J a b ha hb hunit i).restrict (Ioo |(J i : ℝ)| b) =
      markerReferenceInverseMeasure J a b ha hb hunit i := by
  apply VectorMeasure.ext
  intro s hs
  rw [VectorMeasure.restrict_apply _ measurableSet_Ioo hs,
    markerReferenceInverseMeasure_apply _ _ _ _ _ _ _ _ (hs.inter measurableSet_Ioo),
    markerReferenceInverseMeasure_apply _ _ _ _ _ _ _ _ hs,
    Measure.restrict_restrict (hs.inter measurableSet_Ioo), Measure.restrict_restrict hs]
  simp only [inter_assoc, inter_self]

theorem markerReferenceInverseMeasure_totalVariation (J : ι → ℤ) (a b : ℝ)
    (ha : 2 ≤ a) (hb : 0 ≤ b) (hunit : IsUnit (correctedLowBandIdentityPlus J b)) (i : ι) :
    (markerReferenceInverseMeasure J a b ha hb hunit i).variation.real univ =
      ∫ e, ‖markerReferenceInverse J a b ha hb i e‖
        ∂(referenceMeasure (J i)).restrict (Ioo |(J i : ℝ)| b) :=
  correctedLowBandInverseSignedMeasure_totalVariation J b hb hunit _ _
    (markerReferenceRhsHilbert_real J a b ha hb) i

theorem correctedSignedResponse_markerReferenceInverseMeasure
    (J : ι → ℤ) (a b : ℝ) (ha : 2 ≤ a) (hb : 0 ≤ b)
    (hunit : IsUnit (correctedLowBandIdentityPlus J b)) (j : ℤ) (e : ℝ) :
    correctedSignedResponse (markerReferenceInverseMeasure J a b ha hb hunit) J j e =
      correctedKernelResponse J b (markerReferenceInverse J a b ha hb) j e :=
  correctedSignedResponse_inverseSignedMeasure J b hb hunit _ _
    (markerReferenceRhsHilbert_real J a b ha hb) j e

/-- Actual inverse density plus its actual signed response cancels vacuum and marker. -/
theorem markerReferenceInverse_cancel_ae (J : ι → ℤ) (a b : ℝ)
    (ha : 2 ≤ a) (hb : 0 ≤ b) (hunit : IsUnit (correctedLowBandIdentityPlus J b)) (i : ι) :
    ∀ᵐ e ∂(referenceMeasure (J i)).restrict (Ioo |(J i : ℝ)| b),
      vacuumFullKernel a e (J i) + correctedKernel (J i) 0 e b +
        markerReferenceInverse J a b ha hb i e +
        correctedSignedResponse (markerReferenceInverseMeasure J a b ha hb hunit) J (J i) e = 0 := by
  filter_upwards [correctedLowBandInverse_coeFn_eq_sub J b hunit
      (markerReferenceRhsHilbert J a b ha hb) i,
    correctedLowBandOperator_coeFn J b hb (markerReferenceInverse J a b ha hb) i,
    markerReferenceRhsHilbert_coeFn J a b ha hb i] with e hinv hkernel hsource
  change markerReferenceInverse J a b ha hb i e =
    markerReferenceRhsHilbert J a b ha hb i e -
      correctedLowBandOperator J b (markerReferenceInverse J a b ha hb) i e at hinv
  rw [hkernel, hsource] at hinv
  rw [correctedSignedResponse_markerReferenceInverseMeasure, hinv, markerReferenceRhs]
  ring

/-- The ordinary density measure of the negative vacuum-plus-marker source. -/
def markerReferenceSourceMeasure (a b : ℝ) (j : ℤ) : SignedMeasure ℝ :=
  ((referenceMeasure j).restrict (Ioo |(j : ℝ)| b)).withDensityᵥ
    (fun e => (markerReferenceRhs a b j e).re)

theorem markerReferenceSourceMeasure_apply (a b : ℝ) (j : ℤ)
    (ha : 2 ≤ a) (hb : 0 ≤ b) (s : Set ℝ) (hs : MeasurableSet s) :
    markerReferenceSourceMeasure a b j s =
      ∫ e in s, (markerReferenceRhs a b j e).re
        ∂(referenceMeasure j).restrict (Ioo |(j : ℝ)| b) :=
  withDensityᵥ_apply (markerReferenceRhs_integrable a b j ha hb).re hs

/-- Exact ordinary signed-measure identity for the inverse and its induced continuum. -/
theorem markerReferenceInverseMeasure_add_output (J : ι → ℤ) (a b : ℝ)
    (ha : 2 ≤ a) (hb : 0 ≤ b) (hunit : IsUnit (correctedLowBandIdentityPlus J b)) (i : ι) :
    markerReferenceInverseMeasure J a b ha hb hunit i +
      correctedSignedOutputMeasure (markerReferenceInverseMeasure J a b ha hb hunit)
        J (J i) b b (markerReferenceInverseMeasure_ae_physical J a b ha hb hunit) =
      markerReferenceSourceMeasure a b (J i) := by
  apply VectorMeasure.ext
  intro s hs
  change markerReferenceInverseMeasure J a b ha hb hunit i s +
      correctedSignedOutputMeasure (markerReferenceInverseMeasure J a b ha hb hunit)
        J (J i) b b (markerReferenceInverseMeasure_ae_physical J a b ha hb hunit) s = _
  rw [correctedSignedOutputMeasure_apply _ _ _ _ _ _ _ hs]
  simp_rw [correctedSignedResponse_markerReferenceInverseMeasure]
  rw [markerReferenceInverseMeasure,
    correctedLowBandInverseSignedMeasure_apply_eq_sub J b hb hunit _ _ i s hs]
  dsimp only [markerReferenceInverse]
  rw [sub_add_cancel, markerReferenceSourceMeasure_apply a b (J i) ha hb s hs]
  apply integral_congr_ae
  filter_upwards [(markerReferenceRhsHilbert_coeFn J a b ha hb i).restrict] with e he
  exact congrArg Complex.re he

end GapFamily.Construction
