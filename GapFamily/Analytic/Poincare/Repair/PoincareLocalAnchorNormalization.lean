import GapFamily.Analytic.Poincare.Repair.PoincareLocalInverseInput
import GapFamily.Analytic.Foundation.FiniteSeedThreshold
import GapFamily.Analytic.Kernel.FullKernelScalarAnchorNonvanishing
import GapFamily.Analytic.Kernel.FullKernelScalarAnchorPairing
import GapFamily.Analytic.Poincare.Repair.PoincareScalarInputCollapse

/-! Exact threshold normalization of the actual local scalar anchor. Its finite
scalar input is identified with the ordinary single-row input of the scalar
inverse response, and the actual normalized high-band pairing has value one.
-/
noncomputable section
namespace GapFamily.Analytic
open Set MeasureTheory
open scoped Classical BigOperators

/-- The literal scalar high input has threshold mass minus its ordinary signed mass. -/
theorem finiteSignedThresholdMass_localAnchorHighInput
    (S : Finset ℤ) (h0 : 0 ∈ S) (B : ℝ) (hB : 0 < B) (ζ : ℝ → ℝ)
    (hζ : ContinuousOn ζ (scalarAnchorBand B)) :
    finiteSignedThresholdMass S (localAnchorHighInput B hB ζ hζ) =
      -(scalarAnchorBandMeasure B hB ζ hζ univ) := by
  have he (J : ℤ) : localAnchorHighInput B hB ζ hζ J univ =
      if J = 0 then scalarAnchorBandMeasure B hB ζ hζ univ else 0 := by
    by_cases hJ : J = 0 <;> simp [localAnchorHighInput, hJ]
  simp_rw [finiteSignedThresholdMass, he, mul_ite, mul_zero]
  simp [h0]

/-- The actual integer-indexed inverse threshold mass is exactly its native
finite row sum, with no missing or duplicated scalar row. -/
theorem finiteSignedThresholdMass_localInverseInput
    (S : Finset ℤ) (ν : ℤ → SignedMeasure ℝ) (M B : ℝ)
    (hM : 0 ≤ M) (hB : 0 ≤ B)
    (hs : ∀ J ∈ S, ∀ᵐ E ∂(ν J).variation, |(J : ℝ)| ≤ E ∧ E ≤ M)
    (hunit : IsUnit (correctedLowBandIdentityPlus (fun j : S => (j : ℤ)) B)) :
    finiteSignedThresholdMass S (localInverseInput S ν M B hM hB hs hunit) =
      ∑ i : S, (PoincareScalarFourier.scalarThresholdCoefficient (i : ℤ)).re *
        correctedSignedInverseMeasure (fun J : S => ν J) Subtype.val Subtype.val M B hM hB
          (fun J => hs J J.property) hunit i univ := by
  rw [finiteSignedThresholdMass, ← Finset.sum_coe_sort S]
  apply Finset.sum_congr rfl
  intro i hi
  rw [localInverseInput_apply S ν M B hM hB hs hunit i i.property]

/-- The actual anchor threshold is its high-band signed mass minus the actual
finite inverse masses. This identity precedes the analytic pairing computation. -/
theorem finiteSignedThresholdMass_localAnchorInput_eq_native
    (S : Finset ℤ) (h0 : 0 ∈ S) (B : ℝ) (hB : 0 < B) (ζ : ℝ → ℝ)
    (hζ : ContinuousOn ζ (scalarAnchorBand B))
    (hunit : IsUnit (correctedLowBandIdentityPlus (fun j : S => (j : ℤ)) B)) :
    finiteSignedThresholdMass S (localAnchorInput S B hB ζ hζ hunit) =
      -(scalarAnchorBandMeasure B hB ζ hζ univ) -
      ∑ i : S, (PoincareScalarFourier.scalarThresholdCoefficient (i : ℤ)).re *
        correctedSignedInverseMeasure (fun J : S => localAnchorHighInput B hB ζ hζ J)
          Subtype.val Subtype.val (3 * B) B (by positivity) hB.le
          (fun J => localAnchorHighInput_ae_physical B hB ζ hζ J) hunit i univ := by
  rw [localAnchorInput, finiteSignedThresholdMass_sub,
    finiteSignedThresholdMass_localAnchorHighInput S h0 B hB ζ hζ,
    finiteSignedThresholdMass_localInverseInput]

/-- The literal finite anchor threshold is the ordinary pairing with the
actual scalar inverse response. Scalar input embedded in the finite spin set
is identified with the single scalar input used by the pairing theorem. -/
theorem finiteSignedThresholdMass_localAnchorInput_eq_pairing
    (S : Finset ℤ) (h0 : 0 ∈ S) (B : ℝ) (hB : 0 < B) (ζ : ℝ → ℝ)
    (hζ : ContinuousOn ζ (scalarAnchorBand B))
    (hunit : IsUnit (correctedLowBandIdentityPlus (fun j : S => (j : ℤ)) B)) :
    finiteSignedThresholdMass S (localAnchorInput S B hB ζ hζ hunit) =
      ∫ᵛ E, scalarAnchorResponsePhysical (fun j : S => (j : ℤ)) B hB.le E
        ∂<•scalarAnchorBandMeasure B hB ζ hζ := by
  rw [finiteSignedThresholdMass_localAnchorInput_eq_native S h0 B hB ζ hζ hunit]
  have hc (i : S) :
      correctedSignedInverseMeasure (fun J : S => localAnchorHighInput B hB ζ hζ J)
        Subtype.val Subtype.val (3 * B) B (by positivity) hB.le
        (fun J => localAnchorHighInput_ae_physical B hB ζ hζ J) hunit i =
      correctedSignedInverseMeasure (fun _ : Unit => scalarAnchorBandMeasure B hB ζ hζ)
        (fun _ => 0) Subtype.val (3 * B) B (by positivity) hB.le
        (fun _ => by simpa only [Int.cast_zero] using
          scalarAnchorBandMeasure_ae_physical B hB ζ hζ) hunit i := by
    exact correctedSignedInverseMeasure_scalarInput_collapse S h0
      (scalarAnchorBandMeasure B hB ζ hζ) Subtype.val (3 * B) B (by positivity) hB.le
      (fun J => localAnchorHighInput_ae_physical B hB ζ hζ J)
      (scalarAnchorBandMeasure_ae_physical B hB ζ hζ) hunit i
  simp_rw [hc]
  exact scalarAnchorResponsePhysical_signedIntegral Subtype.val B hB
    (scalarAnchorBandMeasure B hB ζ hζ) (3 * B) (by positivity)
    (scalarAnchorBandMeasure_ae_physical B hB ζ hζ) hunit

/-- The actual scalar inverse response gives threshold mass exactly one for
the actual local anchor. Its normalization is proved positive by nonvanishing,
so no anchor-normalization premise remains. -/
theorem finiteSignedThresholdMass_localAnchorInput_actual
    (S : Finset ℤ) (h0 : 0 ∈ S) (B : ℝ) (hB : 0 < B)
    (hunit : IsUnit (correctedLowBandIdentityPlus (fun j : S => (j : ℤ)) B)) :
    finiteSignedThresholdMass S
      (localAnchorInput S B hB
        (scalarAnchorResponsePhysical (fun j : S => (j : ℤ)) B hB.le)
        (continuous_scalarAnchorResponsePhysical (fun j : S => (j : ℤ)) B hB.le).continuousOn
        hunit) = 1 := by
  rw [finiteSignedThresholdMass_localAnchorInput_eq_pairing S h0 B hB]
  exact (scalarAnchorBandMeasure_pairing B hB
    (scalarAnchorResponsePhysical (fun j : S => (j : ℤ)) B hB.le)
    (continuous_scalarAnchorResponsePhysical (fun j : S => (j : ℤ)) B hB.le).continuousOn
    (scalarAnchorSquareMass_actual_pos (fun j : S => (j : ℤ)) B hB hunit)).2

end GapFamily.Analytic
