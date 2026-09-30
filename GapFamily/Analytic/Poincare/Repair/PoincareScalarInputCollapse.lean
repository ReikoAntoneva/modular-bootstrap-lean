import GapFamily.Analytic.Poincare.Repair.PoincareLocalInverseInput

/-! A scalar signed input embedded in a finite spin family has the same actual
response and inverse as the single scalar input indexed by `Unit`.
-/

noncomputable section

namespace GapFamily.Analytic

open MeasureTheory Set
open scoped Classical BigOperators

/-- Zero input in every nonzero spin leaves exactly the scalar signed response. -/
theorem correctedSignedResponse_scalarInput_collapse
    (S : Finset ℤ) (h0 : (0 : ℤ) ∈ S) (ν : SignedMeasure ℝ) (j : ℤ) (e : ℝ) :
    correctedSignedResponse (fun J : S => if (J : ℤ) = 0 then ν else 0) Subtype.val j e =
      correctedSignedResponse (fun _ : Unit => ν) (fun _ => 0) j e := by
  simp only [correctedSignedResponse, Fintype.sum_unique]
  rw [Finset.sum_eq_single (⟨0, h0⟩ : S)]
  · simp
  · intro J _ hJ
    have hne : (J : ℤ) ≠ 0 := fun h => hJ (Subtype.ext h)
    simp [hne, correctedSignedRowResponse]
  · simp

/-- The physical L2 response is unchanged by embedding a scalar input among
the finitely many zero nonzero-spin inputs. -/
theorem correctedSignedResponseLp_scalarInput_collapse
    (S : Finset ℤ) (h0 : (0 : ℤ) ∈ S) (ν : SignedMeasure ℝ) (j : ℤ)
    (M B : ℝ) (hM : 0 ≤ M) (hB : 0 ≤ B)
    (hfinite : ∀ J : S,
      ∀ᵐ E ∂(if (J : ℤ) = 0 then ν else 0).variation, |(J : ℝ)| ≤ E ∧ E ≤ M)
    (hs : ∀ᵐ E ∂ν.variation, |(0 : ℝ)| ≤ E ∧ E ≤ M) :
    correctedSignedResponseLp (fun J : S => if (J : ℤ) = 0 then ν else 0)
        Subtype.val j M B hM hB hfinite =
      correctedSignedResponseLp (fun _ : Unit => ν) (fun _ => 0)
        j M B hM hB (fun _ => by simpa only [Int.cast_zero] using hs) := by
  apply Lp.ext
  filter_upwards [correctedSignedResponseLp_coeFn
      (fun J : S => if (J : ℤ) = 0 then ν else 0) Subtype.val j M B hM hB hfinite,
    correctedSignedResponseLp_coeFn (fun _ : Unit => ν) (fun _ => 0)
      j M B hM hB (fun _ => by simpa only [Int.cast_zero] using hs)] with e he hunit
  rw [he, hunit]
  exact correctedSignedResponse_scalarInput_collapse S h0 ν j e

/-- The full physical Hilbert response of the finite scalar embedding equals
the `Unit` source response on every chosen family of output spins. -/
theorem correctedSignedResponseHilbert_scalarInput_collapse
    {κ : Type*} [Fintype κ] (S : Finset ℤ) (h0 : (0 : ℤ) ∈ S)
    (ν : SignedMeasure ℝ) (j : κ → ℤ) (M B : ℝ) (hM : 0 ≤ M) (hB : 0 ≤ B)
    (hfinite : ∀ J : S,
      ∀ᵐ E ∂(if (J : ℤ) = 0 then ν else 0).variation, |(J : ℝ)| ≤ E ∧ E ≤ M)
    (hs : ∀ᵐ E ∂ν.variation, |(0 : ℝ)| ≤ E ∧ E ≤ M) :
    correctedSignedResponseHilbert (fun J : S => if (J : ℤ) = 0 then ν else 0)
        Subtype.val j M B hM hB hfinite =
      correctedSignedResponseHilbert (fun _ : Unit => ν) (fun _ => 0)
        j M B hM hB (fun _ => by simpa only [Int.cast_zero] using hs) := by
  unfold correctedSignedResponseHilbert
  congr 1
  funext k
  exact correctedSignedResponseLp_scalarInput_collapse S h0 ν (j k) M B hM hB hfinite hs

/-- The actual ordinary inverse measures agree exactly, independently of
whether the scalar source is indexed by a finite spin family or by `Unit`. -/
theorem correctedSignedInverseMeasure_scalarInput_collapse
    {κ : Type*} [Fintype κ] (S : Finset ℤ) (h0 : (0 : ℤ) ∈ S)
    (ν : SignedMeasure ℝ) (j : κ → ℤ) (M B : ℝ) (hM : 0 ≤ M) (hB : 0 ≤ B)
    (hfinite : ∀ J : S,
      ∀ᵐ E ∂(if (J : ℤ) = 0 then ν else 0).variation, |(J : ℝ)| ≤ E ∧ E ≤ M)
    (hs : ∀ᵐ E ∂ν.variation, |(0 : ℝ)| ≤ E ∧ E ≤ M)
    (hunit : IsUnit (correctedLowBandIdentityPlus j B)) (k : κ) :
    correctedSignedInverseMeasure (fun J : S => if (J : ℤ) = 0 then ν else 0)
        Subtype.val j M B hM hB hfinite hunit k =
      correctedSignedInverseMeasure (fun _ : Unit => ν) (fun _ => 0)
        j M B hM hB (fun _ => by simpa only [Int.cast_zero] using hs) hunit k := by
  ext s hset
  rw [correctedSignedInverseMeasure_apply _ _ _ _ _ _ _ _ _ _ _ hset,
    correctedSignedInverseMeasure_apply _ _ _ _ _ _ _ _ _ _ _ hset,
    correctedSignedResponseHilbert_scalarInput_collapse S h0 ν j M B hM hB hfinite hs]

/-- The literal local inverse of the actual high scalar anchor is the same
ordinary measure as the inverse of the single `Unit` scalar-band source. -/
theorem localInverseInput_localAnchorHighInput_collapse
    (S : Finset ℤ) (h0 : (0 : ℤ) ∈ S) (B : ℝ) (hB : 0 < B)
    (ζ : ℝ → ℝ) (hζ : ContinuousOn ζ (scalarAnchorBand B))
    (hunit : IsUnit (correctedLowBandIdentityPlus (fun j : S => (j : ℤ)) B)) (k : S) :
    localInverseInput S (localAnchorHighInput B hB ζ hζ) (3 * B) B
        (by positivity) hB.le
        (fun J _ => localAnchorHighInput_ae_physical B hB ζ hζ J) hunit k =
      correctedSignedInverseMeasure
        (fun _ : Unit => scalarAnchorBandMeasure B hB ζ hζ) (fun _ => 0)
        Subtype.val (3 * B) B (by positivity) hB.le
        (fun _ => by simpa only [Int.cast_zero] using
          scalarAnchorBandMeasure_ae_physical B hB ζ hζ) hunit k := by
  rw [localInverseInput_apply S _ (3 * B) B _ _ _ hunit k k.property]
  exact correctedSignedInverseMeasure_scalarInput_collapse S h0
    (scalarAnchorBandMeasure B hB ζ hζ) Subtype.val (3 * B) B (by positivity) hB.le
    (fun J => localAnchorHighInput_ae_physical B hB ζ hζ J)
    (scalarAnchorBandMeasure_ae_physical B hB ζ hζ) hunit k

end GapFamily.Analytic
