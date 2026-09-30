import GapFamily.Analytic.Poincare.Fourier.PoincareSignedSeedLinearity
import GapFamily.Analytic.Kernel.FullKernelSmoothingSignedMeasure

/-! The actual ordinary unweighted low-band output of a finite signed seed.
This signed measure retains the direct input atoms and the proved integrable
corrected kernel response, with no scalar-threshold or edge atom in the open band.
-/
noncomputable section
namespace GapFamily.Analytic
open Set MeasureTheory
open scoped Classical BigOperators

/-- Finite response addition is literal addition of the actual kernel integrals. -/
theorem correctedSignedResponse_add {ι : Type*} [Fintype ι]
    (ν μ : ι → SignedMeasure ℝ) (J : ι → ℤ) (j : ℤ) (M : ℝ)
    (hν : ∀ i, ∀ᵐ E ∂(ν i).variation, |(J i : ℝ)| ≤ E ∧ E ≤ M)
    (hμ : ∀ i, ∀ᵐ E ∂(μ i).variation, |(J i : ℝ)| ≤ E ∧ E ≤ M) (e : ℝ) :
    correctedSignedResponse (fun i => ν i + μ i) J j e =
      correctedSignedResponse ν J j e + correctedSignedResponse μ J j e := by
  simp only [correctedSignedResponse, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ =>
    correctedSignedRowResponse_add (ν i) (μ i) (J i) j M (hν i) (hμ i) e

/-- Finite response subtraction is literal subtraction of the actual kernel integrals. -/
theorem correctedSignedResponse_sub {ι : Type*} [Fintype ι]
    (ν μ : ι → SignedMeasure ℝ) (J : ι → ℤ) (j : ℤ) (M : ℝ)
    (hν : ∀ i, ∀ᵐ E ∂(ν i).variation, |(J i : ℝ)| ≤ E ∧ E ≤ M)
    (hμ : ∀ i, ∀ᵐ E ∂(μ i).variation, |(J i : ℝ)| ≤ E ∧ E ≤ M) (e : ℝ) :
    correctedSignedResponse (fun i => ν i - μ i) J j e =
      correctedSignedResponse ν J j e - correctedSignedResponse μ J j e := by
  simp only [correctedSignedResponse, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ =>
    correctedSignedRowResponse_sub (ν i) (μ i) (J i) j M (hν i) (hμ i) e

/-- Real scaling commutes with the actual finite corrected response. -/
theorem correctedSignedResponse_smul {ι : Type*} [Fintype ι]
    (ν : ι → SignedMeasure ℝ) (c : ℝ) (J : ι → ℤ) (j : ℤ) (e : ℝ) :
    correctedSignedResponse (fun i => c • ν i) J j e =
      c • correctedSignedResponse ν J j e := by
  simp only [correctedSignedResponse, correctedSignedRowResponse_smul, Finset.smul_sum]

/-- The actual signed output is the ordinary measure with its literal real
kernel response as density; its L1 construction does not change the measure. -/
theorem correctedSignedOutputMeasure_eq_withDensity {ι : Type*} [Fintype ι]
    (ν : ι → SignedMeasure ℝ) (J : ι → ℤ) (j : ℤ) (M B : ℝ)
    (hs : ∀ i, ∀ᵐ E ∂(ν i).variation, |(J i : ℝ)| ≤ E ∧ E ≤ M) :
    correctedSignedOutputMeasure ν J j M B hs =
      ((referenceMeasure j).restrict (Ioo |(j : ℝ)| B)).withDensityᵥ
        (fun e => (correctedSignedResponse ν J j e).re) := by
  have hi : Integrable (fun e => (correctedSignedResponse ν J j e).re)
      ((referenceMeasure j).restrict (Ioo |(j : ℝ)| B)) :=
    (correctedSignedResponse_integrable_lowBand ν J j M B hs).re
  ext s hset
  rw [correctedSignedOutputMeasure_apply ν J j M B hs s hset,
    withDensityᵥ_apply hi hset]

/-- The input cutoff only witnesses convergence; it does not change the actual output measure. -/
theorem correctedSignedOutputMeasure_inputCutoff_eq {ι : Type*} [Fintype ι]
    (ν : ι → SignedMeasure ℝ) (J : ι → ℤ) (j : ℤ) (M N B : ℝ)
    (hM : ∀ i, ∀ᵐ E ∂(ν i).variation, |(J i : ℝ)| ≤ E ∧ E ≤ M)
    (hN : ∀ i, ∀ᵐ E ∂(ν i).variation, |(J i : ℝ)| ≤ E ∧ E ≤ N) :
    correctedSignedOutputMeasure ν J j M B hM =
      correctedSignedOutputMeasure ν J j N B hN := by
  simp only [correctedSignedOutputMeasure_eq_withDensity]

/-- The actual variation of the induced output is supported in the open band. -/
theorem correctedSignedOutputMeasure_ae_mem_lowBand {ι : Type*} [Fintype ι]
    (ν : ι → SignedMeasure ℝ) (J : ι → ℤ) (j : ℤ) (M B : ℝ)
    (hs : ∀ i, ∀ᵐ E ∂(ν i).variation, |(J i : ℝ)| ≤ E ∧ E ≤ M) :
    ∀ᵐ E ∂(correctedSignedOutputMeasure ν J j M B hs).variation,
      E ∈ Ioo |(j : ℝ)| B := by
  rw [correctedSignedOutputMeasure,
    Measure.variation_withDensityᵥ (L1.integrable_coeFn _)]
  exact (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem measurableSet_Ioo)

/-- The induced low-band density has compact physical variation support. -/
theorem correctedSignedOutputMeasure_physicalSupport {ι : Type*} [Fintype ι]
    (ν : ι → SignedMeasure ℝ) (J : ι → ℤ) (j : ℤ) (M B : ℝ)
    (hs : ∀ i, ∀ᵐ E ∂(ν i).variation, |(J i : ℝ)| ≤ E ∧ E ≤ M) :
    ∀ᵐ E ∂(correctedSignedOutputMeasure ν J j M B hs).variation,
      |(j : ℝ)| ≤ E ∧ E ≤ B :=
  (correctedSignedOutputMeasure_ae_mem_lowBand ν J j M B hs).mono
    (fun _ hE => ⟨hE.1.le, hE.2.le⟩)

/-- The actual ordinary density measure preserves addition of physical inputs. -/
theorem correctedSignedOutputMeasure_add {ι : Type*} [Fintype ι]
    (ν μ : ι → SignedMeasure ℝ) (J : ι → ℤ) (j : ℤ) (M B : ℝ)
    (hν : ∀ i, ∀ᵐ E ∂(ν i).variation, |(J i : ℝ)| ≤ E ∧ E ≤ M)
    (hμ : ∀ i, ∀ᵐ E ∂(μ i).variation, |(J i : ℝ)| ≤ E ∧ E ≤ M) :
    correctedSignedOutputMeasure (fun i => ν i + μ i) J j M B
      (fun i => signedPhysicalSupport_add (ν i) (μ i) (J i) M (hν i) (hμ i)) =
      correctedSignedOutputMeasure ν J j M B hν + correctedSignedOutputMeasure μ J j M B hμ := by
  simp_rw [correctedSignedOutputMeasure_eq_withDensity,
    correctedSignedResponse_add ν μ J j M hν hμ, Complex.add_re]
  exact withDensityᵥ_add' (correctedSignedResponse_integrable_lowBand ν J j M B hν).re
    (correctedSignedResponse_integrable_lowBand μ J j M B hμ).re

/-- The actual ordinary density measure preserves subtraction of physical inputs. -/
theorem correctedSignedOutputMeasure_sub {ι : Type*} [Fintype ι]
    (ν μ : ι → SignedMeasure ℝ) (J : ι → ℤ) (j : ℤ) (M B : ℝ)
    (hν : ∀ i, ∀ᵐ E ∂(ν i).variation, |(J i : ℝ)| ≤ E ∧ E ≤ M)
    (hμ : ∀ i, ∀ᵐ E ∂(μ i).variation, |(J i : ℝ)| ≤ E ∧ E ≤ M) :
    correctedSignedOutputMeasure (fun i => ν i - μ i) J j M B
      (fun i => signedPhysicalSupport_sub (ν i) (μ i) (J i) M (hν i) (hμ i)) =
      correctedSignedOutputMeasure ν J j M B hν - correctedSignedOutputMeasure μ J j M B hμ := by
  simp_rw [correctedSignedOutputMeasure_eq_withDensity,
    correctedSignedResponse_sub ν μ J j M hν hμ, Complex.sub_re]
  exact withDensityᵥ_sub' (correctedSignedResponse_integrable_lowBand ν J j M B hν).re
    (correctedSignedResponse_integrable_lowBand μ J j M B hμ).re

/-- The actual ordinary density measure preserves real scaling. -/
theorem correctedSignedOutputMeasure_smul {ι : Type*} [Fintype ι]
    (ν : ι → SignedMeasure ℝ) (c : ℝ) (J : ι → ℤ) (j : ℤ) (M B : ℝ)
    (hs : ∀ i, ∀ᵐ E ∂(ν i).variation, |(J i : ℝ)| ≤ E ∧ E ≤ M) :
    correctedSignedOutputMeasure (fun i => c • ν i) J j M B
      (fun i => signedPhysicalSupport_smul (ν i) (J i) M c (hs i)) =
      c • correctedSignedOutputMeasure ν J j M B hs := by
  simp_rw [correctedSignedOutputMeasure_eq_withDensity,
    correctedSignedResponse_smul, Complex.smul_re]
  exact withDensityᵥ_smul' _ _

/-- Direct physical input plus its actual ordinary corrected density on the
open low band. The scalar threshold atom is outside this open band. -/
def finiteCorrectedLowBandOutput (S : Finset ℤ) (ν : ℤ → SignedMeasure ℝ)
    (j : ℤ) (M B : ℝ)
    (hs : ∀ J ∈ S, ∀ᵐ E ∂(ν J).variation, |(J : ℝ)| ≤ E ∧ E ≤ M) : SignedMeasure ℝ :=
  (if j ∈ S then (ν j).restrict (Ioo |(j : ℝ)| B) else 0) +
    correctedSignedOutputMeasure (fun J : S => ν J) Subtype.val j M B
      (fun J => hs J J.property)

/-- Changing only the input convergence cutoff leaves the finite actual output unchanged. -/
theorem finiteCorrectedLowBandOutput_inputCutoff_eq
    (S : Finset ℤ) (ν : ℤ → SignedMeasure ℝ) (j : ℤ) (M N B : ℝ)
    (hM : ∀ J ∈ S, ∀ᵐ E ∂(ν J).variation, |(J : ℝ)| ≤ E ∧ E ≤ M)
    (hN : ∀ J ∈ S, ∀ᵐ E ∂(ν J).variation, |(J : ℝ)| ≤ E ∧ E ≤ N) :
    finiteCorrectedLowBandOutput S ν j M B hM =
      finiteCorrectedLowBandOutput S ν j N B hN := by
  unfold finiteCorrectedLowBandOutput
  rw [correctedSignedOutputMeasure_inputCutoff_eq (fun J : S => ν J)
    Subtype.val j M N B (fun J => hM J J.property) (fun J => hN J J.property)]

/-- The actual low-band output has exactly its direct input and ordinary kernel integral. -/
theorem finiteCorrectedLowBandOutput_apply (S : Finset ℤ) (ν : ℤ → SignedMeasure ℝ)
    (j : ℤ) (M B : ℝ)
    (hs : ∀ J ∈ S, ∀ᵐ E ∂(ν J).variation, |(J : ℝ)| ≤ E ∧ E ≤ M)
    (s : Set ℝ) (hset : MeasurableSet s) :
    finiteCorrectedLowBandOutput S ν j M B hs s =
      (if j ∈ S then ν j (s ∩ Ioo |(j : ℝ)| B) else 0) +
      ∫ e in s, (correctedSignedResponse (fun J : S => ν J) Subtype.val j e).re
        ∂(referenceMeasure j).restrict (Ioo |(j : ℝ)| B) := by
  unfold finiteCorrectedLowBandOutput
  rw [_root_.add_apply, correctedSignedOutputMeasure_apply _ _ _ _ _ _ _ hset]
  congr 1
  by_cases hj : j ∈ S
  · simp only [hj, ite_true, VectorMeasure.restrict_apply _ measurableSet_Ioo hset]
  · simp [hj]

/-- The only atoms in the open low-band output are the actual direct input atoms. -/
theorem finiteCorrectedLowBandOutput_singleton (S : Finset ℤ) (ν : ℤ → SignedMeasure ℝ)
    (j : ℤ) (M B : ℝ)
    (hs : ∀ J ∈ S, ∀ᵐ E ∂(ν J).variation, |(J : ℝ)| ≤ E ∧ E ≤ M) (e : ℝ) :
    finiteCorrectedLowBandOutput S ν j M B hs {e} =
      if j ∈ S ∧ e ∈ Ioo |(j : ℝ)| B then ν j {e} else 0 := by
  unfold finiteCorrectedLowBandOutput
  rw [_root_.add_apply, correctedSignedOutputMeasure_singleton, add_zero]
  by_cases hj : j ∈ S <;> by_cases he : e ∈ Ioo |(j : ℝ)| B <;>
    simp [hj, he, VectorMeasure.restrict_apply, measurableSet_Ioo]

/-- The actual variation of the complete low-band output is supported in the
open band, including when the direct signed input has atoms. -/
theorem finiteCorrectedLowBandOutput_ae_mem_lowBand
    (S : Finset ℤ) (ν : ℤ → SignedMeasure ℝ) (j : ℤ) (M B : ℝ)
    (hs : ∀ J ∈ S, ∀ᵐ E ∂(ν J).variation, |(J : ℝ)| ≤ E ∧ E ≤ M) :
    ∀ᵐ E ∂(finiteCorrectedLowBandOutput S ν j M B hs).variation,
      E ∈ Ioo |(j : ℝ)| B := by
  have hd : ∀ᵐ E ∂(if j ∈ S then (ν j).restrict (Ioo |(j : ℝ)| B) else 0).variation,
      E ∈ Ioo |(j : ℝ)| B := by
    by_cases hj : j ∈ S
    · simp only [hj, ite_true, VectorMeasure.variation_restrict measurableSet_Ioo]
      exact ae_restrict_mem measurableSet_Ioo
    · simp [hj]
  exact (ae_add_measure_iff.mpr ⟨hd,
    correctedSignedOutputMeasure_ae_mem_lowBand (fun J : S => ν J) Subtype.val j M B
      (fun J => hs J J.property)⟩).filter_mono (ae_mono VectorMeasure.variation_add_le)

/-- Ordinary thermal tilting of the actual low-band output has the same
bounded physical support required of any finite signed input. -/
theorem finiteCorrectedLowBandOutput_physicalSupport
    (S : Finset ℤ) (ν : ℤ → SignedMeasure ℝ) (j : ℤ) (M B : ℝ)
    (hs : ∀ J ∈ S, ∀ᵐ E ∂(ν J).variation, |(J : ℝ)| ≤ E ∧ E ≤ M) :
    ∀ᵐ E ∂(finiteCorrectedLowBandOutput S ν j M B hs).variation,
      |(j : ℝ)| ≤ E ∧ E ≤ B :=
  (finiteCorrectedLowBandOutput_ae_mem_lowBand S ν j M B hs).mono
    (fun _ hE => ⟨hE.1.le, hE.2.le⟩)

/-- Addition commutes with the complete actual unweighted low-band output. -/
theorem finiteCorrectedLowBandOutput_add (S : Finset ℤ) (ν μ : ℤ → SignedMeasure ℝ)
    (j : ℤ) (M B : ℝ)
    (hν : ∀ J ∈ S, ∀ᵐ E ∂(ν J).variation, |(J : ℝ)| ≤ E ∧ E ≤ M)
    (hμ : ∀ J ∈ S, ∀ᵐ E ∂(μ J).variation, |(J : ℝ)| ≤ E ∧ E ≤ M) :
    finiteCorrectedLowBandOutput S (fun J => ν J + μ J) j M B
      (fun J hJ => signedPhysicalSupport_add (ν J) (μ J) J M (hν J hJ) (hμ J hJ)) =
      finiteCorrectedLowBandOutput S ν j M B hν + finiteCorrectedLowBandOutput S μ j M B hμ := by
  unfold finiteCorrectedLowBandOutput
  rw [correctedSignedOutputMeasure_add (fun J : S => ν J) (fun J : S => μ J)
    Subtype.val j M B (fun J => hν J J.property) (fun J => hμ J J.property)]
  by_cases hj : j ∈ S <;> simp only [hj, ite_true, ite_false, VectorMeasure.restrict_add] <;> abel

/-- Subtraction commutes with the complete actual unweighted low-band output. -/
theorem finiteCorrectedLowBandOutput_sub (S : Finset ℤ) (ν μ : ℤ → SignedMeasure ℝ)
    (j : ℤ) (M B : ℝ)
    (hν : ∀ J ∈ S, ∀ᵐ E ∂(ν J).variation, |(J : ℝ)| ≤ E ∧ E ≤ M)
    (hμ : ∀ J ∈ S, ∀ᵐ E ∂(μ J).variation, |(J : ℝ)| ≤ E ∧ E ≤ M) :
    finiteCorrectedLowBandOutput S (fun J => ν J - μ J) j M B
      (fun J hJ => signedPhysicalSupport_sub (ν J) (μ J) J M (hν J hJ) (hμ J hJ)) =
      finiteCorrectedLowBandOutput S ν j M B hν - finiteCorrectedLowBandOutput S μ j M B hμ := by
  unfold finiteCorrectedLowBandOutput
  rw [correctedSignedOutputMeasure_sub (fun J : S => ν J) (fun J : S => μ J)
    Subtype.val j M B (fun J => hν J J.property) (fun J => hμ J J.property)]
  by_cases hj : j ∈ S <;> simp only [hj, ite_true, ite_false, VectorMeasure.restrict_sub] <;> abel

/-- Real scaling commutes with the complete actual unweighted low-band output. -/
theorem finiteCorrectedLowBandOutput_smul (S : Finset ℤ) (ν : ℤ → SignedMeasure ℝ)
    (c : ℝ) (j : ℤ) (M B : ℝ)
    (hs : ∀ J ∈ S, ∀ᵐ E ∂(ν J).variation, |(J : ℝ)| ≤ E ∧ E ≤ M) :
    finiteCorrectedLowBandOutput S (fun J => c • ν J) j M B
      (fun J hJ => signedPhysicalSupport_smul (ν J) J M c (hs J hJ)) =
      c • finiteCorrectedLowBandOutput S ν j M B hs := by
  unfold finiteCorrectedLowBandOutput
  rw [correctedSignedOutputMeasure_smul (fun J : S => ν J) c
    Subtype.val j M B (fun J => hs J J.property)]
  by_cases hj : j ∈ S <;> simp only [hj, ite_true, ite_false, VectorMeasure.restrict_smul,
    smul_add, smul_zero]

end GapFamily.Analytic
