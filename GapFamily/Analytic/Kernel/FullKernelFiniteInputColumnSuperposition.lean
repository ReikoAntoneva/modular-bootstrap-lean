import GapFamily.Analytic.Kernel.FullKernelInputColumnSuperposition

/-! Finite families of compact physical signed inputs superpose the actual
input columns, their inverse columns, and their physical output responses.
The input and output spin families may be independently indexed. -/

noncomputable section

namespace GapFamily.Analytic

open MeasureTheory Real
open scoped BigOperators

private theorem sum_correctedSignedResponseHilbert_single
    {κ ι : Type*} [Fintype κ] [Fintype ι]
    (ν : κ → SignedMeasure ℝ) (jin : κ → ℤ) (J : ι → ℤ) (M B : ℝ)
    (hM : 0 ≤ M) (hB : 0 ≤ B)
    (hs : ∀ k, ∀ᵐ E ∂(ν k).variation, |(jin k : ℝ)| ≤ E ∧ E ≤ M) :
    (∑ k, correctedSignedResponseHilbert (fun _ : Unit => ν k) (fun _ => jin k)
      J M B hM hB (fun _ => hs k)) =
      correctedSignedResponseHilbert ν jin J M B hM hB hs := by
  apply PiLp.ext
  intro i
  change (PiLp.proj (𝕜 := ℂ) 2 (fun l => LowBandRow (J l) B) i)
    (∑ k, correctedSignedResponseHilbert (fun _ : Unit => ν k) (fun _ => jin k)
      J M B hM hB (fun _ => hs k)) = _
  rw [map_sum]
  simp only [PiLp.proj_apply, correctedSignedResponseHilbert, PiLp.toLp_apply,
    correctedSignedResponseLp, Fintype.sum_unique]

/-- The finite signed column integral is the actual finite-seed Hilbert response. -/
theorem sum_signedIntegral_correctedInputColumn
    {κ ι : Type*} [Fintype κ] [Fintype ι]
    (ν : κ → SignedMeasure ℝ) (jin : κ → ℤ) (J : ι → ℤ) (M B : ℝ)
    (hM : 0 ≤ M) (hB : 0 ≤ B)
    (hs : ∀ k, ∀ᵐ E ∂(ν k).variation, |(jin k : ℝ)| ≤ E ∧ E ≤ M) :
    (∑ k, ∫ᵛ E, correctedInputColumn J B hB (jin k)
      (sqrt (E - |(jin k : ℝ)|) : ℂ) ∂<•(ν k)) =
      correctedSignedResponseHilbert ν jin J M B hM hB hs := by
  calc
    _ = ∑ k, correctedSignedResponseHilbert (fun _ : Unit => ν k) (fun _ => jin k)
        J M B hM hB (fun _ => hs k) :=
      Finset.sum_congr rfl fun k _ =>
        signedIntegral_correctedInputColumn J B hB (jin k) (ν k) M hM (hs k)
    _ = _ := sum_correctedSignedResponseHilbert_single ν jin J M B hM hB hs

/-- The actual bounded inverse commutes with finite signed column superposition. -/
theorem sum_signedIntegral_correctedInputInverseColumn
    {κ ι : Type*} [Fintype κ] [Fintype ι]
    (ν : κ → SignedMeasure ℝ) (jin : κ → ℤ) (J : ι → ℤ) (M B : ℝ)
    (hM : 0 ≤ M) (hB : 0 ≤ B)
    (hs : ∀ k, ∀ᵐ E ∂(ν k).variation, |(jin k : ℝ)| ≤ E ∧ E ≤ M) :
    (∑ k, ∫ᵛ E, correctedInputInverseColumn J B hB (jin k)
      (sqrt (E - |(jin k : ℝ)|) : ℂ) ∂<•(ν k)) =
      correctedLowBandInverse J B
        (correctedSignedResponseHilbert ν jin J M B hM hB hs) := by
  calc
    _ = ∑ k, correctedLowBandInverse J B
        (correctedSignedResponseHilbert (fun _ : Unit => ν k) (fun _ => jin k)
          J M B hM hB (fun _ => hs k)) :=
      Finset.sum_congr rfl fun k _ =>
        signedIntegral_correctedInputInverseColumn J B hB (jin k) (ν k) M hM (hs k)
    _ = correctedLowBandInverse J B
        (∑ k, correctedSignedResponseHilbert (fun _ : Unit => ν k) (fun _ => jin k)
          J M B hM hB (fun _ => hs k)) := (map_sum _ _ _).symm
    _ = _ := congrArg (correctedLowBandInverse J B)
      (sum_correctedSignedResponseHilbert_single ν jin J M B hM hB hs)

/-- Every physical output sees the signed superposition of the finite inverse response. -/
theorem sum_signedIntegral_correctedKernelResponse_inputInverseColumn
    {κ ι : Type*} [Fintype κ] [Fintype ι]
    (ν : κ → SignedMeasure ℝ) (jin : κ → ℤ) (J : ι → ℤ) (M B : ℝ)
    (hM : 0 ≤ M) (hB : 0 ≤ B)
    (hs : ∀ k, ∀ᵐ E ∂(ν k).variation, |(jin k : ℝ)| ≤ E ∧ E ≤ M)
    (jout : ℤ) (e : ℝ) (he : |(jout : ℝ)| ≤ e) :
    (∑ k, ∫ᵛ E, correctedKernelResponse J B
      (correctedInputInverseColumn J B hB (jin k)
        (sqrt (E - |(jin k : ℝ)|) : ℂ)) jout e ∂<•(ν k)) =
      correctedKernelResponse J B
        (correctedLowBandInverse J B
          (correctedSignedResponseHilbert ν jin J M B hM hB hs)) jout e := by
  let T := correctedKernelResponseFunctional J B hB jout e he
  calc
    _ = ∑ k, T (∫ᵛ E, correctedInputInverseColumn J B hB (jin k)
        (sqrt (E - |(jin k : ℝ)|) : ℂ) ∂<•(ν k)) := by
      apply Finset.sum_congr rfl
      intro k _
      exact (complexContinuousLinearMap_signedIntegral T
        (correctedInputInverseColumn_signedIntegrable J B hB (jin k) (ν k) M (hs k))).symm
    _ = T (∑ k, ∫ᵛ E, correctedInputInverseColumn J B hB (jin k)
        (sqrt (E - |(jin k : ℝ)|) : ℂ) ∂<•(ν k)) := (map_sum _ _ _).symm
    _ = _ := congrArg T
      (sum_signedIntegral_correctedInputInverseColumn ν jin J M B hM hB hs)

end GapFamily.Analytic
