import GapFamily.Analytic.Kernel.FullKernelSmoothingSeed

/-! Pointwise physical bounds for the actual finite signed response. The input
budget is the sum of ordinary total variation masses. -/

noncomputable section

open MeasureTheory Real Set
open scoped BigOperators

namespace GapFamily.Analytic

/-- A finite set of actual signed input rows satisfies the same uniform kernel bound. -/
theorem norm_sum_correctedSignedRowResponse_le {ι : Type*} (s : Finset ι)
    (ν : ι → SignedMeasure ℝ) (J : ι → ℤ) (j : ℤ) (M : ℝ)
    (hs : ∀ i ∈ s, ∀ᵐ E ∂(ν i).variation, |(J i : ℝ)| ≤ E ∧ E ≤ M)
    (e : ℝ) (he : |(j : ℝ)| ≤ e) :
    ‖∑ i ∈ s, correctedSignedRowResponse (ν i) (J i) j e‖ ≤
      (∑ i ∈ s, (ν i).variation.real univ) * correctedKernelBound *
        (e * M + sqrt e * sqrt M) := by
  calc
    _ ≤ ∑ i ∈ s, ‖correctedSignedRowResponse (ν i) (J i) j e‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ s, (ν i).variation.real univ * correctedKernelBound *
        (e * M + sqrt e * sqrt M) :=
      Finset.sum_le_sum fun i hi => norm_correctedSignedRowResponse_le (ν i) (J i) j M (hs i hi) e he
    _ = _ := by simp only [Finset.sum_mul]

/-- Ordinary total variation controls the actual finite signed response. -/
theorem norm_correctedSignedResponse_le {ι : Type*} [Fintype ι]
    (ν : ι → SignedMeasure ℝ) (J : ι → ℤ) (j : ℤ) (M : ℝ)
    (hs : ∀ i, ∀ᵐ E ∂(ν i).variation, |(J i : ℝ)| ≤ E ∧ E ≤ M)
    (e : ℝ) (he : |(j : ℝ)| ≤ e) :
    ‖correctedSignedResponse ν J j e‖ ≤
      signedSeedMass ν * correctedKernelBound * (e * M + sqrt e * sqrt M) :=
  norm_sum_correctedSignedRowResponse_le Finset.univ ν J j M (fun i _ => hs i) e he

private theorem signedResponse_exterior_coefficient_le {B e : ℝ}
    (hB : 1 ≤ B) (hBe : B ≤ e) :
    e * (3 * B) + sqrt e * sqrt (3 * B) ≤ 6 * B * e := by
  have he1 : 1 ≤ e := hB.trans hBe
  have h3B : 1 ≤ 3 * B := by linarith
  have he : sqrt e ≤ e := Real.sqrt_le_self_iff.mpr (Or.inr he1)
  have hM : sqrt (3 * B) ≤ 3 * B := Real.sqrt_le_self_iff.mpr (Or.inr h3B)
  calc
    _ ≤ e * (3 * B) + e * (3 * B) :=
      add_le_add le_rfl (mul_le_mul he hM (sqrt_nonneg _) (by linarith))
    _ = _ := by ring

/-- Above the physical band, input support up to `3 B` gives a linear energy bound. -/
theorem norm_correctedSignedResponse_le_exterior {ι : Type*} [Fintype ι]
    (ν : ι → SignedMeasure ℝ) (J : ι → ℤ) (j : ℤ) (B : ℝ) (hB : 1 ≤ B)
    (hs : ∀ i, ∀ᵐ E ∂(ν i).variation, |(J i : ℝ)| ≤ E ∧ E ≤ 3 * B)
    (e : ℝ) (he : |(j : ℝ)| ≤ e) (hBe : B ≤ e) :
    ‖correctedSignedResponse ν J j e‖ ≤
      signedSeedMass ν * (6 * correctedKernelBound * B * e) := by
  calc
    _ ≤ signedSeedMass ν * correctedKernelBound *
        (e * (3 * B) + sqrt e * sqrt (3 * B)) :=
      norm_correctedSignedResponse_le ν J j (3 * B) hs e he
    _ ≤ signedSeedMass ν * correctedKernelBound * (6 * B * e) :=
      mul_le_mul_of_nonneg_left (signedResponse_exterior_coefficient_le hB hBe)
        (mul_nonneg (signedSeedMass_nonneg ν) correctedKernelBound_pos.le)
    _ = _ := by ring

/-- Finset form of the exterior estimate, suitable for an explicit finite spin set. -/
theorem norm_sum_correctedSignedRowResponse_le_exterior {ι : Type*} (s : Finset ι)
    (ν : ι → SignedMeasure ℝ) (J : ι → ℤ) (j : ℤ) (B : ℝ) (hB : 1 ≤ B)
    (hs : ∀ i ∈ s, ∀ᵐ E ∂(ν i).variation, |(J i : ℝ)| ≤ E ∧ E ≤ 3 * B)
    (e : ℝ) (he : |(j : ℝ)| ≤ e) (hBe : B ≤ e) :
    ‖∑ i ∈ s, correctedSignedRowResponse (ν i) (J i) j e‖ ≤
      (∑ i ∈ s, (ν i).variation.real univ) * (6 * correctedKernelBound * B * e) := by
  calc
    _ ≤ (∑ i ∈ s, (ν i).variation.real univ) * correctedKernelBound *
        (e * (3 * B) + sqrt e * sqrt (3 * B)) :=
      norm_sum_correctedSignedRowResponse_le s ν J j (3 * B) hs e he
    _ ≤ (∑ i ∈ s, (ν i).variation.real univ) * correctedKernelBound * (6 * B * e) :=
      mul_le_mul_of_nonneg_left (signedResponse_exterior_coefficient_le hB hBe)
        (mul_nonneg (Finset.sum_nonneg fun _ _ => measureReal_nonneg) correctedKernelBound_pos.le)
    _ = _ := by ring

end GapFamily.Analytic
