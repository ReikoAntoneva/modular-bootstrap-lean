import GapFamily.Analytic.Kernel.FullKernelResponseBound
import GapFamily.Analytic.Kernel.FullKernelLowBandControl
import GapFamily.Analytic.Foundation.Propagation

/-! Quantitative propagation for the actual full low-band response. The
observation norm is an ordinary interval integral; its later comparison with
the positive quadratic form is kept separate. -/

noncomputable section

open MeasureTheory Real Set Metric

namespace GapFamily.Analytic

def correctedPropagationExponent : ℝ := correctedResponseDiskExponent 16385

theorem correctedPropagationExponent_pos : 0 < correctedPropagationExponent :=
  correctedResponseDiskExponent_pos _ (by norm_num)

private theorem propagation_of_observation_bound {F : ℂ → ℂ} {A δ : ℝ}
    (hA : 0 ≤ A) (hf : Differentiable ℂ F)
    (hbound : ∀ z : ℂ, ‖z‖ ≤ 16384 → ‖F z‖ ≤ A)
    (hobs : sqrt (∫ t in sqrt 2..sqrt 3, ‖F (t : ℂ)‖ ^ 2) ≤ δ)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖F (t : ℂ)‖ ≤ 100 * sqrt (A * δ) := by
  apply (norm_le_sqrt_l2_of_fixed_disk hA hf.diffContOnCl
    (fun z hz => hbound z (by simpa only [mem_closedBall, dist_zero_right] using hz)) ht).trans
  exact mul_le_mul_of_nonneg_left
    (sqrt_le_sqrt (mul_le_mul_of_nonneg_left hobs hA)) (by norm_num)

/-- Propagation of every nonzero output row of the actual corrected response. -/
theorem norm_correctedKernelScaledResponse_le_of_observation
    {ι : Type*} [Fintype ι] (J : ι → ℤ) (hJ : Function.Injective J)
    (b : ℝ) (hb : 1 ≤ b) (hband : ∀ i, |(J i : ℝ)| < b)
    (f : LowBandHilbert J b) (j : ℤ) (hj : |(j : ℝ)| ≤ b) (δ : ℝ)
    (hobs : sqrt (∫ t in sqrt 2..sqrt 3,
      ‖correctedKernelScaledResponse J b f j (t : ℂ)‖ ^ 2) ≤ δ)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖correctedKernelScaledResponse J b f j t‖ ≤
      100 * sqrt (exp (correctedPropagationExponent * b) * ‖f‖ * δ) := by
  apply propagation_of_observation_bound (by positivity)
    (differentiable_correctedKernelScaledResponse J b (by linarith) f j) _ hobs ht
  intro z hz
  exact norm_correctedKernelScaledResponse_le_exp J hJ b hb hband f j hj
    16385 (by norm_num) z (by linarith)

/-- The scalar removable quotient propagates with the same constant. -/
theorem norm_correctedKernelScalarNormalizedResponse_le_of_observation
    {ι : Type*} [Fintype ι] (J : ι → ℤ) (hJ : Function.Injective J)
    (b : ℝ) (hb : 1 ≤ b) (hband : ∀ i, |(J i : ℝ)| < b)
    (f : LowBandHilbert J b) (δ : ℝ)
    (hobs : sqrt (∫ t in sqrt 2..sqrt 3,
      ‖correctedKernelScalarNormalizedResponse J b f (t : ℂ)‖ ^ 2) ≤ δ)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖correctedKernelScalarNormalizedResponse J b f t‖ ≤
      100 * sqrt (exp (correctedPropagationExponent * b) * ‖f‖ * δ) := by
  apply propagation_of_observation_bound (by positivity)
    (differentiable_correctedKernelScalarNormalizedResponse J b (by linarith) f) _ hobs ht
  intro z hz
  simpa only [correctedPropagationExponent, show (16384 : ℝ) + 1 = 16385 by norm_num]
    using norm_correctedKernelScalarNormalizedResponse_le_exp J hJ b hb hband f
      16384 (by norm_num) z hz

/-- Ordinary observation bounds control the entire full-kernel operator,
including the infinite-reference-mass scalar row through its removable zero. -/
theorem norm_sq_correctedLowBandOperator_le_of_observation
    {ι : Type*} [Fintype ι] (J : ι → ℤ) (hJ : Function.Injective J)
    (b : ℝ) (hb : 1 ≤ b) (hband : ∀ i, |(J i : ℝ)| < b)
    (f : LowBandHilbert J b) (δ : ℝ) (hδ : 0 ≤ δ)
    (hscalar : ∀ i, J i = 0 → sqrt (∫ t in sqrt 2..sqrt 3,
      ‖correctedKernelScalarNormalizedResponse J b f (t : ℂ)‖ ^ 2) ≤ δ)
    (hresponse : ∀ i, J i ≠ 0 → sqrt (∫ t in sqrt 2..sqrt 3,
      ‖correctedKernelScaledResponse J b f (J i) (t : ℂ)‖ ^ 2) ≤ δ) :
    ‖correctedLowBandOperator J b f‖ ^ 2 ≤
      10000 * (Fintype.card ι : ℝ) * b *
        exp (correctedPropagationExponent * b) * ‖f‖ * δ := by
  have h := norm_sq_correctedLowBandOperator_le_of_response_bound J b hb f
    (100 * sqrt (exp (correctedPropagationExponent * b) * ‖f‖ * δ))
    (fun i hi t ht => norm_correctedKernelScalarNormalizedResponse_le_of_observation
      J hJ b hb hband f δ (hscalar i hi) ht)
    (fun i hi t ht => norm_correctedKernelScaledResponse_le_of_observation
      J hJ b hb hband f (J i) (hband i).le δ (hresponse i hi) ht)
  convert h using 1
  rw [mul_pow, sq_sqrt (by positivity)]
  ring

end GapFamily.Analytic
