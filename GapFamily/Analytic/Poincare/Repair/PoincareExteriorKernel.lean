import GapFamily.Analytic.Poincare.Repair.PoincareAnchorExteriorOutput
import GapFamily.Analytic.Kernel.FullKernelResponseFunctional
import GapFamily.Analytic.Kernel.FullKernelResponseConjugation
import GapFamily.Analytic.Kernel.FullKernelInputInverseStripBound
import GapFamily.Analytic.Foundation.MomentCancellation

/-! The actual exterior kernel of canonical local repair. Its holomorphic
input coordinate keeps both the inverse correction and the direct high-band
part of the normalized anchor. All operators and measures are the canonical
ones; holomorphic extension does not replace the actual repair output.
-/

noncomputable section

open Set MeasureTheory Real
open scoped ComplexConjugate

namespace GapFamily.Analytic

/-- The complete exterior repair kernel in the input square-root coordinate. -/
def canonicalRepairKernelHol (B : ℝ) (hB : 1 ≤ B) (j jin : ℤ) (e : ℝ) (z : ℂ) : ℂ :=
  correctedKernelHolInput j jin 1 e z -
    correctedKernelResponse (fun J : LowBandSpin B => (J : ℤ)) B
      (correctedInputInverseColumn Subtype.val B (zero_le_one.trans hB) jin z) j e +
    correctedInputInverseThreshold (fun J : LowBandSpin B => (J : ℤ)) B
      (zero_le_one.trans hB) jin z * (canonicalAnchorExteriorNumerator B hB j e : ℂ)

/-- At each physical output point the complete actual repair kernel is entire. -/
theorem differentiable_canonicalRepairKernelHol (B : ℝ) (hB : 1 ≤ B)
    (j jin : ℤ) (e : ℝ) (he : |(j : ℝ)| ≤ e) :
    Differentiable ℂ (canonicalRepairKernelHol B hB j jin e) :=
  ((differentiable_correctedKernelHolInput j jin 1 e).sub
    (differentiable_correctedKernelResponse_inverseColumn
      (fun J : LowBandSpin B => (J : ℤ)) B (zero_le_one.trans hB) jin j e he)).add
    ((differentiable_correctedInputInverseThreshold
      (fun J : LowBandSpin B => (J : ℤ)) B (zero_le_one.trans hB) jin).mul_const _)

/-- The entire kernel is real on the full real coordinate axis. -/
theorem conj_canonicalRepairKernelHol_ofReal (B : ℝ) (hB : 1 ≤ B)
    (j jin : ℤ) (e x : ℝ) :
    conj (canonicalRepairKernelHol B hB j jin e (x : ℂ)) =
      canonicalRepairKernelHol B hB j jin e x := by
  unfold canonicalRepairKernelHol
  rw [map_add, map_sub, map_mul, Complex.conj_ofReal,
    conj_correctedKernelHolInput, Complex.conj_ofReal,
    conj_correctedKernelResponse_of_real _ _ _
      (correctedInputInverseColumn_real _ _ _
        (isUnit_correctedLowBandIdentityPlus_canonical B hB) jin x),
    conj_correctedInputInverseThreshold_ofReal _ _ _
      (isUnit_correctedLowBandIdentityPlus_canonical B hB)]

theorem canonicalRepairKernelHol_ofReal_im (B : ℝ) (hB : 1 ≤ B)
    (j jin : ℤ) (e x : ℝ) :
    (canonicalRepairKernelHol B hB j jin e (x : ℂ)).im = 0 :=
  Complex.conj_eq_iff_im.mp (conj_canonicalRepairKernelHol_ofReal B hB j jin e x)

/-- Positive physical input energies recover the literal original corrected
kernel, its actual inverse response, and its ordinary inverse threshold mass. -/
theorem canonicalRepairKernelHol_sqrt (B : ℝ) (hB : 1 ≤ B)
    (j jin : ℤ) (e E : ℝ) (hE : |(jin : ℝ)| ≤ E) :
    canonicalRepairKernelHol B hB j jin e (sqrt (E - |(jin : ℝ)|) : ℂ) =
      correctedKernel j jin e E -
        correctedKernelResponse (fun J : LowBandSpin B => (J : ℤ)) B
          (correctedInputInverseColumn Subtype.val B (zero_le_one.trans hB)
            jin (sqrt (E - |(jin : ℝ)|) : ℂ)) j e +
        correctedInputInverseThreshold (fun J : LowBandSpin B => (J : ℤ)) B
          (zero_le_one.trans hB) jin (sqrt (E - |(jin : ℝ)|) : ℂ) *
            (canonicalAnchorExteriorNumerator B hB j e : ℂ) := by
  unfold canonicalRepairKernelHol
  rw [correctedKernelHolInput_ofReal j jin 1 e _ (by norm_num) (sqrt_nonneg _),
    one_mul, sq_sqrt (sub_nonneg.mpr hE), add_sub_cancel]

/-- An explicit strip majorant retains the actual inverse norm and complete
anchor numerator. The real center enters only through the polynomial radius. -/
def canonicalRepairKernelStripSize (B : ℝ) (hB : 1 ≤ B)
    (j jin : ℤ) (e R r : ℝ) : ℝ :=
  inputColumnStripPolynomial jin R * (e + 2 * sqrt e) * exp (4 * π * r * sqrt e) +
    (correctedKernelBound * (e * B + sqrt e * sqrt B) *
      sqrt (Fintype.card (LowBandSpin B) : ℝ)) *
        (‖correctedLowBandInverse (fun J : LowBandSpin B => (J : ℤ)) B‖ *
          inputColumnStripSize (Fintype.card (LowBandSpin B)) jin B R r) +
    (3 * B * (1 + (Fintype.card (LowBandSpin B) : ℝ) *
      (correctedSmoothingBound B * sqrt (Fintype.card (LowBandSpin B) : ℝ)) *
        ‖correctedLowBandInverse (fun J : LowBandSpin B => (J : ℤ)) B‖) *
          inputColumnStripSize (Fintype.card (LowBandSpin B)) jin B R r) *
            |canonicalAnchorExteriorNumerator B hB j e|

theorem norm_canonicalRepairKernelHol_strip_le (B : ℝ) (hB : 1 ≤ B)
    (j jin : ℤ) (e R r : ℝ) (he : |(j : ℝ)| ≤ e)
    (hR : 0 ≤ R) (hr : 0 ≤ r) (z : ℂ) (hz : ‖z‖ ≤ R) (him : |z.im| ≤ r) :
    ‖canonicalRepairKernelHol B hB j jin e z‖ ≤
      canonicalRepairKernelStripSize B hB j jin e R r := by
  have he0 : 0 ≤ e := (abs_nonneg _).trans he
  have hB0 : 0 ≤ B := zero_le_one.trans hB
  have hp : ‖correctedKernelHolInput j jin 1 e z‖ ≤
      inputColumnStripPolynomial jin R * (e + 2 * sqrt e) * exp (4 * π * r * sqrt e) :=
    (norm_correctedKernelHolInput_rectangle_le j jin e e R r z he le_rfl hz him).trans
      (inputColumnStripHilbertCoefficient_le jin e R r he0 hR hr)
  have hi := norm_correctedInputInverseColumn_strip_le
    (fun J : LowBandSpin B => (J : ℤ)) B hB0 jin R r hR hr z hz him
  have ht := norm_correctedInputInverseThreshold_strip_le
    (fun J : LowBandSpin B => (J : ℤ)) B hB
      (fun J => (lowBandSpin_physical B J).le) jin R r hR hr z hz him
  have hc : 0 ≤ correctedKernelBound * (e * B + sqrt e * sqrt B) *
      sqrt (Fintype.card (LowBandSpin B) : ℝ) := by
    have := correctedKernelBound_pos
    positivity
  unfold canonicalRepairKernelHol canonicalRepairKernelStripSize
  refine (norm_add_le _ _).trans (add_le_add
    ((norm_sub_le _ _).trans (add_le_add hp ?_)) ?_)
  · exact (norm_correctedKernelResponse_le _ B hB0 _ j e he).trans
      (mul_le_mul_of_nonneg_left hi hc)
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right ht (abs_nonneg _)

/-- A real-centered disk changes only the polynomial radius. -/
theorem norm_canonicalRepairKernelHol_real_disk_le (B : ℝ) (hB : 1 ≤ B)
    (j jin : ℤ) (e x r : ℝ) (he : |(j : ℝ)| ≤ e) (hr : 0 ≤ r)
    (z : ℂ) (hz : z ∈ Metric.closedBall (x : ℂ) r) :
    ‖canonicalRepairKernelHol B hB j jin e z‖ ≤
      canonicalRepairKernelStripSize B hB j jin e (|x| + r) r := by
  have hd : ‖z - (x : ℂ)‖ ≤ r := by
    simpa only [Metric.mem_closedBall, dist_eq_norm] using hz
  have hn : ‖z‖ ≤ |x| + r := by
    have h := norm_add_le (z - (x : ℂ)) (x : ℂ)
    simp only [sub_add_cancel, Complex.norm_real, Real.norm_eq_abs] at h
    linarith
  have him : |z.im| ≤ r := by
    simpa only [Complex.sub_im, Complex.ofReal_im, sub_zero] using
      (Complex.abs_im_le_norm (z - (x : ℂ))).trans hd
  exact norm_canonicalRepairKernelHol_strip_le B hB j jin e (|x| + r) r he
    (by positivity) hr z hn him

/-- Ordinary signed moments cancel the actual entire exterior kernel, with
the Cauchy geometric factor and its proved sharp strip majorant. -/
theorem norm_signedIntegral_canonicalRepairKernelHol_le
    (B : ℝ) (hB : 1 ≤ B) (j jin : ℤ) (e : ℝ) (he : |(j : ℝ)| ≤ e)
    (ν : SignedMeasure ℝ) (c r d : ℝ) (k : ℕ)
    (hr : 0 < r) (hd : 0 ≤ d) (hdr : d / (2 * r) < 1)
    (hν : ∀ᵐ x ∂ν.totalVariation, x ∈ Icc (c - d / 2) (c + d / 2))
    (hm : ∀ n ≤ k, (∫ᵛ x : ℝ, x ^ n ∂<•ν) = 0) :
    ‖∫ᵛ x : ℝ, canonicalRepairKernelHol B hB j jin e (x : ℂ) ∂<•ν‖ ≤
      ν.totalVariation.real univ *
        canonicalRepairKernelStripSize B hB j jin e (|c| + r) r *
          (d / (2 * r)) ^ (k + 1) / (1 - d / (2 * r)) := by
  have hcenter : (c : ℂ) ∈ Metric.closedBall (c : ℂ) r := by
    simpa using hr.le
  have hA : 0 ≤ canonicalRepairKernelStripSize B hB j jin e (|c| + r) r :=
    (norm_nonneg _).trans
      (norm_canonicalRepairKernelHol_real_disk_le B hB j jin e c r he hr.le _ hcenter)
  exact norm_signedIntegral_le_of_holomorphic_real_moments hr hA hd hdr
    (differentiable_canonicalRepairKernelHol B hB j jin e he).diffContOnCl
    (fun z hz => norm_canonicalRepairKernelHol_real_disk_le B hB j jin e c r he hr.le z
      (Metric.sphere_subset_closedBall hz)) hν hm

end GapFamily.Analytic
