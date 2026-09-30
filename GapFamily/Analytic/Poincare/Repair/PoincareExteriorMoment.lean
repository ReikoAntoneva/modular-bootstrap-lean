import GapFamily.Analytic.Poincare.Repair.PoincareExteriorKernel
import GapFamily.Analytic.Foundation.SignedSqrtCoordinate

/-! Ordinary signed cancellation for the actual local-repair kernel. The
coordinate measure is the square-root pushforward of the original input;
the estimate uses its exact original total variation, including signed atoms.
-/

noncomputable section

open Set MeasureTheory Real

namespace GapFamily.Analytic

/-- The actual exterior kernel as a function of physical input energy. -/
def canonicalRepairKernelEnergy (B : ℝ) (hB : 1 ≤ B)
    (j jin : ℤ) (e E : ℝ) : ℂ :=
  canonicalRepairKernelHol B hB j jin e (sqrtEnergyCoordinate jin E : ℂ)

theorem continuous_canonicalRepairKernelEnergy (B : ℝ) (hB : 1 ≤ B)
    (j jin : ℤ) (e : ℝ) (he : |(j : ℝ)| ≤ e) :
    Continuous (canonicalRepairKernelEnergy B hB j jin e) :=
  (differentiable_canonicalRepairKernelHol B hB j jin e he).continuous.comp
    (Complex.continuous_ofReal.comp (continuous_sqrtEnergyCoordinate jin))

/-- The original signed energy integral is exactly the integral over its
actual square-root pushforward. -/
theorem signedIntegral_canonicalRepairKernelEnergy_eq_coordinate
    (B : ℝ) (hB : 1 ≤ B) (j jin : ℤ) (e : ℝ) (he : |(j : ℝ)| ≤ e)
    (ν : SignedMeasure ℝ) {L V : ℝ}
    (hν : ∀ᵐ E ∂ν.variation, E ∈ Icc L V) :
    (∫ᵛ E, canonicalRepairKernelEnergy B hB j jin e E ∂<•ν) =
      ∫ᵛ x : ℝ, canonicalRepairKernelHol B hB j jin e (x : ℂ)
        ∂<•signedSqrtCoordinate jin ν :=
  (signedIntegral_sqrtCoordinate_of_continuous jin ν
    ((differentiable_canonicalRepairKernelHol B hB j jin e he).continuous.comp
      Complex.continuous_ofReal) hν).symm

theorem canonicalRepairKernelEnergy_signedIntegrable
    (B : ℝ) (hB : 1 ≤ B) (j jin : ℤ) (e : ℝ) (he : |(j : ℝ)| ≤ e)
    (ν : SignedMeasure ℝ) {L V : ℝ}
    (hν : ∀ᵐ E ∂ν.variation, E ∈ Icc L V) :
    ν.Integrable (canonicalRepairKernelEnergy B hB j jin e) := by
  let := signedMeasure_isFiniteMeasure_variation ν
  exact integrable_of_continuousOn_interval_of_ae_mem
    (continuous_canonicalRepairKernelEnergy B hB j jin e he).continuousOn hν

def sqrtInputCenter (jin : ℤ) (L V : ℝ) : ℝ :=
  (sqrt (L - |(jin : ℝ)|) + sqrt (V - |(jin : ℝ)|)) / 2

def sqrtInputWidth (jin : ℤ) (L V : ℝ) : ℝ :=
  sqrt (V - |(jin : ℝ)|) - sqrt (L - |(jin : ℝ)|)

theorem sqrtInputWidth_nonneg (jin : ℤ) (L V : ℝ) (hLV : L ≤ V) :
    0 ≤ sqrtInputWidth jin L V :=
  sub_nonneg.mpr (sqrt_le_sqrt (sub_le_sub_right hLV _))

theorem signedSqrtCoordinate_ae_centered (jin : ℤ) (ν : SignedMeasure ℝ) {L V : ℝ}
    (hν : ∀ᵐ E ∂ν.variation, E ∈ Icc L V) :
    ∀ᵐ x ∂(signedSqrtCoordinate jin ν).totalVariation,
      x ∈ Icc (sqrtInputCenter jin L V - sqrtInputWidth jin L V / 2)
        (sqrtInputCenter jin L V + sqrtInputWidth jin L V / 2) := by
  rw [SignedMeasure.totalVariation_eq_variation]
  filter_upwards [signedSqrtCoordinate_ae_mem jin ν hν] with x hx
  dsimp [sqrtInputCenter, sqrtInputWidth]
  constructor <;> linarith [hx.1, hx.2]

/-- C2's signed-moment cancellation estimate for the literal physical-energy
repair kernel, with no independent approximation or variation hypothesis. -/
theorem norm_signedIntegral_canonicalRepairKernelEnergy_le
    (B : ℝ) (hB : 1 ≤ B) (j jin : ℤ) (e : ℝ) (he : |(j : ℝ)| ≤ e)
    (ν : SignedMeasure ℝ) (L V r : ℝ) (k : ℕ)
    (hL : |(jin : ℝ)| ≤ L) (hLV : L ≤ V) (hr : 0 < r)
    (hdr : sqrtInputWidth jin L V / (2 * r) < 1)
    (hν : ∀ᵐ E ∂ν.variation, E ∈ Icc L V)
    (hm : ∀ n ≤ k, (∫ᵛ x : ℝ, x ^ n ∂<•signedSqrtCoordinate jin ν) = 0) :
    ‖∫ᵛ E, canonicalRepairKernelEnergy B hB j jin e E ∂<•ν‖ ≤
      ν.totalVariation.real univ * canonicalRepairKernelStripSize B hB j jin e
        (|sqrtInputCenter jin L V| + r) r *
          (sqrtInputWidth jin L V / (2 * r)) ^ (k + 1) /
            (1 - sqrtInputWidth jin L V / (2 * r)) := by
  rw [signedIntegral_canonicalRepairKernelEnergy_eq_coordinate B hB j jin e he ν hν]
  have h := norm_signedIntegral_canonicalRepairKernelHol_le B hB j jin e he
    (signedSqrtCoordinate jin ν) (sqrtInputCenter jin L V) r (sqrtInputWidth jin L V) k
    hr (sqrtInputWidth_nonneg jin L V hLV) hdr
    (signedSqrtCoordinate_ae_centered jin ν hν) hm
  rwa [signedSqrtCoordinate_totalVariation_mass_eq jin ν
    (hν.mono fun E hE => hL.trans hE.1)] at h

end GapFamily.Analytic
