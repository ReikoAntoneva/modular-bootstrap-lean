import GapFamily.Analytic.Cusp.Fourier.CuspHorizontalHilbert
import GapFamily.Analytic.Cusp.Fourier.CuspHorizontalProjectionPairingMeasure

/-!
# Actual scalar mass of the horizontal average

The inverse-square profile integral is the genuine cusp Hilbert norm. The
ordinary average therefore satisfies the scalar mass bound needed for its
zero-trace lift into the completed form domain.
-/

noncomputable section
namespace GapFamily.Analytic
open Set MeasureTheory UpperHalfPlane ModularGradient

private theorem scalar_weight_row (b : ℝ → ℂ) (y : ℝ) :
    (∫ _x : ℝ in Ioo (-1/2) (1/2),
      (1 / y ^ 2 : ℝ) • ((‖b y‖ ^ 2 : ℝ) : ℂ)) =
      ((‖b y‖ ^ 2 / y ^ 2 : ℝ) : ℂ) := by
  rw [integral_const]
  norm_num [Measure.real, Real.volume_Ioo, Complex.real_smul, div_eq_mul_inv, mul_comm]

/-- Literal scalar mass transport for any actual cusp-L² profile. -/
theorem cusp_scalar_weighted_norm_integral (b : ℝ → ℂ)
    (hb : MemLp (fun τ : UpperHalfPlane => b τ.im) 2
      (modularMeasure.restrict {τ | 1 < τ.im})) :
    IntegrableOn (fun y : ℝ => ‖b y‖ ^ 2 / y ^ 2) (Ioi 1) ∧
      ‖hb.toLp (fun τ : UpperHalfPlane => b τ.im)‖ ^ 2 =
        ∫ y : ℝ in Ioi 1, ‖b y‖ ^ 2 / y ^ 2 := by
  have hi := (memLp_two_iff_integrable_sq_norm hb.aestronglyMeasurable).mp hb
  have hhigh : IntegrableOn (fun τ : UpperHalfPlane => ((‖b (τ : ℂ).im‖ ^ 2 : ℝ) : ℂ))
      {τ | 1 < τ.im} modularMeasure := by
    simpa only [IntegrableOn, coe_im, RCLike.ofReal_eq_complex_ofReal] using hi.ofReal (𝕜 := ℂ)
  have hprod := integrableOn_modular_highCusp_weight
    (fun z : ℂ => ((‖b z.im‖ ^ 2 : ℝ) : ℂ)) le_rfl hhigh
  rw [IntegrableOn, ← Measure.prod_restrict] at hprod
  have hrow : Integrable (fun y : ℝ => ((‖b y‖ ^ 2 / y ^ 2 : ℝ) : ℂ))
      (volume.restrict (Ioi 1)) := by
    simpa only [scalar_weight_row] using hprod.integral_prod_right
  refine ⟨?_, ?_⟩
  · simpa only [IntegrableOn, RCLike.re_eq_complex_re, Complex.ofReal_re] using hrow.re
  · rw [cuspMean_toLp_norm_sq]
    have h := integral_modular_highCusp_of_integrable
      (fun z : ℂ => ((‖b z.im‖ ^ 2 : ℝ) : ℂ)) le_rfl hhigh
    simp only [coe_im, scalar_weight_row, integral_complex_ofReal] at h
    exact Complex.ofReal_injective h

/-- The actual average has finite scalar weighted mass, bounded by the actual
ambient value norm. -/
theorem cuspHorizontalAverage_scalar_mass_le (F : smoothCore) :
    IntegrableOn (fun y : ℝ => ‖cuspHorizontalAverage F.val y‖ ^ 2 / y ^ 2) (Ioi 1) ∧
      (∫ y : ℝ in Ioi 1, ‖cuspHorizontalAverage F.val y‖ ^ 2 / y ^ 2) ≤ ‖value F‖ ^ 2 := by
  obtain ⟨hi, heq⟩ := cusp_scalar_weighted_norm_integral
    (cuspHorizontalAverage F.val) (cuspHorizontalAverage_memLp F (H := 1) le_rfl)
  refine ⟨hi, ?_⟩
  rw [← heq]
  change ‖cuspCoreAverage 1 le_rfl F‖ ^ 2 ≤ ‖value F‖ ^ 2
  have hnorm := (cuspCoreAverage_norm_le 1 le_rfl F).trans (norm_cuspRestrict_le 1 (value F))
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hnorm

end GapFamily.Analytic
