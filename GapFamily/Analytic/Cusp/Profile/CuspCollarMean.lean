import GapFamily.Analytic.Cusp.Profile.CuspCollarMeanTest
import GapFamily.Analytic.Cusp.Fourier.CuspHorizontalProjection

/-!
# The actual normalized scalar collar mean

A genuine cusp L² test with value `ε⁻¹ y²` on the collar cancels the hyperbolic
measure's inverse-square weight. Its Riesz functional therefore agrees with
the ordinary normalized collar average, and is unchanged by horizontal
averaging. In particular it vanishes on the actual zero-average kernel.
-/

noncomputable section

namespace GapFamily.Analytic

open Set MeasureTheory UpperHalfPlane

/-- The actual bounded complex-linear mean on a positive-width collar. -/
def cuspCollarMean (ε : ℝ) (hε : 0 < ε) : cuspHilbert 1 →L[ℂ] ℂ :=
  innerSL ℂ (cuspCollarMeanTest ε hε)

theorem cuspCollarMean_apply (ε : ℝ) (hε : 0 < ε) (u : cuspHilbert 1) :
    cuspCollarMean ε hε u = inner ℂ (cuspCollarMeanTest ε hε) u := rfl

private theorem collarMean_setIntegral_row (g : ℂ → ℂ) (y : ℝ) :
    (∫ x in Ioo (-1/2 : ℝ) (1/2), g (Complex.mk x y)) =
      cuspHorizontalAverage g y := by
  simp only [cuspHorizontalAverage, cuspHorizontalSlice,
    intervalIntegral.integral_of_le (by norm_num : (-1/2 : ℝ) ≤ 1/2),
    restrict_Ioo_eq_restrict_Ioc]

/-- Representative agreement on the actual cusp yields the literal normalized
ordinary collar integral. The integrability needed for Fubini comes from L². -/
theorem cuspCollarMean_of_ae (ε : ℝ) (hε : 0 < ε) (u : cuspHilbert 1)
    (g : ℂ → ℂ)
    (hu : u =ᵐ[modularMeasure.restrict {τ : UpperHalfPlane | 1 < τ.im}]
      fun τ => g τ) :
    cuspCollarMean ε hε u =
      ε⁻¹ • (∫ y in (1 : ℝ)..(1 + ε), cuspHorizontalAverage g y) := by
  let K : ℂ → ℂ := fun z => (Ioo 1 (1 + ε)).indicator
    (fun y => (ε⁻¹ * y ^ 2) • g z) z.im
  have hrep : (fun τ => inner ℂ (cuspCollarMeanTest ε hε τ) (u τ))
      =ᵐ[modularMeasure.restrict {τ : UpperHalfPlane | 1 < τ.im}]
        fun τ => K τ := by
    filter_upwards [cuspCollarMeanTest_ae ε hε, hu] with τ ht hg
    rw [ht, hg]
    by_cases hτ : 1 < τ.im ∧ τ.im < 1 + ε
    · simp [cuspCollarMeanWeight, K, hτ, RCLike.inner_apply, Complex.real_smul, mul_comm]
    · simp [cuspCollarMeanWeight, K, hτ]
  have hK : IntegrableOn (fun τ : UpperHalfPlane => K τ)
      {τ | 1 < τ.im} modularMeasure :=
    (L2.integrable_inner (𝕜 := ℂ) (cuspCollarMeanTest ε hε) u).congr hrep
  have heq : cuspCollarMean ε hε u =
      ∫ τ : UpperHalfPlane in {τ | 1 < τ.im}, K τ ∂modularMeasure := by
    rw [cuspCollarMean_apply, L2.inner_def]
    exact integral_congr_ae hrep
  rw [heq, integral_modular_highCusp_of_integrable K le_rfl hK]
  trans ∫ y in Ioi (1 : ℝ), (Ioo 1 (1 + ε)).indicator
    (fun y => ε⁻¹ • cuspHorizontalAverage g y) y
  · apply setIntegral_congr_fun measurableSet_Ioi
    intro y hy
    by_cases hy' : y < 1 + ε
    · have hyne : y ≠ 0 := ne_of_gt (lt_trans zero_lt_one hy)
      have hm : y ∈ Ioo 1 (1 + ε) := ⟨hy, hy'⟩
      have hs : (1 / y ^ 2) * (ε⁻¹ * y ^ 2) = ε⁻¹ := by
        field_simp
      simp only [K, Set.indicator_of_mem hm]
      simp_rw [smul_smul, hs]
      rw [integral_smul, collarMean_setIntegral_row]
    · have hm : y ∉ Ioo 1 (1 + ε) := fun hm => hy' hm.2
      simp [K, hm]
  · rw [setIntegral_indicator measurableSet_Ioo,
      Set.inter_eq_right.mpr Ioo_subset_Ioi_self, integral_smul,
      restrict_Ioo_eq_restrict_Ioc,
      ← intervalIntegral.integral_of_le (by linarith : (1 : ℝ) ≤ 1 + ε)]

/-- The functional is the ordinary normalized collar mean on every smooth core value. -/
theorem cuspCollarMean_core (ε : ℝ) (hε : 0 < ε) (F : ModularGradient.smoothCore) :
    cuspCollarMean ε hε (cuspCoreValue 1 F) =
      ε⁻¹ • (∫ y in (1 : ℝ)..(1 + ε), cuspHorizontalAverage F.val y) :=
  cuspCollarMean_of_ae ε hε (cuspCoreValue 1 F) F.val (cuspCoreValue_ae 1 F)

theorem cuspCollarMean_coreAverage (ε : ℝ) (hε : 0 < ε)
    (F : ModularGradient.smoothCore) :
    cuspCollarMean ε hε (cuspCoreAverage 1 le_rfl F) =
      ε⁻¹ • (∫ y in (1 : ℝ)..(1 + ε), cuspHorizontalAverage F.val y) := by
  rw [cuspCollarMean_of_ae ε hε (cuspCoreAverage 1 le_rfl F)
    (fun z => cuspHorizontalAverage F.val z.im) (cuspCoreAverage_ae 1 le_rfl F)]
  have hh : cuspHorizontalAverage (fun z => cuspHorizontalAverage F.val z.im) =
      cuspHorizontalAverage F.val := by
    funext y
    change (∫ _x in (-1/2 : ℝ)..(1/2), cuspHorizontalAverage F.val y) = _
    norm_num [intervalIntegral.integral_const]
  rw [hh]

/-- Ordinary collar integration commutes with the actual extended horizontal average. -/
theorem cuspCollarMean_comp_average (ε : ℝ) (hε : 0 < ε) :
    (cuspCollarMean ε hε).comp (cuspAverage 1 le_rfl) = cuspCollarMean ε hε := by
  apply DFunLike.coe_injective
  apply (cuspCoreValue_dense_range 1).equalizer
    ((cuspCollarMean ε hε).comp (cuspAverage 1 le_rfl)).continuous
    (cuspCollarMean ε hε).continuous
  funext F
  simp only [Function.comp_apply, ContinuousLinearMap.comp_apply,
    cuspAverage_core, cuspCollarMean_coreAverage, cuspCollarMean_core]

theorem cuspCollarMean_average (ε : ℝ) (hε : 0 < ε) (u : cuspHilbert 1) :
    cuspCollarMean ε hε (cuspAverage 1 le_rfl u) = cuspCollarMean ε hε u :=
  congrArg (fun T : cuspHilbert 1 →L[ℂ] ℂ => T u) (cuspCollarMean_comp_average ε hε)

/-- The actual collar mean vanishes on the zero-horizontal-average channel. -/
theorem cuspCollarMean_zero_on_kernel (ε : ℝ) (hε : 0 < ε) (u : cuspHilbert 1)
    (hu : cuspAverage 1 le_rfl u = 0) : cuspCollarMean ε hε u = 0 := by
  have h := cuspCollarMean_average ε hε u
  rw [hu, map_zero] at h
  exact h.symm

end GapFamily.Analytic
