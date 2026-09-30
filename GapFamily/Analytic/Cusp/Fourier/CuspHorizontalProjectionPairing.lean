import GapFamily.Analytic.Cusp.Fourier.CuspHorizontalHilbert
import GapFamily.Analytic.Cusp.Fourier.CuspHorizontalProjectionPairingMeasure

/-!
# Pairing with the ordinary horizontal average

The actual cusp L² pairing is transported to the inverse-square weighted product
strip. On each horizontal row, integration against an averaged first argument
replaces the second argument by its ordinary length-one average.
-/

noncomputable section

namespace GapFamily.Analytic

open Set MeasureTheory UpperHalfPlane

theorem cuspHorizontalAverage_eq_setIntegral (G : ModularGradient.smoothCore) (y : ℝ) :
    cuspHorizontalAverage G.val y =
      ∫ x in Ioo (-1/2 : ℝ) (1/2), G.val (Complex.mk x y) := by
  simp only [cuspHorizontalAverage, cuspHorizontalSlice,
    intervalIntegral.integral_of_le (by norm_num : (-1/2 : ℝ) ≤ 1/2),
    restrict_Ioo_eq_restrict_Ioc]

theorem cuspHorizontalAverage_row_pairing (c : ℂ) (G : ModularGradient.smoothCore)
    {y : ℝ} (hy : 0 < y) :
    (∫ x in Ioo (-1/2 : ℝ) (1/2), (1 / y^2 : ℝ) •
      inner ℂ c (G.val (Complex.mk x y))) =
    (∫ _x in Ioo (-1/2 : ℝ) (1/2), (1 / y^2 : ℝ) •
      inner ℂ c (cuspHorizontalAverage G.val y)) := by
  have hi : IntegrableOn (fun x => G.val (Complex.mk x y))
      (Ioo (-1/2 : ℝ) (1/2)) :=
    (contDiff_cuspHorizontalSlice G.property.1 hy).continuous.integrableOn_Icc.mono_set
      Ioo_subset_Icc_self
  rw [integral_smul, integral_inner hi, ← cuspHorizontalAverage_eq_setIntegral G y]
  rw [integral_const]
  norm_num [Measure.real, Real.volume_Ioo]

theorem cuspCoreAverage_inner_coreValue_integrable (H : ℝ) (hH : 1 ≤ H)
    (F G : ModularGradient.smoothCore) :
    IntegrableOn (fun τ : UpperHalfPlane =>
      inner ℂ (cuspHorizontalAverage F.val τ.im) (G.val τ)) {τ | H < τ.im} modularMeasure := by
  apply (L2.integrable_inner (𝕜 := ℂ) (cuspCoreAverage H hH F) (cuspCoreValue H G)).congr
  filter_upwards [cuspCoreAverage_ae H hH F, cuspCoreValue_ae H G] with τ hF hG
  rw [hF, hG]

theorem cuspCoreAverage_inner_coreAverage_integrable (H : ℝ) (hH : 1 ≤ H)
    (F G : ModularGradient.smoothCore) :
    IntegrableOn (fun τ : UpperHalfPlane =>
      inner ℂ (cuspHorizontalAverage F.val τ.im) (cuspHorizontalAverage G.val τ.im))
      {τ | H < τ.im} modularMeasure := by
  apply (L2.integrable_inner (𝕜 := ℂ) (cuspCoreAverage H hH F) (cuspCoreAverage H hH G)).congr
  filter_upwards [cuspCoreAverage_ae H hH F, cuspCoreAverage_ae H hH G] with τ hF hG
  rw [hF, hG]

/-- Actual dense-core pairing for the ordinary horizontal averaging operator. -/
theorem cuspCoreAverage_inner_coreValue_eq_average (H : ℝ) (hH : 1 ≤ H)
    (F G : ModularGradient.smoothCore) :
    inner ℂ (cuspCoreAverage H hH F) (cuspCoreValue H G) =
      inner ℂ (cuspCoreAverage H hH F) (cuspCoreAverage H hH G) := by
  have hvalue : inner ℂ (cuspCoreAverage H hH F) (cuspCoreValue H G) =
      ∫ τ : UpperHalfPlane in {τ | H < τ.im},
        inner ℂ (cuspHorizontalAverage F.val τ.im) (G.val τ) ∂modularMeasure := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [cuspCoreAverage_ae H hH F, cuspCoreValue_ae H G] with τ hF hG
    rw [hF, hG]
  have havg : inner ℂ (cuspCoreAverage H hH F) (cuspCoreAverage H hH G) =
      ∫ τ : UpperHalfPlane in {τ | H < τ.im},
        inner ℂ (cuspHorizontalAverage F.val τ.im)
          (cuspHorizontalAverage G.val τ.im) ∂modularMeasure := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [cuspCoreAverage_ae H hH F, cuspCoreAverage_ae H hH G] with τ hF hG
    rw [hF, hG]
  rw [hvalue, havg]
  have hleft := integral_modular_highCusp_of_integrable
    (fun z => inner ℂ (cuspHorizontalAverage F.val z.im) (G.val z)) hH
    (cuspCoreAverage_inner_coreValue_integrable H hH F G)
  have hright := integral_modular_highCusp_of_integrable
    (fun z => inner ℂ (cuspHorizontalAverage F.val z.im)
      (cuspHorizontalAverage G.val z.im)) hH
    (cuspCoreAverage_inner_coreAverage_integrable H hH F G)
  simp only [coe_im] at hleft hright
  rw [hleft, hright]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro y hy
  exact cuspHorizontalAverage_row_pairing (cuspHorizontalAverage F.val y) G
    (lt_trans zero_lt_one (hH.trans_lt hy))

end GapFamily.Analytic
