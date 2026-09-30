import GapFamily.Analytic.Modular.ModularComplexFrameTest
import GapFamily.Analytic.Modular.Geometry.ModularCutoffCommutator

noncomputable section
namespace GapFamily.Analytic.ModularGradient.InteriorCutoff
open Set MeasureTheory UpperHalfPlane
open scoped ContDiff ComplexConjugate

private def frameProductCoefficient (χ : ℂ → ℝ) (v : ℂ) : ℂ → ℂ :=
  fun z => (fderiv ℝ χ z v : ℂ)

private theorem frameProductCoefficient_smooth (χ : ℂ → ℝ) (hχ : ContDiff ℝ ∞ χ) (v : ℂ) :
    ContDiff ℝ ∞ (frameProductCoefficient χ v) :=
  Complex.ofRealCLM.contDiff.comp (contDiff_testDerivative χ hχ v)

private theorem frameProductCoefficient_compact (χ : ℂ → ℝ) (hc : HasCompactSupport χ) (v : ℂ) :
    HasCompactSupport (frameProductCoefficient χ v) :=
  (hc.fderiv_apply ℝ v).comp_left Complex.ofReal_zero

private theorem frameProductCoefficient_support (χ : ℂ → ℝ)
    (hs : tsupport χ ⊆ modularInterior) (v : ℂ) :
    tsupport (frameProductCoefficient χ v) ⊆ modularInterior :=
  (tsupport_comp_subset Complex.ofReal_zero (fun z => fderiv ℝ χ z v)).trans
    ((tsupport_fderiv_apply_subset ℝ (f := χ) v).trans hs)

private def frameProductTest (χ : ℂ → ℝ) (v : ℂ) (F : smoothCore) : ℂ → ℂ :=
  fun z => frameProductCoefficient χ v z * F.val z

private theorem frameProductTest_smooth (χ : ℂ → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hs : tsupport χ ⊆ modularInterior) (v : ℂ) (F : smoothCore) :
    ContDiff ℝ ∞ (frameProductTest χ v F) :=
  cutoff_contDiff (frameProductCoefficient_smooth χ hχ v)
    (frameProductCoefficient_support χ hs v) F

private theorem frameProductTest_compact (χ : ℂ → ℝ) (hc : HasCompactSupport χ)
    (v : ℂ) (F : smoothCore) : HasCompactSupport (frameProductTest χ v F) :=
  (frameProductCoefficient_compact χ hc v).mul_right

private theorem frameProductTest_support (χ : ℂ → ℝ)
    (hs : tsupport χ ⊆ modularInterior) (v : ℂ) (F : smoothCore) :
    tsupport (frameProductTest χ v F) ⊆ modularInterior :=
  tsupport_mul_subset_left.trans (frameProductCoefficient_support χ hs v)

private theorem frameProductTest_frame (χ : ℂ → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ modularInterior)
    (v : ℂ) (F : smoothCore) :
    complexFrameTest (frameProductTest χ v F) (frameProductTest_smooth χ hχ hs v F)
      (frameProductTest_compact χ hc v F) = derivativeMultiplier χ hχ hc v (value F) := by
  apply Lp.ext
  filter_upwards [complexFrameTest_ae (frameProductTest χ v F)
      (frameProductTest_smooth χ hχ hs v F) (frameProductTest_compact χ hc v F),
    realMultiplier_ae (fun z => z.im * fderiv ℝ χ z v)
      (Complex.continuous_im.mul (continuous_testDerivative χ hχ v))
      (hc.fderiv_apply ℝ v).mul_left (value F), value_ae F] with τ hf hm hv
  change _ = realMultiplier _ _ _ (value F) τ
  rw [hf, hm, hv]
  simp only [frameProductTest, frameProductCoefficient, Complex.ofReal_mul, UpperHalfPlane.coe_im]
  ring

private theorem frameProductTest_divergence (χ : ℂ → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ modularInterior)
    (v : ℂ) (hmem : ∀ F : smoothCore, MemLp (directional F.val v) 2 modularMeasure)
    (F : smoothCore) :
    complexDivergenceTest (frameProductTest χ v F) (frameProductTest_smooth χ hχ hs v F)
      (frameProductTest_compact χ hc v F) v =
      secondMultiplier χ hχ hc v (value F) -
        derivativeMultiplier χ hχ hc v (component v hmem F) := by
  apply Lp.ext
  filter_upwards [complexDivergenceTest_ae (frameProductTest χ v F)
      (frameProductTest_smooth χ hχ hs v F) (frameProductTest_compact χ hc v F) v,
    realMultiplier_ae (fun z => -(z.im ^ 2 * fderiv ℝ (fun w => fderiv ℝ χ w v) z v))
      (((Complex.continuous_im.pow 2).mul
        (continuous_testDerivative _ (contDiff_testDerivative χ hχ v) v)).neg)
      (compactSupport_testDivergence _ (hc.fderiv_apply ℝ v) v) (value F),
    realMultiplier_ae (fun z => z.im * fderiv ℝ χ z v)
      (Complex.continuous_im.mul (continuous_testDerivative χ hχ v))
      (hc.fderiv_apply ℝ v).mul_left (component v hmem F),
    Lp.coeFn_sub (secondMultiplier χ hχ hc v (value F))
      (derivativeMultiplier χ hχ hc v (component v hmem F)),
    value_ae F, component_ae v hmem F] with τ hd hs2 hs1 hsub hv hcomp
  simp only [Pi.sub_apply] at hsub
  change secondMultiplier χ hχ hc v (value F) τ = _ at hs2
  change derivativeMultiplier χ hχ hc v (component v hmem F) τ = _ at hs1
  rw [hd, hsub, hs2, hs1, hv, hcomp]
  change -((τ.im : ℂ) ^ 2) *
      fderiv ℝ (fun z => frameProductCoefficient χ v z * F.val z) τ v = _
  rw [cutoff_fderiv_apply (frameProductCoefficient_smooth χ hχ v)
    (frameProductCoefficient_support χ hs v)]
  have hderiv : fderiv ℝ (frameProductCoefficient χ v) τ v =
      (fderiv ℝ (fun w => fderiv ℝ χ w v) τ v : ℂ) :=
    fderiv_realTest _ (contDiff_testDerivative χ hχ v) τ v
  rw [hderiv]
  simp only [frameProductCoefficient, directional, Complex.ofReal_neg,
    Complex.ofReal_mul, Complex.ofReal_pow, UpperHalfPlane.coe_im]
  ring

private theorem derivativeMultiplier_pairing_of_frame (χ : ℂ → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ modularInterior)
    (v : ℂ) (hmem : ∀ F : smoothCore, MemLp (directional F.val v) 2 modularMeasure)
    (F : smoothCore) (u gu : ModularHilbert)
    (hpair : inner ℂ
        (complexFrameTest (frameProductTest χ v F) (frameProductTest_smooth χ hχ hs v F)
          (frameProductTest_compact χ hc v F)) gu =
      inner ℂ
        (complexDivergenceTest (frameProductTest χ v F) (frameProductTest_smooth χ hχ hs v F)
          (frameProductTest_compact χ hc v F) v) u) :
    inner ℂ (derivativeMultiplier χ hχ hc v u) (component v hmem F) =
      inner ℂ (secondMultiplier χ hχ hc v u) (value F) -
        inner ℂ (derivativeMultiplier χ hχ hc v gu) (value F) := by
  rw [frameProductTest_frame χ hχ hc hs v F,
    frameProductTest_divergence χ hχ hc hs v hmem F] at hpair
  have h := congrArg (starRingEnd ℂ) hpair
  simp only [inner_conj_symm, inner_sub_right] at h
  rw [← derivativeMultiplier_inner χ hχ hc v, ← secondMultiplier_inner χ hχ hc v,
    ← derivativeMultiplier_inner χ hχ hc v] at h
  linear_combination h

/-- Actual integration by parts for the horizontal cutoff derivative. -/
theorem derivativeMultiplier_ibp_x (χ : ℂ → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ modularInterior)
    (u : FormDomain) (F : smoothCore) :
    inner ℂ (derivativeMultiplier χ hχ hc 1 (formEmbedding u)) (xComponent F) =
      inner ℂ (secondMultiplier χ hχ hc 1 (formEmbedding u)) (value F) -
        inner ℂ (derivativeMultiplier χ hχ hc 1 (formGradient u).fst) (value F) := by
  apply derivativeMultiplier_pairing_of_frame χ hχ hc hs 1
    (fun F => F.property.2.2.2.1) F
  have h := complexFrameTest_closedGradient_pairing_x (frameProductTest χ 1 F)
    (frameProductTest_smooth χ hχ hs 1 F) (frameProductTest_compact χ hc 1 F)
    (frameProductTest_support χ hs 1 F)
    ⟨formEmbedding u, Dirichlet.gradientEmbedding_mem_domain closedGradient u⟩
  simpa only [← Dirichlet.gradientValue_apply, WithLp.ofLp_fst, WithLp.ofLp_snd] using h

/-- Actual integration by parts for the vertical cutoff derivative. -/
theorem derivativeMultiplier_ibp_y (χ : ℂ → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ modularInterior)
    (u : FormDomain) (F : smoothCore) :
    inner ℂ (derivativeMultiplier χ hχ hc Complex.I (formEmbedding u)) (yComponent F) =
      inner ℂ (secondMultiplier χ hχ hc Complex.I (formEmbedding u)) (value F) -
        inner ℂ (derivativeMultiplier χ hχ hc Complex.I (formGradient u).snd) (value F) := by
  apply derivativeMultiplier_pairing_of_frame χ hχ hc hs Complex.I
    (fun F => F.property.2.2.2.2) F
  have h := complexFrameTest_closedGradient_pairing_y (frameProductTest χ Complex.I F)
    (frameProductTest_smooth χ hχ hs Complex.I F) (frameProductTest_compact χ hc Complex.I F)
    (frameProductTest_support χ hs Complex.I F)
    ⟨formEmbedding u, Dirichlet.gradientEmbedding_mem_domain closedGradient u⟩
  simpa only [← Dirichlet.gradientValue_apply, WithLp.ofLp_fst, WithLp.ofLp_snd] using h

end GapFamily.Analytic.ModularGradient.InteriorCutoff
