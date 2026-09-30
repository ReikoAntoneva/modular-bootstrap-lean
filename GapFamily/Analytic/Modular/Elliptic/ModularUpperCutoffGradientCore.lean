import GapFamily.Analytic.Modular.Elliptic.ModularInteriorCompactUpperSmooth
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Literal cutoff derivatives of the smooth modular core

The coefficient is compactly supported anywhere in the upper half-plane,
including across modular seams. The output is the ordinary Euclidean L² class
of the cutoff times the derivative of the original core function.
-/

noncomputable section
namespace GapFamily.Analytic.ModularGradient
open Set MeasureTheory UpperHalfPlane
open scoped ContDiff

/-- The derivative of the core need only be continuous on the upper half-plane:
the cutoff vanishes locally at every other point. -/
theorem continuous_upperCutoffGradient {χ : ℂ → ℂ} (hχ : ContDiff ℝ ∞ χ)
    (hs : tsupport χ ⊆ upperHalfPlaneSet) (F : smoothCore) (v : ℂ) :
    Continuous (fun z => χ z * fderiv ℝ F.val z v) := by
  have hD : ContinuousOn (fun z => fderiv ℝ F.val z v) upperHalfPlaneSet :=
    (F.property.1.continuousOn_fderiv_of_isOpen isOpen_upperHalfPlaneSet (by simp)).clm_apply
      continuousOn_const
  rw [continuous_iff_continuousAt]
  intro z
  by_cases hz : z ∈ tsupport χ
  · exact hχ.continuous.continuousAt.mul (hD.continuousAt
      (isOpen_upperHalfPlaneSet.mem_nhds (hs hz)))
  · apply (continuousAt_const (y := (0 : ℂ))).congr_of_eventuallyEq
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hz] with w hw
    simp [hw]

/-- The literal cutoff derivative has genuine finite ordinary Euclidean L² norm. -/
theorem memLp_upperCutoffGradient (χ : ℂ → ℂ) (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ upperHalfPlaneSet)
    (F : smoothCore) (v : ℂ) :
    MemLp (fun z => χ z * fderiv ℝ F.val z v) 2 (volume : Measure ℂ) :=
  (continuous_upperCutoffGradient hχ hs F v).memLp_of_hasCompactSupport hc.mul_right

private def upperCutoffGradientValue (χ : ℂ → ℂ) (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ upperHalfPlaneSet)
    (v : ℂ) (F : smoothCore) : Lp ℂ 2 (volume : Measure ℂ) :=
  (memLp_upperCutoffGradient χ hχ hc hs F v).toLp _

private theorem upperCutoffGradientValue_ae (χ : ℂ → ℂ) (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ upperHalfPlaneSet)
    (v : ℂ) (F : smoothCore) :
    upperCutoffGradientValue χ hχ hc hs v F =ᵐ[volume]
      (fun z : ℂ => χ z * fderiv ℝ F.val z v) := MemLp.coeFn_toLp _

/-- The actual core-linear map into global Euclidean L² of `χ ∂ᵥF`. -/
def upperCutoffGradientCoreMap (χ : ℂ → ℂ) (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ upperHalfPlaneSet)
    (v : ℂ) : smoothCore →ₗ[ℂ] Lp ℂ 2 (volume : Measure ℂ) where
  toFun := upperCutoffGradientValue χ hχ hc hs v
  map_add' F G := by
    apply Lp.ext
    filter_upwards [upperCutoffGradientValue_ae χ hχ hc hs v (F + G),
      upperCutoffGradientValue_ae χ hχ hc hs v F,
      upperCutoffGradientValue_ae χ hχ hc hs v G,
      Lp.coeFn_add (upperCutoffGradientValue χ hχ hc hs v F)
        (upperCutoffGradientValue χ hχ hc hs v G)] with z hsum hF hG hadd
    simp only [Pi.add_apply] at hadd
    rw [hsum, hadd, hF, hG]
    by_cases hz : z ∈ tsupport χ
    · have hdF := smooth_differentiableAt F.property.1 (⟨z, hs hz⟩ : UpperHalfPlane)
      have hdG := smooth_differentiableAt G.property.1 (⟨z, hs hz⟩ : UpperHalfPlane)
      simp only [Submodule.coe_add]
      rw [fderiv_add hdF hdG]
      simp only [add_apply, mul_add]
    · simp [image_eq_zero_of_notMem_tsupport hz]
  map_smul' c F := by
    apply Lp.ext
    filter_upwards [upperCutoffGradientValue_ae χ hχ hc hs v (c • F),
      upperCutoffGradientValue_ae χ hχ hc hs v F,
      Lp.coeFn_smul c (upperCutoffGradientValue χ hχ hc hs v F)] with z hsm hF hcoe
    simp only [Pi.smul_apply, smul_eq_mul] at hcoe
    simp only [RingHom.id_apply]
    rw [hsm, hcoe, hF]
    by_cases hz : z ∈ tsupport χ
    · have hdF := smooth_differentiableAt F.property.1 (⟨z, hs hz⟩ : UpperHalfPlane)
      simp only [Submodule.coe_smul]
      rw [fderiv_const_smul hdF]
      simp only [smul_apply, smul_eq_mul]
      ring
    · simp [image_eq_zero_of_notMem_tsupport hz]

theorem upperCutoffGradientCoreMap_ae (χ : ℂ → ℂ) (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ upperHalfPlaneSet)
    (v : ℂ) (F : smoothCore) :
    upperCutoffGradientCoreMap χ hχ hc hs v F =ᵐ[volume]
      (fun z : ℂ => χ z * fderiv ℝ F.val z v) :=
  upperCutoffGradientValue_ae χ hχ hc hs v F

/-- The actual Euclidean L² norm is the global ordinary derivative integral. -/
theorem upperCutoffGradientCoreMap_norm_sq (χ : ℂ → ℂ) (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ upperHalfPlaneSet)
    (v : ℂ) (F : smoothCore) :
    ‖upperCutoffGradientCoreMap χ hχ hc hs v F‖ ^ 2 =
      ∫ z : ℂ, ‖χ z * fderiv ℝ F.val z v‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [upperCutoffGradientCoreMap_ae χ hχ hc hs v F] with z hz
  simp only [hz, real_inner_self_eq_norm_sq]

end GapFamily.Analytic.ModularGradient
