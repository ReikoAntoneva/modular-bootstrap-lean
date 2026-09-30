import GapFamily.Analytic.Modular.Geometry.ModularCutoffForm
import GapFamily.Analytic.Modular.ModularLaplacianTest

noncomputable section
namespace GapFamily.Analytic.ModularGradient.InteriorCutoff
open Set MeasureTheory UpperHalfPlane
open scoped ContDiff ComplexConjugate

def realMultiplier (a : ℂ → ℝ) (ha : Continuous a) (hc : HasCompactSupport a) :
    ModularHilbert →L[ℂ] ModularHilbert :=
  modularCutoffMultiplier (fun z => (a z : ℂ)) (Complex.continuous_ofReal.comp ha)
    (hc.comp_left Complex.ofReal_zero)

theorem realMultiplier_ae (a : ℂ → ℝ) (ha : Continuous a) (hc : HasCompactSupport a)
    (f : ModularHilbert) : realMultiplier a ha hc f =ᵐ[modularMeasure]
      fun τ : UpperHalfPlane => (a τ : ℂ) * f τ :=
  modularCutoffMultiplier_ae _ _ _ _

theorem realMultiplier_inner (a : ℂ → ℝ) (ha : Continuous a) (hc : HasCompactSupport a)
    (f g : ModularHilbert) :
    inner ℂ (realMultiplier a ha hc f) g = inner ℂ f (realMultiplier a ha hc g) := by
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [realMultiplier_ae a ha hc f, realMultiplier_ae a ha hc g] with τ hf hg
  simp only [hf, hg, RCLike.inner_apply, map_mul, Complex.conj_ofReal]
  ring

def valueMultiplier (χ : ℂ → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) :=
  realMultiplier χ hχ.continuous hc

def derivativeMultiplier (χ : ℂ → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (v : ℂ) : ModularHilbert →L[ℂ] ModularHilbert :=
  realMultiplier (fun z => z.im * fderiv ℝ χ z v)
    (Complex.continuous_im.mul (continuous_testDerivative χ hχ v))
    (hc.fderiv_apply ℝ v).mul_left

def secondMultiplier (χ : ℂ → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (v : ℂ) : ModularHilbert →L[ℂ] ModularHilbert :=
  realMultiplier (fun z => -(z.im ^ 2 * fderiv ℝ (fun w => fderiv ℝ χ w v) z v))
    (((Complex.continuous_im.pow 2).mul
      (continuous_testDerivative _ (contDiff_testDerivative χ hχ v) v)).neg)
    (compactSupport_testDivergence _ (hc.fderiv_apply ℝ v) v)

theorem valueMultiplier_inner (χ : ℂ → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (f g : ModularHilbert) :
    inner ℂ (valueMultiplier χ hχ hc f) g = inner ℂ f (valueMultiplier χ hχ hc g) :=
  realMultiplier_inner _ _ _ _ _

theorem derivativeMultiplier_inner (χ : ℂ → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (v : ℂ) (f g : ModularHilbert) :
    inner ℂ (derivativeMultiplier χ hχ hc v f) g =
      inner ℂ f (derivativeMultiplier χ hχ hc v g) := realMultiplier_inner _ _ _ _ _

theorem secondMultiplier_inner (χ : ℂ → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (v : ℂ) (f g : ModularHilbert) :
    inner ℂ (secondMultiplier χ hχ hc v f) g =
      inner ℂ f (secondMultiplier χ hχ hc v g) := realMultiplier_inner _ _ _ _ _

theorem derivativeMultiplier_eq (χ : ℂ → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (v : ℂ) :
    modularCutoffDirectionalMultiplier (fun z => (χ z : ℂ))
      (Complex.ofRealCLM.contDiff.comp hχ) (hc.comp_left Complex.ofReal_zero) v =
      derivativeMultiplier χ hχ hc v := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [modularCutoffDirectionalMultiplier_ae (fun z => (χ z : ℂ))
      (Complex.ofRealCLM.contDiff.comp hχ) (hc.comp_left Complex.ofReal_zero) v f,
    realMultiplier_ae (fun z => z.im * fderiv ℝ χ z v)
      (Complex.continuous_im.mul (continuous_testDerivative χ hχ v))
      (hc.fderiv_apply ℝ v).mul_left f] with τ hleft hright
  change derivativeMultiplier χ hχ hc v f τ = _ at hright
  rw [hleft, hright, fderiv_realTest χ hχ]
  simp only [Complex.ofReal_mul]
  rfl

def formMultiplier (χ : ℂ → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ modularInterior) :
    FormDomain →L[ℂ] FormDomain :=
  interiorCutoffForm (fun z => (χ z : ℂ)) (Complex.ofRealCLM.contDiff.comp hχ)
    (hc.comp_left Complex.ofReal_zero) ((tsupport_comp_subset Complex.ofReal_zero χ).trans hs)

theorem formMultiplier_value (χ : ℂ → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ modularInterior) (u : FormDomain) :
    formEmbedding (formMultiplier χ hχ hc hs u) = valueMultiplier χ hχ hc (formEmbedding u) := rfl

theorem formMultiplier_gradient (χ : ℂ → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ modularInterior) (u : FormDomain) :
    formGradient (formMultiplier χ hχ hc hs u) = WithLp.toLp 2
      (valueMultiplier χ hχ hc (formGradient u).fst +
        derivativeMultiplier χ hχ hc 1 (formEmbedding u),
       valueMultiplier χ hχ hc (formGradient u).snd +
        derivativeMultiplier χ hχ hc Complex.I (formEmbedding u)) := by
  have h := interiorCutoffForm_gradient (fun z => (χ z : ℂ))
    (Complex.ofRealCLM.contDiff.comp hχ) (hc.comp_left Complex.ofReal_zero)
    ((tsupport_comp_subset Complex.ofReal_zero χ).trans hs) u
  rw [derivativeMultiplier_eq, derivativeMultiplier_eq] at h
  exact h

end GapFamily.Analytic.ModularGradient.InteriorCutoff
