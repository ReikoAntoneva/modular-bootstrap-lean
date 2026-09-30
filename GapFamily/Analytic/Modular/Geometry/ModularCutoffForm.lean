import GapFamily.Analytic.Modular.Elliptic.ModularInteriorCompactSmooth
import GapFamily.Analytic.Modular.Elliptic.ModularInteriorCompactCore
import GapFamily.Analytic.Modular.Periodization.ModularPeriodizationDensity
import Mathlib.Analysis.Normed.Operator.Extend
import GapFamily.Analytic.Modular.Geometry.ModularCutoffMultiplier

noncomputable section
namespace GapFamily.Analytic.ModularGradient
open Set MeasureTheory UpperHalfPlane
open scoped ContDiff

def interiorCutoffCore (χ : ℂ → ℂ) (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ modularInterior)
    (F : smoothCore) : smoothCore :=
  periodizedCore (fun z => χ z * F.val z) (cutoff_contDiff hχ hs F)
    (cutoff_hasCompactSupport hc F) ((cutoff_tsupport_subset χ F).trans hs)

theorem interiorCutoffCore_value_ae (χ : ℂ → ℂ) (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ modularInterior)
    (F : smoothCore) :
    value (interiorCutoffCore χ hχ hc hs F) =ᵐ[modularMeasure]
      fun τ : UpperHalfPlane => χ τ * F.val τ :=
  value_periodizedCore_ae _ _ _ _

theorem interiorCutoffCore_component_ae (χ : ℂ → ℂ) (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ modularInterior)
    (v : ℂ) (hmem : ∀ F : smoothCore, MemLp (directional F.val v) 2 modularMeasure)
    (F : smoothCore) :
    component v hmem (interiorCutoffCore χ hχ hc hs F) =ᵐ[modularMeasure]
      fun τ : UpperHalfPlane => χ τ * directional F.val v τ +
        ((τ.im : ℂ) * fderiv ℝ χ τ v) * F.val τ := by
  have h := (component_ae v hmem (interiorCutoffCore χ hχ hc hs F)).trans
    (modularPeriodization_directional_ae (cutoff_contDiff hχ hs F)
      (cutoff_hasCompactSupport hc F) ((cutoff_tsupport_subset χ F).trans hs) v)
  filter_upwards [h] with τ hτ
  rw [hτ, directional, cutoff_fderiv_apply hχ hs]
  unfold directional
  ring

def interiorCutoffCoreFormMap (χ : ℂ → ℂ) (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ modularInterior) :
    smoothCore →ₗ[ℂ] FormDomain where
  toFun F := coreForm (interiorCutoffCore χ hχ hc hs F)
  map_add' F G := by
    apply formEmbedding_injective
    simp only [map_add, formEmbedding_coreForm]
    apply Lp.ext
    filter_upwards [interiorCutoffCore_value_ae χ hχ hc hs (F + G),
      interiorCutoffCore_value_ae χ hχ hc hs F,
      interiorCutoffCore_value_ae χ hχ hc hs G,
      Lp.coeFn_add (value (interiorCutoffCore χ hχ hc hs F))
        (value (interiorCutoffCore χ hχ hc hs G))] with τ hsum hF hG hadd
    rw [hsum, hadd]
    simp only [Pi.add_apply, hF, hG, Submodule.coe_add, mul_add]
  map_smul' c F := by
    apply formEmbedding_injective
    simp only [map_smul, formEmbedding_coreForm, RingHom.id_apply]
    apply Lp.ext
    filter_upwards [interiorCutoffCore_value_ae χ hχ hc hs (c • F),
      interiorCutoffCore_value_ae χ hχ hc hs F,
      Lp.coeFn_smul c (value (interiorCutoffCore χ hχ hc hs F))] with τ hsmul hF hcoe
    rw [hsmul, hcoe]
    simp only [Pi.smul_apply, hF, Submodule.coe_smul, smul_eq_mul]
    ring


theorem interiorCutoffCore_value (χ : ℂ → ℂ) (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ modularInterior)
    (F : smoothCore) :
    value (interiorCutoffCore χ hχ hc hs F) =
      modularCutoffMultiplier χ hχ.continuous hc (value F) := by
  apply Lp.ext
  filter_upwards [interiorCutoffCore_value_ae χ hχ hc hs F,
    modularCutoffMultiplier_ae χ hχ.continuous hc (value F), value_ae F]
    with τ hp hm hF
  rw [hp, hm, hF]

theorem interiorCutoffCore_component (χ : ℂ → ℂ) (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ modularInterior)
    (v : ℂ) (hmem : ∀ F : smoothCore, MemLp (directional F.val v) 2 modularMeasure)
    (F : smoothCore) :
    component v hmem (interiorCutoffCore χ hχ hc hs F) =
      modularCutoffMultiplier χ hχ.continuous hc (component v hmem F) +
      modularCutoffDirectionalMultiplier χ hχ hc v (value F) := by
  apply Lp.ext
  filter_upwards [interiorCutoffCore_component_ae χ hχ hc hs v hmem F,
    modularCutoffMultiplier_ae χ hχ.continuous hc (component v hmem F),
    modularCutoffDirectionalMultiplier_ae χ hχ hc v (value F),
    component_ae v hmem F, value_ae F,
    Lp.coeFn_add (modularCutoffMultiplier χ hχ.continuous hc (component v hmem F))
      (modularCutoffDirectionalMultiplier χ hχ hc v (value F))]
    with τ hp hm hd hF hv hsum
  rw [hp, hsum]
  simp only [Pi.add_apply, hm, hd, hF, hv]

def interiorCutoffJet (χ : ℂ → ℂ) (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) :
    FormDomain →L[ℂ] WithLp 2 (ModularHilbert × GradientSpace) :=
  let A := modularCutoffMultiplier χ hχ.continuous hc
  let Ax := modularCutoffDirectionalMultiplier χ hχ hc 1
  let Ay := modularCutoffDirectionalMultiplier χ hχ hc Complex.I
  let X := (WithLp.fstL 2 ℂ ModularHilbert ModularHilbert).comp formGradient
  let Y := (WithLp.sndL 2 ℂ ModularHilbert ModularHilbert).comp formGradient
  (WithLp.prodContinuousLinearEquiv 2 ℂ ModularHilbert GradientSpace).symm.toContinuousLinearMap.comp
    ((A.comp formEmbedding).prod
      ((WithLp.prodContinuousLinearEquiv 2 ℂ ModularHilbert ModularHilbert).symm.toContinuousLinearMap.comp
        ((A.comp X + Ax.comp formEmbedding).prod
          (A.comp Y + Ay.comp formEmbedding))))

theorem interiorCutoffJet_apply (χ : ℂ → ℂ) (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (u : FormDomain) :
    interiorCutoffJet χ hχ hc u = WithLp.toLp 2
      (modularCutoffMultiplier χ hχ.continuous hc (formEmbedding u),
        WithLp.toLp 2
          (modularCutoffMultiplier χ hχ.continuous hc (formGradient u).fst +
            modularCutoffDirectionalMultiplier χ hχ hc 1 (formEmbedding u),
           modularCutoffMultiplier χ hχ.continuous hc (formGradient u).snd +
            modularCutoffDirectionalMultiplier χ hχ hc Complex.I (formEmbedding u))) := rfl

theorem interiorCutoffJet_coreForm (χ : ℂ → ℂ) (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ modularInterior) (F : smoothCore) :
    interiorCutoffJet χ hχ hc (coreForm F) =
      (coreForm (interiorCutoffCore χ hχ hc hs F)).val := by
  apply (WithLp.linearEquiv 2 ℂ (ModularHilbert × GradientSpace)).injective
  apply Prod.ext
  · change modularCutoffMultiplier χ hχ.continuous hc (value F) =
      value (interiorCutoffCore χ hχ hc hs F)
    exact (interiorCutoffCore_value χ hχ hc hs F).symm
  · change WithLp.toLp 2
        (modularCutoffMultiplier χ hχ.continuous hc (formGradient (coreForm F)).fst +
          modularCutoffDirectionalMultiplier χ hχ hc 1 (value F),
         modularCutoffMultiplier χ hχ.continuous hc (formGradient (coreForm F)).snd +
          modularCutoffDirectionalMultiplier χ hχ hc Complex.I (value F)) =
        formGradient (coreForm (interiorCutoffCore χ hχ hc hs F))
    rw [formGradient_coreForm, formGradient_coreForm]
    apply (WithLp.linearEquiv 2 ℂ (ModularHilbert × ModularHilbert)).injective
    apply Prod.ext
    · exact (interiorCutoffCore_component χ hχ hc hs 1 _ F).symm
    · exact (interiorCutoffCore_component χ hχ hc hs Complex.I _ F).symm

theorem interiorCutoffJet_mem (χ : ℂ → ℂ) (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ modularInterior) (u : FormDomain) :
    interiorCutoffJet χ hχ hc u ∈ Dirichlet.gradientGraph closedGradient := by
  refine coreForm_denseRange.induction_on (p := fun u : FormDomain =>
    interiorCutoffJet χ hχ hc u ∈ Dirichlet.gradientGraph closedGradient) u ?_ ?_
  · exact (Dirichlet.gradientGraph_isClosed closedGradient closedGradient_isClosed).preimage
      (interiorCutoffJet χ hχ hc).continuous
  · intro F
    rw [interiorCutoffJet_coreForm χ hχ hc hs]
    exact (coreForm (interiorCutoffCore χ hχ hc hs F)).property

def interiorCutoffForm (χ : ℂ → ℂ) (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ modularInterior) :
    FormDomain →L[ℂ] FormDomain :=
  (interiorCutoffJet χ hχ hc).codRestrict (Dirichlet.gradientGraph closedGradient)
    (interiorCutoffJet_mem χ hχ hc hs)

theorem interiorCutoffForm_coreForm (χ : ℂ → ℂ) (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ modularInterior) (F : smoothCore) :
    interiorCutoffForm χ hχ hc hs (coreForm F) =
      coreForm (interiorCutoffCore χ hχ hc hs F) :=
  Subtype.ext (interiorCutoffJet_coreForm χ hχ hc hs F)

theorem interiorCutoffForm_value (χ : ℂ → ℂ) (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ modularInterior) (u : FormDomain) :
    formEmbedding (interiorCutoffForm χ hχ hc hs u) =
      modularCutoffMultiplier χ hχ.continuous hc (formEmbedding u) := rfl

theorem interiorCutoffForm_gradient (χ : ℂ → ℂ) (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ modularInterior) (u : FormDomain) :
    formGradient (interiorCutoffForm χ hχ hc hs u) = WithLp.toLp 2
      (modularCutoffMultiplier χ hχ.continuous hc (formGradient u).fst +
        modularCutoffDirectionalMultiplier χ hχ hc 1 (formEmbedding u),
       modularCutoffMultiplier χ hχ.continuous hc (formGradient u).snd +
        modularCutoffDirectionalMultiplier χ hχ hc Complex.I (formEmbedding u)) := rfl

theorem interiorCutoffForm_norm_le (χ : ℂ → ℂ) (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ modularInterior) (u : FormDomain) :
    ‖interiorCutoffForm χ hχ hc hs u‖ ≤ ‖interiorCutoffJet χ hχ hc‖ * ‖u‖ :=
  (interiorCutoffJet χ hχ hc).le_opNorm u

/-- The completed multiplier has its literal almost-everywhere value on the fundamental domain. -/
theorem interiorCutoffForm_value_ae (χ : ℂ → ℂ) (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ modularInterior) (u : FormDomain) :
    formEmbedding (interiorCutoffForm χ hχ hc hs u) =ᵐ[modularMeasure]
      fun τ : UpperHalfPlane => χ τ * formEmbedding u τ :=
  modularCutoffMultiplier_ae χ hχ.continuous hc (formEmbedding u)

/-- The coefficient is the genuine smooth automorphic periodization of the compact cutoff. -/
theorem interiorCutoffForm_periodized_value_ae (χ : ℂ → ℂ) (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ modularInterior) (u : FormDomain) :
    formEmbedding (interiorCutoffForm χ hχ hc hs u) =ᵐ[modularMeasure]
      fun τ : UpperHalfPlane => (periodizedCore χ hχ hc hs).val τ * formEmbedding u τ := by
  filter_upwards [interiorCutoffForm_value_ae χ hχ hc hs u,
    modularPeriodization_ae hs] with τ hm hχτ
  exact hm.trans (congrArg (fun c : ℂ => c * formEmbedding u τ) hχτ.symm)

theorem interiorCutoffForm_opNorm_le (χ : ℂ → ℂ) (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ modularInterior) :
    ‖interiorCutoffForm χ hχ hc hs‖ ≤ ‖interiorCutoffJet χ hχ hc‖ := by
  have h := (interiorCutoffForm χ hχ hc hs).opNorm_le_bound
    (norm_nonneg (interiorCutoffJet χ hχ hc)) (interiorCutoffForm_norm_le χ hχ hc hs)
  exact h

end GapFamily.Analytic.ModularGradient
