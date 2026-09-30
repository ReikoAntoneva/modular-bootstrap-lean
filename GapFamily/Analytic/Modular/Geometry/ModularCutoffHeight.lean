import GapFamily.Analytic.Modular.Geometry.ModularCutoffLaplacian
import GapFamily.Analytic.Modular.Geometry.ModularTruncatedIndicator

/-!
# Height absorption for actual interior cutoff multipliers

Multiplication by a compact coefficient below a fixed height absorbs the
ordinary low-height projection. The actual first and second cutoff derivative
coefficients inherit this support bound, so the completed form product and
physical Laplacian commutator can use the truncated value and gradient fields.
-/

noncomputable section

namespace GapFamily.Analytic

open Set MeasureTheory UpperHalfPlane
open scoped ContDiff

/-- A supported coefficient absorbs the actual low-height indicator on its input. -/
theorem modularCutoffMultiplier_comp_lowCut (a : ℂ → ℂ) (ha : Continuous a)
    (hc : HasCompactSupport a) (H : ℝ) (hH : tsupport a ⊆ {z : ℂ | z.im ≤ H}) :
    (modularCutoffMultiplier a ha hc).comp (modularLowCut H) =
      modularCutoffMultiplier a ha hc := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [modularCutoffMultiplier_ae a ha hc (modularLowCut H f),
    modularCutoffMultiplier_ae a ha hc f, modularLowCut_ae H f] with τ hleft hright hcut
  change modularCutoffMultiplier a ha hc (modularLowCut H f) τ =
    modularCutoffMultiplier a ha hc f τ
  rw [hleft, hright, hcut]
  by_cases hτ : τ.im ≤ H
  · simp [hτ]
  · have ha0 : a τ = 0 := image_eq_zero_of_notMem_tsupport (fun ht => hτ (hH ht))
    simp [ha0]

namespace ModularGradient.InteriorCutoff

theorem realMultiplier_comp_lowCut (a : ℂ → ℝ) (ha : Continuous a)
    (hc : HasCompactSupport a) (H : ℝ) (hH : tsupport a ⊆ {z : ℂ | z.im ≤ H}) :
    (realMultiplier a ha hc).comp (modularLowCut H) = realMultiplier a ha hc :=
  modularCutoffMultiplier_comp_lowCut _ _ _ H
    ((tsupport_comp_subset Complex.ofReal_zero a).trans hH)

/-- The hyperbolic first derivative coefficient has no support outside the cutoff. -/
theorem derivativeCoefficient_tsupport_subset (χ : ℂ → ℝ) (v : ℂ) :
    tsupport (fun z => z.im * fderiv ℝ χ z v) ⊆ tsupport χ :=
  tsupport_mul_subset_right.trans (tsupport_fderiv_apply_subset ℝ (f := χ) v)

/-- The second coefficient also has support inside the original cutoff. -/
theorem secondCoefficient_tsupport_subset (χ : ℂ → ℝ) (v : ℂ) :
    tsupport (fun z => -(z.im ^ 2 * fderiv ℝ (fun w => fderiv ℝ χ w v) z v)) ⊆
      tsupport χ := by
  rw [tsupport_fun_neg]
  exact tsupport_mul_subset_right.trans
    ((tsupport_fderiv_apply_subset ℝ (f := fun w => fderiv ℝ χ w v) v).trans
      (tsupport_fderiv_apply_subset ℝ (f := χ) v))

theorem valueMultiplier_comp_lowCut (χ : ℂ → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (H : ℝ) (hH : tsupport χ ⊆ {z : ℂ | z.im ≤ H}) :
    (valueMultiplier χ hχ hc).comp (modularLowCut H) = valueMultiplier χ hχ hc :=
  realMultiplier_comp_lowCut χ hχ.continuous hc H hH

theorem derivativeMultiplier_comp_lowCut (χ : ℂ → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (v : ℂ) (H : ℝ)
    (hH : tsupport χ ⊆ {z : ℂ | z.im ≤ H}) :
    (derivativeMultiplier χ hχ hc v).comp (modularLowCut H) =
      derivativeMultiplier χ hχ hc v :=
  realMultiplier_comp_lowCut _ _ _ H ((derivativeCoefficient_tsupport_subset χ v).trans hH)

theorem secondMultiplier_comp_lowCut (χ : ℂ → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (v : ℂ) (H : ℝ)
    (hH : tsupport χ ⊆ {z : ℂ | z.im ≤ H}) :
    (secondMultiplier χ hχ hc v).comp (modularLowCut H) = secondMultiplier χ hχ hc v :=
  realMultiplier_comp_lowCut _ _ _ H ((secondCoefficient_tsupport_subset χ v).trans hH)

theorem valueMultiplier_lowCut (χ : ℂ → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (H : ℝ) (hH : tsupport χ ⊆ {z : ℂ | z.im ≤ H})
    (f : ModularHilbert) :
    valueMultiplier χ hχ hc (modularLowCut H f) = valueMultiplier χ hχ hc f :=
  congrArg (fun T : ModularHilbert →L[ℂ] ModularHilbert => T f)
    (valueMultiplier_comp_lowCut χ hχ hc H hH)

theorem derivativeMultiplier_lowCut (χ : ℂ → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (v : ℂ) (H : ℝ)
    (hH : tsupport χ ⊆ {z : ℂ | z.im ≤ H}) (f : ModularHilbert) :
    derivativeMultiplier χ hχ hc v (modularLowCut H f) = derivativeMultiplier χ hχ hc v f :=
  congrArg (fun T : ModularHilbert →L[ℂ] ModularHilbert => T f)
    (derivativeMultiplier_comp_lowCut χ hχ hc v H hH)

theorem secondMultiplier_lowCut (χ : ℂ → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (v : ℂ) (H : ℝ)
    (hH : tsupport χ ⊆ {z : ℂ | z.im ≤ H}) (f : ModularHilbert) :
    secondMultiplier χ hχ hc v (modularLowCut H f) = secondMultiplier χ hχ hc v f :=
  congrArg (fun T : ModularHilbert →L[ℂ] ModularHilbert => T f)
    (secondMultiplier_comp_lowCut χ hχ hc v H hH)

/-- The actual form-cutoff value is reconstructed from the low-height value. -/
theorem formMultiplier_value_lowCut (χ : ℂ → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ modularInterior) (H : ℝ)
    (hH : tsupport χ ⊆ {z : ℂ | z.im ≤ H}) (u : FormDomain) :
    formEmbedding (formMultiplier χ hχ hc hs u) =
      valueMultiplier χ hχ hc (modularLowCut H (formEmbedding u)) := by
  rw [valueMultiplier_lowCut χ hχ hc H hH]
  exact formMultiplier_value χ hχ hc hs u

/-- Both actual gradient components are reconstructed from their low-height fields. -/
theorem formMultiplier_gradient_lowCut (χ : ℂ → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ modularInterior) (H : ℝ)
    (hH : tsupport χ ⊆ {z : ℂ | z.im ≤ H}) (u : FormDomain) :
    formGradient (formMultiplier χ hχ hc hs u) = WithLp.toLp 2
      (valueMultiplier χ hχ hc (modularLowCut H (formGradient u).fst) +
        derivativeMultiplier χ hχ hc 1 (modularLowCut H (formEmbedding u)),
       valueMultiplier χ hχ hc (modularLowCut H (formGradient u).snd) +
        derivativeMultiplier χ hχ hc Complex.I (modularLowCut H (formEmbedding u))) := by
  simp only [valueMultiplier_lowCut χ hχ hc H hH,
    derivativeMultiplier_lowCut χ hχ hc 1 H hH,
    derivativeMultiplier_lowCut χ hχ hc Complex.I H hH]
  exact formMultiplier_gradient χ hχ hc hs u

/-- The physical commutator uses only low-height value, gradient, and source fields. -/
theorem commutatorValue_lowCut (χ : ℂ → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (H : ℝ) (hH : tsupport χ ⊆ {z : ℂ | z.im ≤ H})
    (u : laplacian.domain) :
    commutatorValue χ hχ hc u =
      valueMultiplier χ hχ hc (modularLowCut H (laplacian u)) +
      secondMultiplier χ hχ hc 1 (modularLowCut H u) +
      secondMultiplier χ hχ hc Complex.I (modularLowCut H u) -
      (2 : ℂ) •
        (derivativeMultiplier χ hχ hc 1 (modularLowCut H (formGradient (operatorForm u)).fst) +
         derivativeMultiplier χ hχ hc Complex.I
           (modularLowCut H (formGradient (operatorForm u)).snd)) := by
  simp only [valueMultiplier_lowCut χ hχ hc H hH,
    secondMultiplier_lowCut χ hχ hc 1 H hH,
    secondMultiplier_lowCut χ hχ hc Complex.I H hH,
    derivativeMultiplier_lowCut χ hχ hc 1 H hH,
    derivativeMultiplier_lowCut χ hχ hc Complex.I H hH]
  rfl

end ModularGradient.InteriorCutoff
end GapFamily.Analytic
