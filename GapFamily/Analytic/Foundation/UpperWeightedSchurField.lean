import GapFamily.Analytic.Foundation.UpperCutoffCommonHeight
import GapFamily.Analytic.Cusp.Profile.CuspWeightedSchurGradientPhysical
import Mathlib.Analysis.Normed.Operator.Prod

/-!
Scratch threshold analytic upper-chart value and gradient fields.
Only genuine finite-height recovery operators are used. Physical identities
identify the actual Schur form candidate; operator-domain/PDE membership is
not asserted on the full physical half-plane.
-/

noncomputable section
namespace GapFamily.Analytic.UpperWeighted
open Set MeasureTheory UpperHalfPlane ModularGradient CuspSchurLocal
open scoped ContDiff

abbrev UpperField := Lp ℂ 2 (volume : Measure ℂ)

/-- Bounded packaging of a pair of ambient gradient operators in its Hilbert norm. -/
def gradientPairOperator :
    ((ModularHilbert →L[ℂ] ModularHilbert) × (ModularHilbert →L[ℂ] ModularHilbert)) →L[ℂ]
      (ModularHilbert →L[ℂ] GradientSpace) :=
  ((ContinuousLinearMap.compL ℂ ModularHilbert (ModularHilbert × ModularHilbert)
    GradientSpace)
    (WithLp.prodContinuousLinearEquiv 2 ℂ ModularHilbert ModularHilbert).symm.toContinuousLinearMap).comp
      (ContinuousLinearMap.prodₗᵢ ℂ).toContinuousLinearEquiv.toContinuousLinearMap

@[simp] theorem gradientPairOperator_apply
    (A B : ModularHilbert →L[ℂ] ModularHilbert) (f : ModularHilbert) :
    gradientPairOperator (A, B) f = WithLp.toLp 2 (A f, B f) := rfl

/-- The norm-analytic pair of actual continued weighted output-gradient components. -/
def weightedGradientPair (α : ℝ) (hα : 0 ≤ α) (L : ℝ) (κ : ℂ) :
    ModularHilbert →L[ℂ] GradientSpace :=
  gradientPairOperator
    (CuspSchurWeighted.continuedLocalSchurGradientX α hα L L κ,
     CuspSchurWeighted.continuedLocalSchurGradientY α hα L L κ)

theorem weightedGradientPair_analyticAt_zero {α : ℝ} (hα : 0 < α) (L : ℝ) :
    AnalyticAt ℂ (weightedGradientPair α hα.le L) 0 := by
  have hp := ContinuousLinearMap.analyticAt (𝕜 := ℂ)
    (E := (ModularHilbert →L[ℂ] ModularHilbert) × (ModularHilbert →L[ℂ] ModularHilbert))
    (F := ModularHilbert →L[ℂ] GradientSpace) gradientPairOperator
    (CuspSchurWeighted.continuedLocalSchurGradientX α hα.le L L 0,
     CuspSchurWeighted.continuedLocalSchurGradientY α hα.le L L 0)
  exact hp.comp_of_eq
    ((CuspSchurWeighted.continuedLocalSchurGradientX_analyticAt_zero hα L L).prod
      (CuspSchurWeighted.continuedLocalSchurGradientY_analyticAt_zero hα L L)) rfl

theorem weightedGradientPair_eq_physical {α L : ℝ} (hα : 0 < α) (hL : 0 ≤ L)
    {κ : ℂ} (hκ : 0 < κ.re) (hp : κ ≠ (1 / 2 : ℂ)) (f : ModularHilbert) :
    weightedGradientPair α hα.le L κ f = gradientLowCut (Real.exp L)
      (formGradient (CuspSchur.actualSchurSolution (parameter κ)
        (cuspWeightedInput α hα.le f))) := by
  change WithLp.toLp 2
    (CuspSchurWeighted.continuedLocalSchurGradientX α hα.le L L κ f,
     CuspSchurWeighted.continuedLocalSchurGradientY α hα.le L L κ f) = _
  rw [CuspSchurWeighted.continuedLocalSchurGradientX_apply_eq_physical hα.le L L hκ hp,
    CuspSchurWeighted.continuedLocalSchurGradientY_apply_eq_physical hα hL hL le_rfl hκ hp]
  rfl

/-- The continued ordinary upper-chart value at a finite output collar. -/
def upperWeightedSchurValue (χ : ℂ → ℂ) (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ upperHalfPlaneSet)
    (α : ℝ) (hα : 0 ≤ α) (L : ℝ) (κ : ℂ) : ModularHilbert →L[ℂ] UpperField :=
  (upperCutoffHilbertValueOperator χ hχ hc hs).comp
    (CuspSchurWeighted.continuedLocalSchur α hα L L κ)

/-- A bounded actual gradient recovery map applied to the continued pair. -/
def upperWeightedSchurGradient (B : GradientSpace →L[ℂ] UpperField)
    (α : ℝ) (hα : 0 ≤ α) (L : ℝ) (κ : ℂ) : ModularHilbert →L[ℂ] UpperField :=
  B.comp (weightedGradientPair α hα L κ)

theorem upperWeightedSchurValue_analyticAt_zero
    (χ : ℂ → ℂ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ upperHalfPlaneSet) {α : ℝ} (hα : 0 < α) (L : ℝ) :
    AnalyticAt ℂ (upperWeightedSchurValue χ hχ hc hs α hα.le L) 0 := by
  let Q : (ModularHilbert →L[ℂ] ModularHilbert) →L[ℂ]
      (ModularHilbert →L[ℂ] UpperField) :=
    (ContinuousLinearMap.compL ℂ ModularHilbert ModularHilbert UpperField)
      (upperCutoffHilbertValueOperator χ hχ hc hs)
  have hQ := Q.analyticAt (CuspSchurWeighted.continuedLocalSchur α hα.le L L 0)
  exact hQ.comp_of_eq (CuspSchurWeighted.continuedLocalSchur_analyticAt_zero hα L L) rfl

theorem upperWeightedSchurGradient_analyticAt_zero
    (B : GradientSpace →L[ℂ] UpperField) {α : ℝ} (hα : 0 < α) (L : ℝ) :
    AnalyticAt ℂ (upperWeightedSchurGradient B α hα.le L) 0 := by
  let Q : (ModularHilbert →L[ℂ] GradientSpace) →L[ℂ]
      (ModularHilbert →L[ℂ] UpperField) :=
    (ContinuousLinearMap.compL ℂ ModularHilbert GradientSpace UpperField) B
  exact (Q.analyticAt (weightedGradientPair α hα.le L 0)).comp_of_eq
    (weightedGradientPair_analyticAt_zero hα L) rfl

/-- Conditional composition identity used only after the actual absorption
height has been constructed. -/
theorem upperWeightedSchurValue_eq_physical
    (χ : ℂ → ℂ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ upperHalfPlaneSet) {α L : ℝ} (hα : 0 < α) (hL : 0 ≤ L)
    (hvalue : (upperCutoffHilbertValueOperator χ hχ hc hs).comp
      (modularLowCut (Real.exp L)) = upperCutoffHilbertValueOperator χ hχ hc hs)
    {κ : ℂ} (hκ : 0 < κ.re) (hp : κ ≠ (1 / 2 : ℂ)) (f : ModularHilbert) :
    upperWeightedSchurValue χ hχ hc hs α hα.le L κ f =
      upperCutoffValueOperator χ hχ hc hs
        (CuspSchur.actualSchurSolution (parameter κ) (cuspWeightedInput α hα.le f)) := by
  rw [upperWeightedSchurValue,
    CuspSchurWeighted.continuedLocalSchur_eq_physical hα hL hL le_rfl hκ hp]
  change upperCutoffHilbertValueOperator χ hχ hc hs
    (modularLowCut (Real.exp L)
      (CuspSchur.actualSchurResolvent (parameter κ) (cuspWeightedInput α hα.le f))) = _
  have hv := congrArg (fun T : ModularHilbert →L[ℂ] UpperField =>
    T (CuspSchur.actualSchurResolvent (parameter κ) (cuspWeightedInput α hα.le f))) hvalue
  change upperCutoffHilbertValueOperator χ hχ hc hs
    (modularLowCut (Real.exp L)
      (CuspSchur.actualSchurResolvent (parameter κ) (cuspWeightedInput α hα.le f))) =
        upperCutoffHilbertValueOperator χ hχ hc hs
          (CuspSchur.actualSchurResolvent (parameter κ) (cuspWeightedInput α hα.le f)) at hv
  rw [hv, CuspSchur.actualSchurResolvent_apply, upperCutoffHilbertValueOperator_formEmbedding]

theorem upperWeightedSchurGradient_eq_physical
    (χ : ℂ → ℂ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ upperHalfPlaneSet) (v : ℂ)
    (B : GradientSpace →L[ℂ] UpperField) {α L : ℝ} (hα : 0 < α) (hL : 0 ≤ L)
    (hB : B.comp ((gradientLowCut (Real.exp L)).comp formGradient) =
      upperCutoffGradientOperator χ hχ hc hs v)
    {κ : ℂ} (hκ : 0 < κ.re) (hp : κ ≠ (1 / 2 : ℂ)) (f : ModularHilbert) :
    upperWeightedSchurGradient B α hα.le L κ f =
      upperCutoffGradientOperator χ hχ hc hs v
        (CuspSchur.actualSchurSolution (parameter κ) (cuspWeightedInput α hα.le f)) := by
  change B (weightedGradientPair α hα.le L κ f) = _
  rw [weightedGradientPair_eq_physical hα hL hκ hp]
  exact congrArg (fun T : FormDomain →L[ℂ] UpperField =>
    T (CuspSchur.actualSchurSolution (parameter κ) (cuspWeightedInput α hα.le f))) hB

/-- Actual threshold-analytic upper-chart fields for arbitrary exponentially
weighted Hilbert sources. The common height and recovery maps are constructed,
not supplied as compatibility assumptions. -/
theorem exists_upperWeightedSchur_fields
    (χ : ℂ → ℂ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ upperHalfPlaneSet) {α : ℝ} (hα : 0 < α) :
    ∃ L : ℝ, 0 ≤ L ∧ ∃ Bx By : GradientSpace →L[ℂ] UpperField,
      AnalyticAt ℂ (upperWeightedSchurValue χ hχ hc hs α hα.le L) 0 ∧
      AnalyticAt ℂ (upperWeightedSchurGradient Bx α hα.le L) 0 ∧
      AnalyticAt ℂ (upperWeightedSchurGradient By α hα.le L) 0 ∧
      ∀ κ : ℂ, 0 < κ.re → κ ≠ (1 / 2 : ℂ) → ∀ f : ModularHilbert,
        upperWeightedSchurValue χ hχ hc hs α hα.le L κ f =
          upperCutoffValueOperator χ hχ hc hs
            (CuspSchur.actualSchurSolution (parameter κ) (cuspWeightedInput α hα.le f)) ∧
        upperWeightedSchurGradient Bx α hα.le L κ f =
          upperCutoffGradientOperator χ hχ hc hs 1
            (CuspSchur.actualSchurSolution (parameter κ) (cuspWeightedInput α hα.le f)) ∧
        upperWeightedSchurGradient By α hα.le L κ f =
          upperCutoffGradientOperator χ hχ hc hs Complex.I
            (CuspSchur.actualSchurSolution (parameter κ) (cuspWeightedInput α hα.le f)) := by
  obtain ⟨L, hL, Bx, By, hvalue, hx, hy⟩ :=
    WeightedSeam.exists_upperCutoff_common_height χ hχ hc hs
  exact ⟨L, hL, Bx, By,
    upperWeightedSchurValue_analyticAt_zero χ hχ hc hs hα L,
    upperWeightedSchurGradient_analyticAt_zero Bx hα L,
    upperWeightedSchurGradient_analyticAt_zero By hα L,
    fun κ hκ hp f => ⟨upperWeightedSchurValue_eq_physical χ hχ hc hs hα hL hvalue hκ hp f,
      upperWeightedSchurGradient_eq_physical χ hχ hc hs 1 Bx hα hL hx hκ hp f,
      upperWeightedSchurGradient_eq_physical χ hχ hc hs Complex.I By hα hL hy hκ hp f⟩⟩

/-- Operator-family form of the actual upper-chart construction, for later
closed local Poisson-jet packaging. -/
theorem exists_analytic_upperWeightedSchur_fields
    (χ : ℂ → ℂ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ upperHalfPlaneSet) {α : ℝ} (hα : 0 < α) :
    ∃ V Dx Dy : ℂ → ModularHilbert →L[ℂ] UpperField,
      AnalyticAt ℂ V 0 ∧ AnalyticAt ℂ Dx 0 ∧ AnalyticAt ℂ Dy 0 ∧
      ∀ κ : ℂ, 0 < κ.re → κ ≠ (1 / 2 : ℂ) → ∀ f : ModularHilbert,
        V κ f = upperCutoffValueOperator χ hχ hc hs
          (CuspSchur.actualSchurSolution (parameter κ) (cuspWeightedInput α hα.le f)) ∧
        Dx κ f = upperCutoffGradientOperator χ hχ hc hs 1
          (CuspSchur.actualSchurSolution (parameter κ) (cuspWeightedInput α hα.le f)) ∧
        Dy κ f = upperCutoffGradientOperator χ hχ hc hs Complex.I
          (CuspSchur.actualSchurSolution (parameter κ) (cuspWeightedInput α hα.le f)) := by
  obtain ⟨L, _, Bx, By, hV, hx, hy, hphysical⟩ :=
    exists_upperWeightedSchur_fields χ hχ hc hs hα
  exact ⟨upperWeightedSchurValue χ hχ hc hs α hα.le L,
    upperWeightedSchurGradient Bx α hα.le L, upperWeightedSchurGradient By α hα.le L,
    hV, hx, hy, hphysical⟩

end GapFamily.Analytic.UpperWeighted
