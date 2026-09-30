import GapFamily.Analytic.Cusp.Green.CuspGreenTailOperator
import GapFamily.Analytic.Cusp.Green.CuspGreenMixedOperator
import GapFamily.Analytic.Cusp.Profile.CuspHalfLineWeightedInput
import GapFamily.Analytic.Cusp.Profile.CuspHalfLineCollarRepresentative
import GapFamily.Analytic.Cusp.Green.CuspGreenBoundedOutput

/-!
# The actual weighted Green response in a bounded observation window

The finite source collar and the genuine rank-one source tail form one bounded
operator with continuous output. Its literal ordinary integral is independent
of the auxiliary source cutoff and remains analytic through κ=0.
-/

noncomputable section
namespace GapFamily.Analytic
open Set Filter MeasureTheory CuspHalfLineLaplace CuspHalfLineLaplaceTail
open scoped Topology

/-- The actual finite-source weighted Green operator plus its genuine noncompact tail. -/
def cuspGreenWeightedLocalOperator (α : ℝ) (hα : 0 ≤ α) (L T : ℝ) (κ : ℂ) :
    HalfLineL2 →L[ℂ] C(CuspGreenCollar 0 L, ℂ) :=
  (cuspGreenMixedOperator L T κ).comp
      ((cuspHalfLineCollarRestriction T).comp (cuspHalfLineWeight α hα)) +
    cuspGreenWeightedTailOperator α L T κ

/-- Norm analyticity holds throughout the shifted Laplace half-plane. -/
theorem analyticAt_cuspGreenWeightedLocalOperator (α : ℝ) (hα : 0 ≤ α) (L T : ℝ)
    {κ : ℂ} (hβ : 0 < ((α : ℂ) + κ).re) :
    AnalyticAt ℂ (cuspGreenWeightedLocalOperator α hα L T) κ := by
  have hf : AnalyticAt ℂ (fun z : ℂ => (cuspGreenMixedOperator L T z).comp
      ((cuspHalfLineCollarRestriction T).comp (cuspHalfLineWeight α hα))) κ :=
    ((differentiable_cuspGreenMixedOperator L T).clm_comp
      (differentiable_const ((cuspHalfLineCollarRestriction T).comp
        (cuspHalfLineWeight α hα)))).analyticAt κ
  exact hf.add (analyticAt_cuspGreenWeightedTailOperator α L T hβ)

theorem analyticAt_cuspGreenWeightedLocalOperator_zero {α : ℝ} (hα : 0 < α)
    (L T : ℝ) : AnalyticAt ℂ (cuspGreenWeightedLocalOperator α hα.le L T) 0 :=
  analyticAt_cuspGreenWeightedLocalOperator α hα.le L T (by simpa using hα)

/-- The finite operator is the literal weighted integral of the same half-line source. -/
theorem cuspGreenWeightedLocal_finite_apply (α : ℝ) (hα : 0 ≤ α) (L T : ℝ) (κ : ℂ)
    (f : HalfLineL2) (t : CuspGreenCollar 0 L) :
    cuspGreenMixedOperator L T κ
      (cuspHalfLineCollarRestriction T (cuspHalfLineWeight α hα f)) t =
      ∫ u : ℝ in Ioc 0 T,
        cuspGreen 0 t u κ * Complex.exp (-(α : ℂ) * u) * f u := by
  rw [cuspGreenMixedOperator_apply,
    cuspHalfLineCollarRestriction_integral T (cuspHalfLineWeight α hα f)
      (fun u => cuspGreen 0 t u κ)]
  apply integral_congr_ae
  have hw := (MeasureTheory.ae_mono
    (Measure.restrict_mono_set volume (Ioc_subset_Ioi_self : Ioc (0 : ℝ) T ⊆ Ioi 0)))
      (cuspHalfLineWeight_ae α hα f)
  filter_upwards [hw] with u hu
  rw [hu, Complex.ofReal_exp, Complex.ofReal_mul, Complex.ofReal_neg]
  ring

/-- On its natural half-plane the operator is exactly the ordinary noncompact
weighted Green integral at every point of the observed collar. -/
theorem cuspGreenWeightedLocalOperator_apply {α L T : ℝ} (hα : 0 ≤ α)
    (hT : 0 ≤ T) (hLT : L ≤ T) {κ : ℂ} (hβ : 0 < ((α : ℂ) + κ).re)
    (f : HalfLineL2) (t : CuspGreenCollar 0 L) :
    cuspGreenWeightedLocalOperator α hα L T κ f t =
      ∫ u : ℝ in Ioi 0,
        cuspGreen 0 t u κ * Complex.exp (-(α : ℂ) * u) * f u := by
  change cuspGreenMixedOperator L T κ
    (cuspHalfLineCollarRestriction T (cuspHalfLineWeight α hα f)) t +
    cuspGreenWeightedTailOperator α L T κ f t = _
  rw [cuspGreenWeightedLocal_finite_apply, cuspGreenWeightedTailOperator_apply]
  exact (cuspGreen_weighted_integral_split hT (t.property.2.trans hLT) hβ f).symm

/-- The genuine local response does not depend on the auxiliary source collar. -/
theorem cuspGreenWeightedLocalOperator_cutoff_eq {α L T R : ℝ} (hα : 0 ≤ α)
    (hT : 0 ≤ T) (hLT : L ≤ T) (hR : 0 ≤ R) (hLR : L ≤ R)
    {κ : ℂ} (hβ : 0 < ((α : ℂ) + κ).re) :
    cuspGreenWeightedLocalOperator α hα L T κ =
      cuspGreenWeightedLocalOperator α hα L R κ := by
  apply ContinuousLinearMap.ext
  intro f
  ext t
  rw [cuspGreenWeightedLocalOperator_apply hα hT hLT hβ,
    cuspGreenWeightedLocalOperator_apply hα hR hLR hβ]

/-- The actual modular Hilbert output obtained by the already proved collar isometry. -/
def cuspGreenWeightedLocalOutput (α : ℝ) (hα : 0 ≤ α) (L T : ℝ) (κ : ℂ) :
    HalfLineL2 →L[ℂ] ModularHilbert :=
  (cuspGreenSourceEmbedding L).toContinuousLinearMap.comp
    ((ContinuousMap.toLp 2 (cuspGreenCollarMeasure 0 L) ℂ).comp
      (cuspGreenWeightedLocalOperator α hα L T κ))

theorem analyticAt_cuspGreenWeightedLocalOutput (α : ℝ) (hα : 0 ≤ α) (L T : ℝ)
    {κ : ℂ} (hβ : 0 < ((α : ℂ) + κ).re) :
    AnalyticAt ℂ (cuspGreenWeightedLocalOutput α hα L T) κ :=
  by
    let P : C(CuspGreenCollar 0 L, ℂ) →L[ℂ] ModularHilbert :=
      (cuspGreenSourceEmbedding L).toContinuousLinearMap.comp
        (ContinuousMap.toLp 2 (cuspGreenCollarMeasure 0 L) ℂ)
    exact ((ContinuousLinearMap.compL ℂ HalfLineL2 C(CuspGreenCollar 0 L, ℂ)
      ModularHilbert P).analyticAt _).comp
        (analyticAt_cuspGreenWeightedLocalOperator α hα L T hβ)

end GapFamily.Analytic
