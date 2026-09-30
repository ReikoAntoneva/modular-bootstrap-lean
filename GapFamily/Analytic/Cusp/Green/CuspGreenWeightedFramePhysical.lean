import GapFamily.Analytic.Cusp.Green.CuspGreenWeightedFrameLocal
import GapFamily.Analytic.Cusp.Profile.CuspWeightedInputCutoff

/-!
# Physical identification for the local weighted Green gradient

The finite source-cutoff physical gradient equations converge through the
actual bounded form and gradient maps. The genuine frame tail vanishes in
operator norm, identifying the continued local frame output for every ambient
Hilbert source. The output is clipped after taking the physical gradient.
-/

noncomputable section
namespace GapFamily.Analytic
open Set Filter MeasureTheory ModularGradient CuspHalfLineLaplace
open scoped Topology

/-- A finite auxiliary source collar leaves exactly the actual frame tail. -/
theorem cuspGreenWeightedFrameLocalOutput_eq_finite_add_tail {α L T R : ℝ} (hα : 0 ≤ α)
    (hT : 0 ≤ T) (hLT : L ≤ T) (hR : 0 ≤ R) (hLR : L ≤ R)
    {κ : ℂ} (hβ : 0 < ((α : ℂ) + κ).re) (F : ModularHilbert) :
    cuspGreenWeightedFrameLocalOutput α hα L T κ (cuspHalfLineSourceCoefficient F) =
      cuspGreenFrameBoundedOutput L R κ (cuspWeightedInput α hα F) +
      cuspGreenSourceEmbedding L (ContinuousMap.toLp 2 (cuspGreenCollarMeasure 0 L) ℂ
        (cuspGreenWeightedTailFrameOperator α L R κ (cuspHalfLineSourceCoefficient F))) := by
  have hc := cuspGreenWeightedFrameLocalOperator_cutoff_eq hα hT hLT hR hLR hβ
  unfold cuspGreenWeightedFrameLocalOutput
  rw [hc]
  change cuspGreenSourceEmbedding L
    (ContinuousMap.toLp 2 (cuspGreenCollarMeasure 0 L) ℂ
      (cuspGreenFrameOperator L R κ
        (cuspHalfLineCollarRestriction R
          (cuspHalfLineWeight α hα (cuspHalfLineSourceCoefficient F))) +
        cuspGreenWeightedTailFrameOperator α L R κ (cuspHalfLineSourceCoefficient F))) = _
  rw [map_add, map_add, ← cuspHalfLineSourceCoefficient_weightedInput,
    cuspHalfLineCollarRestriction_sourceCoefficient]
  rfl

/-- The local weighted frame family equals the clipped actual scalar gradient
for every ambient modular Hilbert source in the physical half-plane. -/
theorem cuspGreenWeightedFrameLocalOutput_eq_physical {α L T : ℝ} (hα : 0 < α)
    (hL : 0 ≤ L) (hT : 0 ≤ T) (hLT : L ≤ T) {κ : ℂ} (hκ : 0 < κ.re)
    (F : ModularHilbert) :
    cuspGreenWeightedFrameLocalOutput α hα.le L T κ (cuspHalfLineSourceCoefficient F) =
      modularLowCut (Real.exp L)
        (cuspScalarGradient (cuspScalarPencilSolution (1 / 4 - κ ^ 2)
          (cuspWeightedInput α hα.le F))).ofLp.2 := by
  have hβ : 0 < ((α : ℂ) + κ).re := by
    simp only [Complex.add_re, Complex.ofReal_re]
    positivity
  let P : ModularHilbert →L[ℂ] ModularHilbert :=
    (modularLowCut (Real.exp L)).comp
      (((WithLp.sndL 2 ℂ ModularHilbert ModularHilbert).comp cuspScalarGradient).comp
        (cuspScalarPencilSolution (1 / 4 - κ ^ 2)))
  let J : C(CuspGreenCollar 0 L, ℂ) →L[ℂ] ModularHilbert :=
    (cuspGreenSourceEmbedding L).toContinuousLinearMap.comp
      (ContinuousMap.toLp 2 (cuspGreenCollarMeasure 0 L) ℂ)
  have hinput : Tendsto
      (fun R : ℝ => modularLowCut (Real.exp R) (cuspWeightedInput α hα.le F))
      atTop (𝓝 (cuspWeightedInput α hα.le F)) := by
    exact ((ContinuousLinearMap.apply ℂ ModularHilbert F).continuous.tendsto _).comp
      (cuspWeightedInput_lowCut_tendsto hα)
  have hphysical := (P.continuous.tendsto _).comp hinput
  have hfinite : Tendsto (fun R : ℝ => cuspGreenFrameBoundedOutput L R κ
      (cuspWeightedInput α hα.le F)) atTop (𝓝 (P (cuspWeightedInput α hα.le F))) := by
    apply hphysical.congr'
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with R hR
    have he : cuspGreenFrameBoundedOutput L R κ
        (modularLowCut (Real.exp R) (cuspWeightedInput α hα.le F)) =
        cuspGreenFrameBoundedOutput L R κ (cuspWeightedInput α hα.le F) := by
      simp only [cuspGreenFrameBoundedOutput, ContinuousLinearMap.comp_apply,
        cuspGreenSourceCoefficient_lowCut]
    exact (cuspGreenFrameBoundedOutput_eq_physical hL hR hκ
      (modularLowCut (Real.exp R) (cuspWeightedInput α hα.le F))
      (modularHighCut_lowCut _ _)).symm.trans he
  have htail : Tendsto (fun R : ℝ =>
      J (cuspGreenWeightedTailFrameOperator α L R κ (cuspHalfLineSourceCoefficient F)))
      atTop (𝓝 0) := by
    have hh := ((ContinuousLinearMap.apply ℂ C(CuspGreenCollar 0 L, ℂ)
      (cuspHalfLineSourceCoefficient F)).continuous.tendsto _).comp
        (cuspGreenWeightedTailFrameOperator_tendsto α L hβ)
    have hj := (J.continuous.tendsto _).comp hh
    simp only [map_zero] at hj
    apply hj.congr'
    exact Filter.Eventually.of_forall fun R => rfl
  have hsum := hfinite.add htail
  simp only [add_zero] at hsum
  have hconst : Tendsto (fun _ : ℝ =>
      cuspGreenWeightedFrameLocalOutput α hα.le L T κ (cuspHalfLineSourceCoefficient F))
      atTop (𝓝 (P (cuspWeightedInput α hα.le F))) := by
    apply hsum.congr'
    filter_upwards [eventually_ge_atTop (max 0 L)] with R hR
    exact (cuspGreenWeightedFrameLocalOutput_eq_finite_add_tail hα.le hT hLT
      ((le_max_left 0 L).trans hR) ((le_max_right 0 L).trans hR) hβ F).symm
  exact tendsto_nhds_unique tendsto_const_nhds hconst

end GapFamily.Analytic
