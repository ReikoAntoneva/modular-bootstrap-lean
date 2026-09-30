import GapFamily.Analytic.Cusp.Green.CuspGreenWeightedLocal
import GapFamily.Analytic.Cusp.Profile.CuspWeightedInputCutoff

/-!
# Physical identification for the local weighted Green response

The finite source-cutoff physical equations converge in the actual modular
Hilbert norm. Their genuine rank-one tails vanish, identifying the constructed
analytic local response for every ambient Hilbert source.
-/

noncomputable section
namespace GapFamily.Analytic
open Set Filter MeasureTheory ModularGradient CuspHalfLineLaplace
open scoped Topology

/-- For a fixed parameter in the shifted half-plane, the genuine tail operator
vanishes in operator norm as the source cutoff tends to infinity. -/
theorem cuspGreenWeightedTailOperator_tendsto (α L : ℝ) {κ : ℂ}
    (hβ : 0 < ((α : ℂ) + κ).re) :
    Tendsto (fun T : ℝ => cuspGreenWeightedTailOperator α L T κ) atTop (𝓝 0) := by
  have he : Tendsto (fun T : ℝ => Real.exp (-((α : ℂ) + κ).re * T)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp
      (tendsto_id.const_mul_atTop_of_neg (neg_neg_of_pos hβ))
  have hb := (he.div_const (Real.sqrt (2 * ((α : ℂ) + κ).re))).const_mul
    ‖cuspGreenTailObserved L κ‖
  simp only [zero_div, mul_zero] at hb
  apply (tendsto_zero_iff_norm_tendsto_zero
    (f := fun T : ℝ => cuspGreenWeightedTailOperator α L T κ)).mpr
  exact squeeze_zero' (Filter.Eventually.of_forall fun T => norm_nonneg _)
    ((eventually_ge_atTop (0 : ℝ)).mono fun T hT =>
      cuspGreenWeightedTailOperator_norm_le hT hβ) hb

/-- A finite auxiliary source collar leaves exactly the actual rank-one tail. -/
theorem cuspGreenWeightedLocalOutput_eq_finite_add_tail {α L T R : ℝ} (hα : 0 ≤ α)
    (hT : 0 ≤ T) (hLT : L ≤ T) (hR : 0 ≤ R) (hLR : L ≤ R)
    {κ : ℂ} (hβ : 0 < ((α : ℂ) + κ).re) (F : ModularHilbert) :
    cuspGreenWeightedLocalOutput α hα L T κ (cuspHalfLineSourceCoefficient F) =
      cuspGreenBoundedOutput L R κ (cuspWeightedInput α hα F) +
      cuspGreenSourceEmbedding L (ContinuousMap.toLp 2 (cuspGreenCollarMeasure 0 L) ℂ
        (cuspGreenWeightedTailOperator α L R κ (cuspHalfLineSourceCoefficient F))) := by
  have hc := cuspGreenWeightedLocalOperator_cutoff_eq hα hT hLT hR hLR hβ
  unfold cuspGreenWeightedLocalOutput
  rw [hc]
  change cuspGreenSourceEmbedding L
    (ContinuousMap.toLp 2 (cuspGreenCollarMeasure 0 L) ℂ
      (cuspGreenMixedOperator L R κ
        (cuspHalfLineCollarRestriction R
          (cuspHalfLineWeight α hα (cuspHalfLineSourceCoefficient F))) +
        cuspGreenWeightedTailOperator α L R κ (cuspHalfLineSourceCoefficient F))) = _
  rw [map_add, map_add, ← cuspHalfLineSourceCoefficient_weightedInput,
    cuspHalfLineCollarRestriction_sourceCoefficient]
  rfl

/-- The local weighted family equals the original physical scalar response for
every ambient modular Hilbert source. No global inverse at κ=0 is claimed. -/
theorem cuspGreenWeightedLocalOutput_eq_physical {α L T : ℝ} (hα : 0 < α)
    (hL : 0 ≤ L) (hT : 0 ≤ T) (hLT : L ≤ T) {κ : ℂ} (hκ : 0 < κ.re)
    (F : ModularHilbert) :
    cuspGreenWeightedLocalOutput α hα.le L T κ (cuspHalfLineSourceCoefficient F) =
      modularLowCut (Real.exp L)
        (scalarCuspEmbedding (cuspScalarPencilSolution (1/4 - κ^2)
          (cuspWeightedInput α hα.le F))) := by
  have hβ : 0 < ((α : ℂ) + κ).re := by
    simp only [Complex.add_re, Complex.ofReal_re]
    positivity
  let P : ModularHilbert →L[ℂ] ModularHilbert :=
    (modularLowCut (Real.exp L)).comp
      (scalarCuspEmbedding.comp (cuspScalarPencilSolution (1/4 - κ^2)))
  let J : C(CuspGreenCollar 0 L, ℂ) →L[ℂ] ModularHilbert :=
    (cuspGreenSourceEmbedding L).toContinuousLinearMap.comp
      (ContinuousMap.toLp 2 (cuspGreenCollarMeasure 0 L) ℂ)
  have hinput : Tendsto
      (fun R : ℝ => modularLowCut (Real.exp R) (cuspWeightedInput α hα.le F))
      atTop (𝓝 (cuspWeightedInput α hα.le F)) := by
    exact ((ContinuousLinearMap.apply ℂ ModularHilbert F).continuous.tendsto _).comp
      (cuspWeightedInput_lowCut_tendsto hα)
  have hphysical := (P.continuous.tendsto _).comp hinput
  have hfinite : Tendsto (fun R : ℝ => cuspGreenBoundedOutput L R κ
      (cuspWeightedInput α hα.le F)) atTop (𝓝 (P (cuspWeightedInput α hα.le F))) := by
    apply hphysical.congr'
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with R hR
    have he : cuspGreenBoundedOutput L R κ
        (modularLowCut (Real.exp R) (cuspWeightedInput α hα.le F)) =
        cuspGreenBoundedOutput L R κ (cuspWeightedInput α hα.le F) := by
      simp only [cuspGreenBoundedOutput, ContinuousLinearMap.comp_apply,
        cuspGreenSourceCoefficient_lowCut]
    exact (cuspGreenBoundedOutput_eq_physical hL hR hκ
      (modularLowCut (Real.exp R) (cuspWeightedInput α hα.le F))
      (modularHighCut_lowCut _ _)).symm.trans he
  have htail : Tendsto (fun R : ℝ =>
      J (cuspGreenWeightedTailOperator α L R κ (cuspHalfLineSourceCoefficient F)))
      atTop (𝓝 0) := by
    have hh := ((ContinuousLinearMap.apply ℂ C(CuspGreenCollar 0 L, ℂ)
      (cuspHalfLineSourceCoefficient F)).continuous.tendsto _).comp
        (cuspGreenWeightedTailOperator_tendsto α L hβ)
    have hj := (J.continuous.tendsto _).comp hh
    simp only [map_zero] at hj
    apply hj.congr'
    exact Filter.Eventually.of_forall fun R => rfl
  have hsum := hfinite.add htail
  simp only [add_zero] at hsum
  have hconst : Tendsto (fun _ : ℝ =>
      cuspGreenWeightedLocalOutput α hα.le L T κ (cuspHalfLineSourceCoefficient F))
      atTop (𝓝 (P (cuspWeightedInput α hα.le F))) := by
    apply hsum.congr'
    filter_upwards [eventually_ge_atTop (max 0 L)] with R hR
    exact (cuspGreenWeightedLocalOutput_eq_finite_add_tail hα.le hT hLT
      ((le_max_left 0 L).trans hR) ((le_max_right 0 L).trans hR) hβ F).symm
  exact tendsto_nhds_unique tendsto_const_nhds hconst

end GapFamily.Analytic
