import GapFamily.Analytic.Cusp.Profile.CuspWeightedSchurContinuation
import GapFamily.Analytic.Cusp.MeanZero.CuspMeanZeroPencilWeak

/-! The actual global constrained form coordinate inside the weighted threshold
Schur formula. Scalar terms are retained explicitly in the exact local split. -/
noncomputable section
namespace GapFamily.Analytic.CuspConstrainedThreshold
open ModularGradient CuspSchurLocal

/-- The actual scalar trace coefficient of the weighted threshold Schur formula. -/
def traceCoefficient (α : ℝ) (hα : 0 ≤ α) : ModularHilbert →L[ℂ] ℂ :=
  (CuspSchur.continuedDenominator 0)⁻¹ • CuspSchurWeighted.localNumerator α hα 0

/-- The constant trace contribution is included in the genuine constrained source. -/
def effectiveSource (α : ℝ) (hα : 0 ≤ α) : ModularHilbert →L[ℂ] ModularHilbert :=
  cuspWeightedInput α hα + (traceCoefficient α hα).smulRight ((1 / 4 : ℂ) • modularConstant)

/-- This is an actual global finite-energy mean-zero-cusp form vector, including
its trace-correction contribution. It is not the global full threshold resolvent. -/
def constrainedForm (α : ℝ) (hα : 0 ≤ α) : ModularHilbert →L[ℂ] cuspMeanZeroForm :=
  (cuspMeanZeroPencilSolution (1 / 4)).comp (effectiveSource α hα)

theorem constrainedForm_apply (α : ℝ) (hα : 0 ≤ α) (F : ModularHilbert) :
    constrainedForm α hα F = cuspMeanZeroPencilSolution (1 / 4) (cuspWeightedInput α hα F) +
      traceCoefficient α hα F •
        ((1 / 4 : ℂ) • cuspMeanZeroPencilSolution (1 / 4) modularConstant) := by
  simp only [constrainedForm, ContinuousLinearMap.comp_apply, effectiveSource,
    add_apply, ContinuousLinearMap.smulRight_apply, map_add, map_smul]

/-- The literal finite-window Schur value splits into its global constrained
coordinate and exactly the two scalar pieces. No height-dependent bound is assumed. -/
theorem continuedLocalSchur_threshold_split (α : ℝ) (hα : 0 ≤ α)
    (L T : ℝ) (F : ModularHilbert) :
    CuspSchurWeighted.continuedLocalSchur α hα L T 0 F =
      modularLowCut (Real.exp L) (meanZeroCuspEmbedding (constrainedForm α hα F)) +
        cuspGreenWeightedLocalOutput α hα L T 0 (cuspHalfLineSourceCoefficient F) +
      traceCoefficient α hα F •
        (modularLowCut (Real.exp L) modularConstant +
          (1 / 4 : ℂ) • cuspConstantLocalResponse L 0) := by
  simp only [CuspSchurWeighted.continuedLocalSchur, CuspSchurWeighted.localZeroTrace,
    add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply,
    smul_apply, localTraceVector, constrainedResponse,
    constrainedForm_apply, map_add, map_smul, parameter, zero_pow (by decide : 2 ≠ 0),
    sub_zero, traceCoefficient, smul_add]
  module

/-- Every higher cusp average of the actual constrained coordinate is zero. -/
theorem constrainedForm_average_zero (α : ℝ) (hα : 0 ≤ α) (F : ModularHilbert)
    (H : ℝ) (hH : 1 ≤ H) :
    cuspAverage H hH (cuspRestrict H (meanZeroCuspEmbedding (constrainedForm α hα F))) = 0 :=
  meanZeroCusp_average_eq_zero H hH _

/-- The constrained source equation is actual: quarter-pencil regularity is proved. -/
theorem constrainedForm_weak_equation (α : ℝ) (hα : 0 ≤ α) (F : ModularHilbert)
    (v : cuspMeanZeroForm) :
    inner ℂ (cuspMeanZeroGradient v) (cuspMeanZeroGradient (constrainedForm α hα F)) -
      (1 / 4 : ℂ) * inner ℂ (meanZeroCuspEmbedding v)
        (meanZeroCuspEmbedding (constrainedForm α hα F)) =
      inner ℂ (meanZeroCuspEmbedding v) (effectiveSource α hα F) :=
  cuspMeanZeroPencilSolution_equation cuspMeanZeroPencil_isUnit_quarter _ _

/-- One source-norm constant controls the actual constrained form and all its
high-cusp Hilbert tails with the proved reciprocal-height decay. -/
theorem exists_constrainedForm_tail_bound (α : ℝ) (hα : 0 ≤ α) :
    ∃ C : ℝ, 0 < C ∧ ∀ F : ModularHilbert,
      ‖constrainedForm α hα F‖ ≤ C * ‖F‖ ∧
      ∀ (H : ℝ) (hH : 1 ≤ H),
        ‖meanZeroCuspTail H hH (constrainedForm α hα F)‖ ≤ (C / H) * ‖F‖ := by
  obtain ⟨C, hC, hu⟩ := @ContinuousLinearMap.bound ℂ ℂ ModularHilbert cuspMeanZeroForm
    inferInstance inferInstance inferInstance inferInstance inferInstance
    cuspMeanZeroForm_normedSpace (RingHom.id ℂ) inferInstance (constrainedForm α hα)
  refine ⟨C, hC, ?_⟩
  intro F
  have hu := hu F
  refine ⟨hu, ?_⟩
  intro H hH
  calc
    _ ≤ (1 / H) * ‖constrainedForm α hα F‖ := meanZeroCuspTail_norm_le H hH _
    _ ≤ (1 / H) * (C * ‖F‖) := mul_le_mul_of_nonneg_left hu (by positivity)
    _ = (C / H) * ‖F‖ := by ring

end GapFamily.Analytic.CuspConstrainedThreshold
