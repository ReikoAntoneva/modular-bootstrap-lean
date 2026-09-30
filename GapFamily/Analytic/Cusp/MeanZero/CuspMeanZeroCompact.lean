import GapFamily.Analytic.Cusp.MeanZero.CuspMeanZeroFormTruncation
import GapFamily.Analytic.Modular.Geometry.ModularTruncatedCompact
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Compactness after removing the horizontal cusp channel

The actual bounded-height modular restrictions are compact. On the closed
form subspace with zero horizontal average above height one, their difference
from the actual embedding has operator norm at most `1 / H`. The embedding
is therefore a norm limit of genuine compact operators.
-/

noncomputable section

namespace GapFamily.Analytic

open Set Filter ModularGradient
open scoped Topology

/-- Literal bounded-height approximation of the constrained form embedding. -/
def meanZeroCuspTruncation (H : ℝ) : cuspMeanZeroForm →L[ℂ] ModularHilbert :=
  (truncatedFormEmbedding H).comp cuspMeanZeroForm.subtypeL

theorem meanZeroCuspTruncation_isCompact (H : ℝ) :
    IsCompactOperator (meanZeroCuspTruncation H) :=
  (isCompactOperator_truncatedFormEmbedding H).comp_clm cuspMeanZeroForm.subtypeL

/-- The error is the actual high-cusp tail, not an assumed approximation. -/
theorem meanZeroCuspTruncation_error (H : ℝ) (hH : 1 ≤ H) :
    ‖meanZeroCuspTruncation H - meanZeroCuspEmbedding‖ ≤ 1 / H := by
  have heq := @norm_sub_rev (cuspMeanZeroForm →L[ℂ] ModularHilbert)
    (inferInstance : SeminormedAddGroup (cuspMeanZeroForm →L[ℂ] ModularHilbert))
    (meanZeroCuspTruncation H) meanZeroCuspEmbedding
  exact heq.le.trans (meanZeroCuspEmbedding_truncatedForm_error H hH)

/-- Genuine operator-norm convergence along increasing integer cutoff heights. -/
theorem meanZeroCuspTruncation_tendsto :
    Tendsto (fun n : ℕ => meanZeroCuspTruncation ((n : ℝ) + 1))
      atTop (𝓝 meanZeroCuspEmbedding) := by
  apply (@tendsto_iff_norm_sub_tendsto_zero ℕ
    (cuspMeanZeroForm →L[ℂ] ModularHilbert)
    (inferInstance : SeminormedAddCommGroup (cuspMeanZeroForm →L[ℂ] ModularHilbert))
    (fun n : ℕ => meanZeroCuspTruncation ((n : ℝ) + 1)) atTop meanZeroCuspEmbedding).mpr
  exact squeeze_zero (fun n => @norm_nonneg (cuspMeanZeroForm →L[ℂ] ModularHilbert)
      (inferInstance : SeminormedAddGroup (cuspMeanZeroForm →L[ℂ] ModularHilbert))
      (meanZeroCuspTruncation ((n : ℝ) + 1) - meanZeroCuspEmbedding))
    (fun n => meanZeroCuspTruncation_error ((n : ℝ) + 1) (le_add_of_nonneg_left (Nat.cast_nonneg n)))
    tendsto_one_div_add_atTop_nhds_zero_nat

/-- The actual completed modular form embedding is compact after imposing
the proved zero-horizontal-average cusp condition. -/
theorem isCompactOperator_meanZeroCuspEmbedding :
    IsCompactOperator meanZeroCuspEmbedding :=
  isCompactOperator_of_tendsto (𝕜₁ := ℂ) (𝕜₂ := ℂ) (σ₁₂ := RingHom.id ℂ)
    (M₁ := cuspMeanZeroForm) (M₂ := ModularHilbert) meanZeroCuspTruncation_tendsto
    (Eventually.of_forall fun n => meanZeroCuspTruncation_isCompact ((n : ℝ) + 1))

theorem meanZeroCuspEmbedding_isCompact_closure_image_closedBall (R : ℝ) :
    IsCompact (closure (meanZeroCuspEmbedding '' Metric.closedBall 0 R)) :=
  @IsCompactOperator.isCompact_closure_image_closedBall ℂ ℂ inferInstance inferInstance
    (RingHom.id ℂ) cuspMeanZeroForm ModularHilbert
    (inferInstance : SeminormedAddCommGroup cuspMeanZeroForm)
    (inferInstance : TopologicalSpace ModularHilbert)
    (inferInstance : AddCommMonoid ModularHilbert)
    (inferInstance : NormedSpace ℂ cuspMeanZeroForm)
    (inferInstance : Module ℂ ModularHilbert) inferInstance inferInstance
    meanZeroCuspEmbedding.toLinearMap isCompactOperator_meanZeroCuspEmbedding R

end GapFamily.Analytic
