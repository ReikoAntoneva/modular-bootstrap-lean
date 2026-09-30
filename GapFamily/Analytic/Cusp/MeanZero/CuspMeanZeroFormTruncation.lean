import GapFamily.Analytic.Cusp.MeanZero.CuspMeanZeroForm
import GapFamily.Analytic.Modular.Geometry.ModularTruncatedForm

/-!
# The literal low-height approximation on the zero-average cusp form space

The approximation error is exactly the full high-height indicator, extended
by zero in the actual modular Hilbert space. Its operator norm tends to zero
at the proved rate `1 / H`.
-/

noncomputable section

namespace GapFamily.Analytic

open MeasureTheory Set UpperHalfPlane ModularGradient

theorem meanZeroCuspTail_eq_highCut (H : ℝ) (hH : 1 ≤ H) :
    meanZeroCuspTail H hH = (modularHighCut H).comp meanZeroCuspEmbedding := by
  ext u
  rfl

/-- The full tail is the literal ordinary high-cusp indicator on the ambient class. -/
theorem meanZeroCuspTail_ae (H : ℝ) (hH : 1 ≤ H) (u : cuspMeanZeroForm) :
    meanZeroCuspTail H hH u =ᵐ[modularMeasure]
      {τ : UpperHalfPlane | H < τ.im}.indicator (meanZeroCuspEmbedding u) :=
  modularHighCut_ae H (meanZeroCuspEmbedding u)

/-- The low-height piece plus the full cusp tail reconstructs the value. -/
theorem meanZeroCusp_lowCut_add_tail (H : ℝ) (hH : 1 ≤ H) (u : cuspMeanZeroForm) :
    modularLowCut H (meanZeroCuspEmbedding u) + meanZeroCuspTail H hH u =
      meanZeroCuspEmbedding u :=
  modularLowCut_add_highCut H (meanZeroCuspEmbedding u)

/-- The low-height approximation error is exactly the actual full-cusp tail map. -/
theorem meanZeroCuspEmbedding_sub_lowCut (H : ℝ) (hH : 1 ≤ H) :
    meanZeroCuspEmbedding - (modularLowCut H).comp meanZeroCuspEmbedding =
      meanZeroCuspTail H hH := by
  apply ContinuousLinearMap.ext
  intro u
  change meanZeroCuspEmbedding u -
      (meanZeroCuspEmbedding u - modularHighCut H (meanZeroCuspEmbedding u)) =
    modularHighCut H (meanZeroCuspEmbedding u)
  abel

theorem meanZeroCuspEmbedding_lowCut_error (H : ℝ) (hH : 1 ≤ H) :
    ‖meanZeroCuspEmbedding - (modularLowCut H).comp meanZeroCuspEmbedding‖ ≤ 1 / H := by
  rw [meanZeroCuspEmbedding_sub_lowCut]
  exact meanZeroCuspTail_opNorm_le H hH

/-- The constrained low-height map is the restriction of the actual form truncation. -/
theorem meanZeroCusp_lowCut_eq_truncatedForm (H : ℝ) :
    (modularLowCut H).comp meanZeroCuspEmbedding =
      (truncatedFormEmbedding H).comp cuspMeanZeroForm.subtypeL := by
  ext u
  rfl

theorem meanZeroCuspEmbedding_sub_truncatedForm (H : ℝ) (hH : 1 ≤ H) :
    meanZeroCuspEmbedding - (truncatedFormEmbedding H).comp cuspMeanZeroForm.subtypeL =
      meanZeroCuspTail H hH :=
  meanZeroCuspEmbedding_sub_lowCut H hH

theorem meanZeroCuspEmbedding_truncatedForm_error (H : ℝ) (hH : 1 ≤ H) :
    ‖meanZeroCuspEmbedding - (truncatedFormEmbedding H).comp cuspMeanZeroForm.subtypeL‖ ≤
      1 / H :=
  meanZeroCuspEmbedding_lowCut_error H hH

end GapFamily.Analytic
