import GapFamily.Analytic.Modular.ModularHilbert
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions

noncomputable section

namespace GapFamily.Analytic.SpatialPoint

open MeasureTheory BoundedContinuousFunction

/-- The actual finite-measure inclusion of bounded continuous functions into modular L². -/
def modularBoundedEmbedding : (UpperHalfPlane →ᵇ ℂ) →L[ℂ] ModularHilbert :=
  BoundedContinuousFunction.toLp 2 modularMeasure ℂ

theorem modularBoundedEmbedding_def :
    modularBoundedEmbedding =
      BoundedContinuousFunction.toLp (α := UpperHalfPlane) (E := ℂ) 2 modularMeasure ℂ :=
  rfl

theorem modularBoundedEmbedding_ae (f : UpperHalfPlane →ᵇ ℂ) :
    modularBoundedEmbedding f =ᵐ[modularMeasure] f :=
  BoundedContinuousFunction.coeFn_toLp 2 modularMeasure ℂ f

theorem modularBoundedEmbedding_memLp (f : UpperHalfPlane →ᵇ ℂ) :
    MemLp f 2 modularMeasure :=
  (memLp_congr_ae (modularBoundedEmbedding_ae f)).mp
    (Lp.memLp (modularBoundedEmbedding f))

theorem modularBoundedEmbedding_apply_eq_toLp (f : UpperHalfPlane →ᵇ ℂ) :
    modularBoundedEmbedding f = (modularBoundedEmbedding_memLp f).toLp f := by
  apply Lp.ext
  exact (modularBoundedEmbedding_ae f).trans (MemLp.coeFn_toLp _).symm

theorem modularBoundedEmbedding_norm_le :
    ‖modularBoundedEmbedding‖ ≤
      (measureUnivNNReal modularMeasure : ℝ) ^ (1 / 2 : ℝ) := by
  simpa [modularBoundedEmbedding] using
    (BoundedContinuousFunction.toLp_norm_le
      (α := UpperHalfPlane) (E := ℂ) (𝕜 := ℂ) (p := 2) modularMeasure)

end GapFamily.Analytic.SpatialPoint
