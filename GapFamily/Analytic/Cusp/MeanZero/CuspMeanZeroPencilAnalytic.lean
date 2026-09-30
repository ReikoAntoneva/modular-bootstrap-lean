import GapFamily.Analytic.Cusp.MeanZero.CuspMeanZeroPencilBasic
import GapFamily.Analytic.Foundation.CompactSelfAdjointPencilRegular

/-!
# The actual regular domain and analytic constrained solution

The regular domain is the actual unit set of the operator pencil. Inversion
and bounded composition prove norm-valued analyticity of the source solution
there. This local theorem is separate from meromorphy at singular parameters.
-/

noncomputable section

namespace GapFamily.Analytic

open Set Filter
open scoped Topology

/-- The canonical operator-norm structure on actual constrained solution maps. -/
instance cuspMeanZeroSolutionOperator_normedSpace :
    NormedSpace ℂ (ModularHilbert →L[ℂ] cuspMeanZeroForm) :=
  ContinuousLinearMap.toNormedSpace (𝕜 := ℂ) (𝕜₂ := ℂ) (𝕜' := ℂ)
    (E := ModularHilbert) (F := cuspMeanZeroForm) (σ₁₂ := RingHom.id ℂ)

/-- The actual regular parameter set, without a spectral-isolation assumption. -/
def cuspMeanZeroPencilRegularSet : Set ℂ := {z | IsUnit (cuspMeanZeroPencil z)}

theorem isOpen_cuspMeanZeroPencilRegularSet : IsOpen cuspMeanZeroPencilRegularSet := by
  apply isOpen_iff_mem_nhds.mpr
  intro z hz
  exact compactSelfAdjointPencil_eventually_isUnit cuspMeanZeroWeakResolvent z hz

/-- Bounded postcomposition by the actual constrained weak solution. -/
def cuspMeanZeroSolutionPostcompose :
    (ModularHilbert →L[ℂ] ModularHilbert) →L[ℂ] (ModularHilbert →L[ℂ] cuspMeanZeroForm) :=
  ContinuousLinearMap.compL ℂ ModularHilbert ModularHilbert cuspMeanZeroForm
    cuspMeanZeroWeakSolution

@[simp] theorem cuspMeanZeroSolutionPostcompose_apply
    (A : ModularHilbert →L[ℂ] ModularHilbert) :
    cuspMeanZeroSolutionPostcompose A = cuspMeanZeroWeakSolution.comp A := rfl

theorem cuspMeanZeroPencilSolution_eq_postcompose (z : ℂ) :
    cuspMeanZeroPencilSolution z =
      cuspMeanZeroSolutionPostcompose (Ring.inverse (cuspMeanZeroPencil z)) := rfl

/-- Actual inverse and bounded postcomposition give analytic source solutions
at every regular parameter. -/
theorem cuspMeanZeroPencilSolution_analyticAt {z : ℂ}
    (hz : IsUnit (cuspMeanZeroPencil z)) :
    AnalyticAt ℂ cuspMeanZeroPencilSolution z := by
  have hi := inverse_compactSelfAdjointPencil_analyticAt cuspMeanZeroWeakResolvent z hz
  have hL := ContinuousLinearMap.analyticAt (𝕜 := ℂ)
    (E := ModularHilbert →L[ℂ] ModularHilbert)
    (F := ModularHilbert →L[ℂ] cuspMeanZeroForm) cuspMeanZeroSolutionPostcompose
    (Ring.inverse (cuspMeanZeroPencil z))
  exact hL.comp_of_eq hi rfl

theorem cuspMeanZeroPencilSolution_analyticOnNhd :
    AnalyticOnNhd ℂ cuspMeanZeroPencilSolution cuspMeanZeroPencilRegularSet :=
  fun _ hz => cuspMeanZeroPencilSolution_analyticAt hz

end GapFamily.Analytic
