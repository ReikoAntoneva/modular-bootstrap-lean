import GapFamily.Analytic.Cusp.Scalar.CuspScalarPencilBasic
import GapFamily.Analytic.Foundation.CompactSelfAdjointPencilRegular

/-!
# Operator-norm analyticity on the actual scalar regular set

Inversion and bounded postcomposition give operator-norm analyticity at each
actual unit parameter. This is local analyticity on the genuine regular set;
no compactness or continuation across the continuous spectrum is asserted.
-/

noncomputable section

namespace GapFamily.Analytic

open Set Filter
open scoped Topology

/-- The canonical operator-norm structure on actual scalar solution maps. -/
instance cuspScalarSolutionOperator_normedSpace :
    NormedSpace ℂ (ModularHilbert →L[ℂ] cuspScalarForm) :=
  ContinuousLinearMap.toNormedSpace (𝕜 := ℂ) (𝕜₂ := ℂ) (𝕜' := ℂ)
    (E := ModularHilbert) (F := cuspScalarForm) (σ₁₂ := RingHom.id ℂ)

/-- Regular parameters are exactly the actual unit set of the scalar pencil. -/
def cuspScalarPencilRegularSet : Set ℂ := {z | IsUnit (cuspScalarPencil z)}

theorem isOpen_cuspScalarPencilRegularSet : IsOpen cuspScalarPencilRegularSet := by
  apply isOpen_iff_mem_nhds.mpr
  intro z hz
  exact compactSelfAdjointPencil_eventually_isUnit cuspScalarWeakResolvent z hz

/-- Bounded postcomposition by the actual scalar Riesz source map. -/
def cuspScalarSolutionPostcompose :
    (ModularHilbert →L[ℂ] ModularHilbert) →L[ℂ] (ModularHilbert →L[ℂ] cuspScalarForm) :=
  ContinuousLinearMap.compL ℂ ModularHilbert ModularHilbert cuspScalarForm
    cuspScalarWeakSolution

@[simp] theorem cuspScalarSolutionPostcompose_apply
    (A : ModularHilbert →L[ℂ] ModularHilbert) :
    cuspScalarSolutionPostcompose A = cuspScalarWeakSolution.comp A := rfl

theorem cuspScalarPencilSolution_eq_postcompose (z : ℂ) :
    cuspScalarPencilSolution z =
      cuspScalarSolutionPostcompose (Ring.inverse (cuspScalarPencil z)) := rfl

/-- The actual form-valued source response is analytic in operator norm at
every regular parameter. No continuation through the continuous spectrum is asserted. -/
theorem cuspScalarPencilSolution_analyticAt {z : ℂ}
    (hz : IsUnit (cuspScalarPencil z)) :
    AnalyticAt ℂ cuspScalarPencilSolution z := by
  have hi := inverse_compactSelfAdjointPencil_analyticAt cuspScalarWeakResolvent z hz
  have hL := ContinuousLinearMap.analyticAt (𝕜 := ℂ)
    (E := ModularHilbert →L[ℂ] ModularHilbert)
    (F := ModularHilbert →L[ℂ] cuspScalarForm) cuspScalarSolutionPostcompose
    (Ring.inverse (cuspScalarPencil z))
  exact hL.comp_of_eq hi rfl

theorem cuspScalarPencilSolution_analyticOnNhd :
    AnalyticOnNhd ℂ cuspScalarPencilSolution cuspScalarPencilRegularSet :=
  fun _ hz => cuspScalarPencilSolution_analyticAt hz

end GapFamily.Analytic
