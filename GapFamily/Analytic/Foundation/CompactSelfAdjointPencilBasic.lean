import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Meromorphic.Basic
import Mathlib.Analysis.Normed.Algebra.Spectrum

/-!
# The affine compact-response pencil

This file defines the actual affine pencil and proves its local analytic
inverse statements. Meromorphy across singular parameters is proved separately.
-/

noncomputable section

namespace GapFamily.Analytic

open Filter
open scoped Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The actual pencil associated with a shifted compact response. -/
def compactSelfAdjointPencil (R : H →L[ℂ] H) (z : ℂ) : H →L[ℂ] H :=
  1 - (z + 1) • R

@[simp] theorem compactSelfAdjointPencil_neg_one (R : H →L[ℂ] H) :
    compactSelfAdjointPencil R (-1) = 1 := by
  simp [compactSelfAdjointPencil]

theorem compactSelfAdjointPencil_analyticAt (R : H →L[ℂ] H) (z : ℂ) :
    AnalyticAt ℂ (compactSelfAdjointPencil R) z := by
  unfold compactSelfAdjointPencil
  fun_prop

variable [CompleteSpace H]

/-- Actual inversion is analytic at every already regular pencil parameter. -/
theorem inverse_compactSelfAdjointPencil_analyticAt (R : H →L[ℂ] H) (z : ℂ)
    (hz : IsUnit (compactSelfAdjointPencil R z)) :
    AnalyticAt ℂ (fun w => Ring.inverse (compactSelfAdjointPencil R w)) z := by
  have hi : AnalyticAt ℂ Ring.inverse (compactSelfAdjointPencil R z) :=
    analyticOnNhd_inverse (𝕜 := ℂ) _ hz
  exact hi.comp (compactSelfAdjointPencil_analyticAt R z)

end GapFamily.Analytic
