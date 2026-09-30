import GapFamily.Analytic.Cusp.MeanZero.CuspMeanZeroCoercive
import GapFamily.Analytic.Foundation.CompactSelfAdjointPencilBasic

/-!
# The actual constrained cusp pencil and source solution family

The pencil is I-(z+1)R for the genuine compact constrained response R. Its
source map is S composed with the algebra's actual totalized inverse. Weak
solution identities are asserted only at parameters where the pencil is a unit.
-/

noncomputable section

namespace GapFamily.Analytic

/-- The actual affine constrained response pencil. -/
def cuspMeanZeroPencil (z : ℂ) : ModularHilbert →L[ℂ] ModularHilbert :=
  compactSelfAdjointPencil cuspMeanZeroWeakResolvent z

@[simp] theorem cuspMeanZeroPencil_apply (z : ℂ) (f : ModularHilbert) :
    cuspMeanZeroPencil z f = f - (z + 1) • cuspMeanZeroWeakResolvent f := rfl

@[simp] theorem cuspMeanZeroPencil_neg_one : cuspMeanZeroPencil (-1) = 1 :=
  compactSelfAdjointPencil_neg_one cuspMeanZeroWeakResolvent

theorem cuspMeanZeroPencil_zero : cuspMeanZeroPencil 0 = 1 - cuspMeanZeroWeakResolvent := by
  simp [cuspMeanZeroPencil, compactSelfAdjointPencil]

theorem cuspMeanZeroPencil_isUnit_zero : IsUnit (cuspMeanZeroPencil 0) := by
  rw [cuspMeanZeroPencil_zero]
  exact cuspMeanZero_one_sub_resolvent_isUnit

/-- The actual constrained source solution family, using the totalized algebra inverse. -/
def cuspMeanZeroPencilSolution (z : ℂ) : ModularHilbert →L[ℂ] cuspMeanZeroForm :=
  cuspMeanZeroWeakSolution.comp (Ring.inverse (cuspMeanZeroPencil z))

theorem cuspMeanZeroPencilSolution_apply (z : ℂ) (f : ModularHilbert) :
    cuspMeanZeroPencilSolution z f =
      cuspMeanZeroWeakSolution (Ring.inverse (cuspMeanZeroPencil z) f) := rfl

theorem cuspMeanZeroPencil_apply_inverse {z : ℂ} (hz : IsUnit (cuspMeanZeroPencil z))
    (f : ModularHilbert) :
    cuspMeanZeroPencil z (Ring.inverse (cuspMeanZeroPencil z) f) = f := by
  have h := congrArg (fun A : ModularHilbert →L[ℂ] ModularHilbert => A f)
    (Ring.mul_inverse_cancel (cuspMeanZeroPencil z) hz)
  exact h

theorem cuspMeanZeroPencil_inverse_apply {z : ℂ} (hz : IsUnit (cuspMeanZeroPencil z))
    (f : ModularHilbert) :
    Ring.inverse (cuspMeanZeroPencil z) (cuspMeanZeroPencil z f) = f := by
  have h := congrArg (fun A : ModularHilbert →L[ℂ] ModularHilbert => A f)
    (Ring.inverse_mul_cancel (cuspMeanZeroPencil z) hz)
  exact h

/-- Conjugating the actual mass-plus-energy equation gives the test-first convention. -/
theorem cuspMeanZeroWeakSolution_equation_test_first (f : ModularHilbert) (v : cuspMeanZeroForm) :
    inner ℂ (cuspMeanZeroGradient v) (cuspMeanZeroGradient (cuspMeanZeroWeakSolution f)) +
      inner ℂ (meanZeroCuspEmbedding v) (cuspMeanZeroWeakResolvent f) =
        inner ℂ (meanZeroCuspEmbedding v) f := by
  have h := congrArg (starRingEnd ℂ) (cuspMeanZeroWeakSolution_equation f v)
  simpa only [map_add, inner_conj_symm] using h

theorem cuspMeanZeroWeakSolution_unique_test_first (f : ModularHilbert)
    (u : cuspMeanZeroForm)
    (hu : ∀ v : cuspMeanZeroForm,
      inner ℂ (cuspMeanZeroGradient v) (cuspMeanZeroGradient u) +
        inner ℂ (meanZeroCuspEmbedding v) (meanZeroCuspEmbedding u) =
          inner ℂ (meanZeroCuspEmbedding v) f) :
    u = cuspMeanZeroWeakSolution f := by
  apply cuspMeanZeroWeakSolution_unique f u
  intro v
  have h := congrArg (starRingEnd ℂ) (hu v)
  simpa only [map_add, inner_conj_symm] using h

end GapFamily.Analytic
