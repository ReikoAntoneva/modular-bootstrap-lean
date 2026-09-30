import GapFamily.Analytic.Modular.ModularProjectedInversePositive

/-! The actual mean-zero resolvent of the unbounded modular Laplacian below
the proved quarter gap. Existing completed-form inverse and positivity proofs
discharge the analytic hypotheses. -/

noncomputable section
namespace GapFamily.Analytic.ModularMeanZeroResolvent
open ModularGradient ModularProjected

def meanZeroResolvent (a : ℝ) : ModularHilbert →L[ℂ] ModularHilbert :=
  projectedWeakResolvent.comp (Ring.inverse (projectedPencil (a : ℂ)))

theorem meanZeroResolvent_mem_domain (a : ℝ) (f : ModularHilbert) :
    meanZeroResolvent a f ∈ laplacian.domain := projectedWeakResolvent_mem_domain _

theorem meanZeroResolvent_mem_meanZero (a : ℝ) (f : ModularHilbert) :
    meanZeroResolvent a f ∈ modularMeanZero := projectedWeakResolvent_mem_meanZero _

theorem meanZeroResolvent_rightInverse (a : ℝ) (ha : a < 1 / 4) (f : ModularHilbert) :
    laplacian ⟨meanZeroResolvent a f, meanZeroResolvent_mem_domain a f⟩ -
      (a : ℂ) • meanZeroResolvent a f = modularMeanZeroProjection f :=
  projected_inverse_right_shift
    (projectedPencil_isUnit_regular (Or.inr (by simpa only [Complex.ofReal_re] using ha))) f

theorem meanZeroResolvent_leftInverse (a : ℝ) (ha : a < 1 / 4) (u : laplacian.domain) :
    meanZeroResolvent a (laplacian u - (a : ℂ) • (u : ModularHilbert)) =
      modularMeanZeroProjection u :=
  projected_inverse_left_shift
    (projectedPencil_isUnit_regular (Or.inr (by simpa only [Complex.ofReal_re] using ha))) u

/-- Genuine positivity follows from the actual quarter energy inequality. -/
theorem meanZeroResolvent_isPositive (a : ℝ) (ha : a < 1 / 4) :
    (meanZeroResolvent a).IsPositive := projectedInverse_isPositive_real ha

theorem meanZeroResolvent_isSelfAdjoint (a : ℝ) (ha : a < 1 / 4) :
    IsSelfAdjoint (meanZeroResolvent a) := (meanZeroResolvent_isPositive a ha).isSelfAdjoint

theorem projection_meanZeroResolvent (a : ℝ) (f : ModularHilbert) :
    modularMeanZeroProjection (meanZeroResolvent a f) = meanZeroResolvent a f :=
  modularMeanZero.starProjection_eq_self_iff.mpr (meanZeroResolvent_mem_meanZero a f)

theorem meanZeroResolvent_projection (a : ℝ) (ha : a < 1 / 4) (f : ModularHilbert) :
    meanZeroResolvent a (modularMeanZeroProjection f) = meanZeroResolvent a f := by
  have hQ : IsUnit (projectedPencil (a : ℂ)) :=
    projectedPencil_isUnit_regular (Or.inr (by simpa only [Complex.ofReal_re] using ha))
  change projectedWeakResolvent (Ring.inverse (projectedPencil (a : ℂ))
    (modularMeanZeroProjection f)) = projectedWeakResolvent (Ring.inverse (projectedPencil (a : ℂ)) f)
  rw [projected_response_inverse_commute hQ, projectedWeakResolvent_projection,
    projected_response_inverse_commute hQ]

end GapFamily.Analytic.ModularMeanZeroResolvent
