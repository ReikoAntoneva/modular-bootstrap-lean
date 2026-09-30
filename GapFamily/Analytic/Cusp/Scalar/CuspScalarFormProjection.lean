import GapFamily.Analytic.Cusp.Scalar.CuspScalarOrthogonal

/-!
# The ambient scalar cusp projection

Restriction to the cusp, actual horizontal averaging, and extension by zero
define a contractive orthogonal projection on the full modular Hilbert space.
Every compact scalar cusp profile is fixed by this projection.
-/

noncomputable section

namespace GapFamily.Analytic

open Set ModularGradient
open scoped ContDiff

/-- The scalar cusp channel inside the full modular Hilbert space. -/
def cuspScalarProjection : ModularHilbert →L[ℂ] ModularHilbert :=
  (cuspZeroExtension 1).toContinuousLinearMap.comp
    ((cuspAverage 1 le_rfl).comp (cuspRestrict 1))

theorem cuspScalarProjection_apply (f : ModularHilbert) :
    cuspScalarProjection f = cuspZeroExtend 1 (cuspAverage 1 le_rfl (cuspRestrict 1 f)) := rfl

/-- Scalar projection does not increase the ambient Hilbert norm. -/
theorem cuspScalarProjection_norm_le (f : ModularHilbert) :
    ‖cuspScalarProjection f‖ ≤ ‖f‖ := by
  rw [cuspScalarProjection_apply, cuspZeroExtend_norm]
  exact (cuspAverage_norm_le 1 le_rfl (cuspRestrict 1 f)).trans (norm_cuspRestrict_le 1 f)

theorem cuspScalarProjection_norm_le_one : ‖cuspScalarProjection‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  simpa only [one_mul] using cuspScalarProjection_norm_le f

theorem cuspScalarProjection_idempotent (f : ModularHilbert) :
    cuspScalarProjection (cuspScalarProjection f) = cuspScalarProjection f := by
  simp only [cuspScalarProjection_apply, cuspRestrict_zeroExtend, cuspAverage_idempotent]

theorem cuspScalarProjection_isIdempotent : IsIdempotentElem cuspScalarProjection := by
  apply ContinuousLinearMap.ext
  exact cuspScalarProjection_idempotent

/-- The scalar cusp projection is symmetric for the actual ambient inner product. -/
theorem cuspScalarProjection_inner_symm (f g : ModularHilbert) :
    inner ℂ (cuspScalarProjection f) g = inner ℂ f (cuspScalarProjection g) := by
  rw [cuspScalarProjection_apply, cuspZeroExtend_inner_restrict, cuspAverage_inner_symm]
  have h := congrArg (starRingEnd ℂ)
    (cuspZeroExtend_inner_restrict 1 (cuspAverage 1 le_rfl (cuspRestrict 1 g)) f)
  simp only [inner_conj_symm] at h
  exact h.symm

theorem cuspScalarProjection_isSelfAdjoint : IsSelfAdjoint cuspScalarProjection :=
  ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr cuspScalarProjection_inner_symm

theorem cuspScalarProjection_isStarProjection : IsStarProjection cuspScalarProjection :=
  ⟨cuspScalarProjection_isIdempotent, cuspScalarProjection_isSelfAdjoint⟩

/-- Actual compact scalar profiles lie in the fixed space of the ambient projection. -/
theorem cuspScalarProjection_cuspProfileCore (b : ℝ → ℂ) (hb : ContDiff ℝ ∞ b)
    (hc : HasCompactSupport b) (hs : tsupport b ⊆ Ioi (1 : ℝ)) :
    cuspScalarProjection (value (cuspProfileCore b hb hc hs)) =
      value (cuspProfileCore b hb hc hs) := by
  rw [cuspScalarProjection_apply, cuspAverage_cuspProfileCore,
    cuspProfileCore_value_zeroExtend]

end GapFamily.Analytic
