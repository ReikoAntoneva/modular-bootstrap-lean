import GapFamily.Analytic.Cusp.Fourier.CuspHorizontalProjectionPairing
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Orthogonal horizontal averaging on the actual cusp Hilbert space

The ordinary horizontal Fubini pairing on the dense automorphic core extends
to every cusp L² vector. It identifies the previously constructed bounded
average as a selfadjoint idempotent and its residual as the complementary
orthogonal projection.
-/

noncomputable section

namespace GapFamily.Analytic

/-- The actual horizontal average can be inserted in the second factor when
the first factor has already been averaged. -/
theorem cuspAverage_inner (H : ℝ) (hH : 1 ≤ H) (f g : cuspHilbert H) :
    inner ℂ (cuspAverage H hH f) g =
      inner ℂ (cuspAverage H hH f) (cuspAverage H hH g) := by
  refine (cuspCoreValue_dense_range H).induction_on₂
    (p := fun f g => inner ℂ (cuspAverage H hH f) g =
      inner ℂ (cuspAverage H hH f) (cuspAverage H hH g)) ?_ ?_ f g
  · exact isClosed_eq
      (((cuspAverage H hH).continuous.comp continuous_fst).inner continuous_snd)
      (((cuspAverage H hH).continuous.comp continuous_fst).inner
        ((cuspAverage H hH).continuous.comp continuous_snd))
  · intro F G
    simpa only [cuspAverage_core] using
      cuspCoreAverage_inner_coreValue_eq_average H hH F G

theorem cuspAverage_inner_symm (H : ℝ) (hH : 1 ≤ H) (f g : cuspHilbert H) :
    inner ℂ (cuspAverage H hH f) g = inner ℂ f (cuspAverage H hH g) := by
  have h := congrArg (starRingEnd ℂ) (cuspAverage_inner H hH g f)
  simp only [inner_conj_symm] at h
  exact (cuspAverage_inner H hH f g).trans h.symm

theorem cuspAverage_isSelfAdjoint (H : ℝ) (hH : 1 ≤ H) :
    IsSelfAdjoint (cuspAverage H hH) :=
  ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr (cuspAverage_inner_symm H hH)

theorem cuspAverage_idempotent (H : ℝ) (hH : 1 ≤ H) (f : cuspHilbert H) :
    cuspAverage H hH (cuspAverage H hH f) = cuspAverage H hH f := by
  apply ext_inner_right ℂ
  intro g
  exact (cuspAverage_inner_symm H hH (cuspAverage H hH f) g).trans
    (cuspAverage_inner H hH f g).symm

theorem cuspAverage_isIdempotent (H : ℝ) (hH : 1 ≤ H) :
    IsIdempotentElem (cuspAverage H hH) := by
  apply ContinuousLinearMap.ext
  exact cuspAverage_idempotent H hH

/-- The extended ordinary horizontal average is an actual orthogonal projection. -/
theorem cuspAverage_isStarProjection (H : ℝ) (hH : 1 ≤ H) :
    IsStarProjection (cuspAverage H hH) :=
  ⟨cuspAverage_isIdempotent H hH, cuspAverage_isSelfAdjoint H hH⟩

theorem cuspAverage_range_isClosed (H : ℝ) (hH : 1 ≤ H) :
    IsClosed ((cuspAverage H hH).range : Set (cuspHilbert H)) :=
  ContinuousLinearMap.IsIdempotentElem.isClosed_range (cuspAverage_isIdempotent H hH)

instance cuspAverage_range_hasOrthogonalProjection (H : ℝ) (hH : 1 ≤ H) :
    (cuspAverage H hH).range.HasOrthogonalProjection :=
  ContinuousLinearMap.IsIdempotentElem.hasOrthogonalProjection_range
    (cuspAverage_isIdempotent H hH)

theorem cuspAverage_eq_starProjection (H : ℝ) (hH : 1 ≤ H) :
    cuspAverage H hH = (cuspAverage H hH).range.starProjection := by
  obtain ⟨hR, h⟩ := isStarProjection_iff_eq_starProjection_range.mp
    (cuspAverage_isStarProjection H hH)
  exact h

/-- The zero-average channel is exactly orthogonal to the average range. -/
theorem cuspAverage_range_orthogonal (H : ℝ) (hH : 1 ≤ H) :
    (cuspAverage H hH).rangeᗮ = (cuspAverage H hH).ker := by
  rw [(cuspAverage H hH).orthogonal_range, (cuspAverage_isSelfAdjoint H hH).adjoint_eq]

theorem cuspAverage_eq_self_iff (H : ℝ) (hH : 1 ≤ H) (f : cuspHilbert H) :
    cuspAverage H hH f = f ↔ f ∈ (cuspAverage H hH).range := by
  constructor
  · intro hf
    exact ⟨f, hf⟩
  · rintro ⟨g, rfl⟩
    exact cuspAverage_idempotent H hH g

theorem cuspResidual_range_eq_average_ker (H : ℝ) (hH : 1 ≤ H) :
    (cuspResidual H hH).range = (cuspAverage H hH).ker :=
  (LinearMap.IsIdempotentElem.ker_eq_range
    (ContinuousLinearMap.IsIdempotentElem.toLinearMap (cuspAverage_isIdempotent H hH))).symm

theorem cuspResidual_ker_eq_average_range (H : ℝ) (hH : 1 ≤ H) :
    (cuspResidual H hH).ker = (cuspAverage H hH).range :=
  (LinearMap.IsIdempotentElem.range_eq_ker
    (ContinuousLinearMap.IsIdempotentElem.toLinearMap (cuspAverage_isIdempotent H hH))).symm

theorem cuspResidual_eq_starProjection (H : ℝ) (hH : 1 ≤ H) :
    cuspResidual H hH = (cuspAverage H hH).rangeᗮ.starProjection := by
  rw [Submodule.starProjection_orthogonal]
  exact congrArg (fun A => ContinuousLinearMap.id ℂ (cuspHilbert H) - A)
    (cuspAverage_eq_starProjection H hH)

theorem cuspResidual_isStarProjection (H : ℝ) (hH : 1 ≤ H) :
    IsStarProjection (cuspResidual H hH) :=
  (cuspAverage_isStarProjection H hH).one_sub

theorem cuspResidual_isSelfAdjoint (H : ℝ) (hH : 1 ≤ H) :
    IsSelfAdjoint (cuspResidual H hH) :=
  (cuspResidual_isStarProjection H hH).isSelfAdjoint

theorem cuspResidual_idempotent (H : ℝ) (hH : 1 ≤ H) (f : cuspHilbert H) :
    cuspResidual H hH (cuspResidual H hH f) = cuspResidual H hH f := by
  change (cuspResidual H hH * cuspResidual H hH) f = cuspResidual H hH f
  rw [(cuspResidual_isStarProjection H hH).isIdempotentElem.eq]

/-- The full Hilbert residual is a contraction, with the sharp projection bound. -/
theorem cuspResidual_norm_le_one (H : ℝ) (hH : 1 ≤ H) :
    ‖cuspResidual H hH‖ ≤ 1 := by
  rw [cuspResidual_eq_starProjection]
  exact Submodule.starProjection_norm_le _

theorem cuspResidual_norm_le_self (H : ℝ) (hH : 1 ≤ H) (f : cuspHilbert H) :
    ‖cuspResidual H hH f‖ ≤ ‖f‖ := by
  have h := (cuspResidual H hH).le_opNorm f
  have hb := cuspResidual_norm_le_one H hH
  nlinarith [norm_nonneg f]

theorem cuspAverage_inner_residual (H : ℝ) (hH : 1 ≤ H) (f g : cuspHilbert H) :
    inner ℂ (cuspAverage H hH f) (cuspResidual H hH g) = 0 := by
  rw [cuspResidual_apply, inner_sub_right, cuspAverage_inner, sub_self]

theorem cuspAverage_add_residual (H : ℝ) (hH : 1 ≤ H) (f : cuspHilbert H) :
    cuspAverage H hH f + cuspResidual H hH f = f := by
  rw [cuspResidual_apply, add_sub_cancel]

/-- The average and nonconstant part give the exact orthogonal mass decomposition. -/
theorem cuspAverage_residual_norm_sq (H : ℝ) (hH : 1 ≤ H) (f : cuspHilbert H) :
    ‖f‖ ^ 2 = ‖cuspAverage H hH f‖ ^ 2 + ‖cuspResidual H hH f‖ ^ 2 := by
  have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
    (cuspAverage H hH f) (cuspResidual H hH f) (cuspAverage_inner_residual H hH f f)
  simpa only [cuspResidual_apply, add_sub_cancel, ← sq] using h

theorem cuspAverage_residual_eq_zero (H : ℝ) (hH : 1 ≤ H) (f : cuspHilbert H) :
    cuspAverage H hH (cuspResidual H hH f) = 0 := by
  rw [cuspResidual_apply, map_sub, cuspAverage_idempotent, sub_self]

theorem cuspResidual_average_eq_zero (H : ℝ) (hH : 1 ≤ H) (f : cuspHilbert H) :
    cuspResidual H hH (cuspAverage H hH f) = 0 := by
  rw [cuspResidual_apply, cuspAverage_idempotent, sub_self]

end GapFamily.Analytic
