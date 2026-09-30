import Mathlib.Analysis.InnerProductSpace.Positive

/-! A strictly coercive bounded operator on a complete complex Hilbert space
has an actual bounded inverse, with the reciprocal coercivity bound. -/

noncomputable section

namespace GapFamily.Analytic.CoerciveOperatorInverse

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Coercivity gives a lower bound on the norm of the operator's value. -/
theorem mul_norm_le_norm_apply_of_coercive (P : H →L[ℂ] H) {c : ℝ}
    (_hc : 0 < c) (hP : ∀ f, c * ‖f‖ ^ 2 ≤ (inner ℂ f (P f)).re) (f : H) :
    c * ‖f‖ ≤ ‖P f‖ := by
  by_cases hf : f = 0
  · simp [hf]
  · have hfpos : 0 < ‖f‖ := norm_pos_iff.mpr hf
    have h := (hP f).trans ((Complex.re_le_norm _).trans (norm_inner_le_norm _ _))
    nlinarith

variable [CompleteSpace H]

/-- Strict real-part coercivity implies invertibility, without a separate
self-adjointness or positivity assumption. -/
theorem isUnit_of_coercive (P : H →L[ℂ] H) {c : ℝ}
    (hc : 0 < c) (hP : ∀ f, c * ‖f‖ ^ 2 ≤ (inner ℂ f (P f)).re) :
    IsUnit P := by
  apply ContinuousLinearMap.isUnit_of_forall_le_norm_inner_map P
    (c := ⟨c, hc.le⟩) hc
  intro f
  change ‖f‖ ^ 2 * c ≤ ‖inner ℂ (P f) f‖
  calc
    ‖f‖ ^ 2 * c = c * ‖f‖ ^ 2 := mul_comm _ _
    _ ≤ (inner ℂ f (P f)).re := hP f
    _ = (inner ℂ (P f) f).re := inner_re_symm (𝕜 := ℂ) _ _
    _ ≤ ‖inner ℂ (P f) f‖ := Complex.re_le_norm _

theorem apply_inverse_of_coercive (P : H →L[ℂ] H) {c : ℝ}
    (hc : 0 < c) (hP : ∀ f, c * ‖f‖ ^ 2 ≤ (inner ℂ f (P f)).re) (f : H) :
    P (Ring.inverse P f) = f := by
  exact congrArg (fun Q : H →L[ℂ] H => Q f)
    (Ring.mul_inverse_cancel P (isUnit_of_coercive P hc hP))

theorem inverse_apply_of_coercive (P : H →L[ℂ] H) {c : ℝ}
    (hc : 0 < c) (hP : ∀ f, c * ‖f‖ ^ 2 ≤ (inner ℂ f (P f)).re) (f : H) :
    Ring.inverse P (P f) = f := by
  exact congrArg (fun Q : H →L[ℂ] H => Q f)
    (Ring.inverse_mul_cancel P (isUnit_of_coercive P hc hP))

/-- The inverse has the standard reciprocal coercivity bound. -/
theorem norm_inverse_le_of_coercive (P : H →L[ℂ] H) {c : ℝ}
    (hc : 0 < c) (hP : ∀ f, c * ‖f‖ ^ 2 ≤ (inner ℂ f (P f)).re) :
    ‖Ring.inverse P‖ ≤ c⁻¹ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.mpr hc.le)
  intro f
  have h := mul_norm_le_norm_apply_of_coercive P hc hP (Ring.inverse P f)
  rw [apply_inverse_of_coercive P hc hP] at h
  rw [← div_eq_inv_mul]
  exact (le_div_iff₀ hc).mpr (by simpa [mul_comm] using h)

end GapFamily.Analytic.CoerciveOperatorInverse
