import Mathlib.Analysis.InnerProductSpace.StarOrder
import GapFamily.Analytic.Foundation.CoerciveOperatorInverse

/-! Norm-energy control for positive operators on a complex Hilbert space. -/
noncomputable section
namespace GapFamily.Analytic

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The operator norm controls the squared response by the positive quadratic
energy, with constant one. No lower spectral bound is assumed. -/
theorem norm_sq_apply_le_norm_mul_energy (P : H →L[ℂ] H)
    (hP : P.IsPositive) (f : H) :
    ‖P f‖ ^ 2 ≤ ‖P‖ * (inner ℂ f (P f)).re := by
  obtain ⟨Q, hQ, _, hQQ⟩ :=
    CFC.exists_sqrt_of_isSelfAdjoint_of_quasispectrumRestricts
      hP.isSelfAdjoint hP.spectrumRestricts
  have hQsymm : Q.IsSymmetric :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hQ
  have hnorm : ‖Q‖ ^ 2 = ‖P‖ := by
    rw [← hQQ, hQ.norm_mul_self]
  have henergy : (inner ℂ f (P f)).re = ‖Q f‖ ^ 2 := by
    rw [← hQQ]
    change (inner ℂ f (Q (Q f))).re = _
    have hinner : inner ℂ (Q f) (Q f) = inner ℂ f (Q (Q f)) := hQsymm f (Q f)
    rw [← hinner]
    exact inner_self_eq_norm_sq (𝕜 := ℂ) (Q f)
  calc
    ‖P f‖ ^ 2 = ‖Q (Q f)‖ ^ 2 := by rw [← hQQ]; rfl
    _ ≤ (‖Q‖ * ‖Q f‖) ^ 2 := by
      gcongr
      exact Q.le_opNorm (Q f)
    _ = ‖P‖ * (inner ℂ f (P f)).re := by rw [mul_pow, hnorm, henergy]

/-- A supplied operator-norm bound may replace the exact norm in the energy
estimate, useful for quantitative propagation inequalities. -/
theorem norm_sq_apply_le_mul_energy (P : H →L[ℂ] H) (hP : P.IsPositive)
    {M : ℝ} (hM : ‖P‖ ≤ M) (f : H) :
    ‖P f‖ ^ 2 ≤ M * (inner ℂ f (P f)).re :=
  (norm_sq_apply_le_norm_mul_energy P hP f).trans
    (mul_le_mul_of_nonneg_right hM (hP.re_inner_nonneg_right f))

end GapFamily.Analytic
