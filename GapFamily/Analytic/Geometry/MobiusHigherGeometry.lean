import GapFamily.Analytic.Geometry.LaplacianMobiusAction

noncomputable section

open Matrix UpperHalfPlane
open scoped MatrixGroups

namespace GapFamily.Analytic.MobiusHigher

/-- The actual imaginary part of the Möbius denominator controls its norm. -/
theorem abs_bottomLeft_mul_im_le_norm_denom (γ : SL(2, ℝ)) (τ : UpperHalfPlane) :
    |γ 1 0| * τ.im ≤ ‖UpperHalfPlane.denom (γ : GL (Fin 2) ℝ) τ‖ := by
  have him : (UpperHalfPlane.denom (γ : GL (Fin 2) ℝ) τ).im = γ 1 0 * τ.im := by
    simp [UpperHalfPlane.denom]
  have h := Complex.abs_im_le_norm (UpperHalfPlane.denom (γ : GL (Fin 2) ℝ) τ)
  rwa [him, abs_mul, abs_of_pos τ.im_pos] at h

/-- The denominator ratio is bounded by the reciprocal original height,
including the affine case with zero bottom-left entry. -/
theorem norm_bottomLeft_div_denom_le (γ : SL(2, ℝ)) (τ : UpperHalfPlane) :
    ‖((γ 1 0 : ℝ) : ℂ) / UpperHalfPlane.denom (γ : GL (Fin 2) ℝ) τ‖ ≤ 1 / τ.im := by
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs]
  apply (div_le_div_iff₀
    (norm_pos_iff.mpr (UpperHalfPlane.denom_ne_zero (γ : GL (Fin 2) ℝ) τ)) τ.im_pos).mpr
  simpa only [one_mul] using abs_bottomLeft_mul_im_le_norm_denom γ τ

/-- The exact first-derivative norm is the transformed-height ratio. -/
theorem norm_one_div_denom_sq_eq_height_ratio (γ : SL(2, ℝ)) (τ : UpperHalfPlane) :
    ‖1 / UpperHalfPlane.denom (γ : GL (Fin 2) ℝ) τ ^ 2‖ =
      (γ • τ : UpperHalfPlane).im / τ.im := by
  have him : (γ • τ : UpperHalfPlane).im =
      τ.im / Complex.normSq (UpperHalfPlane.denom (γ : GL (Fin 2) ℝ) τ) := by
    change ((γ : GL (Fin 2) ℝ) • τ : UpperHalfPlane).im = _
    simpa using UpperHalfPlane.im_smul_eq_div_normSq (γ : GL (Fin 2) ℝ) τ
  rw [him, Complex.normSq_eq_norm_sq, norm_div, norm_one, norm_pow]
  field_simp [τ.im_ne_zero]

theorem norm_deriv_rawRealModularAction_eq_height_ratio
    (γ : SL(2, ℝ)) (τ : UpperHalfPlane) :
    ‖deriv (LaplacianCovariance.rawRealModularAction γ) τ‖ =
      (γ • τ : UpperHalfPlane).im / τ.im := by
  rw [LaplacianCovariance.deriv_rawRealModularAction]
  exact norm_one_div_denom_sq_eq_height_ratio γ τ

theorem norm_bottomLeft_div_denom_int_le (γ : SL(2, ℤ)) (τ : UpperHalfPlane) :
    ‖(γ 1 0 : ℂ) / UpperHalfPlane.denom (γ : GL (Fin 2) ℝ) τ‖ ≤ 1 / τ.im := by
  simpa using norm_bottomLeft_div_denom_le (γ : SL(2, ℝ)) τ

theorem norm_one_div_denom_sq_int_eq_height_ratio (γ : SL(2, ℤ)) (τ : UpperHalfPlane) :
    ‖1 / UpperHalfPlane.denom (γ : GL (Fin 2) ℝ) τ ^ 2‖ =
      (γ • τ : UpperHalfPlane).im / τ.im :=
  norm_one_div_denom_sq_eq_height_ratio (γ : SL(2, ℝ)) τ

/-- The actual geometric factors in an order-`n` Möbius derivative already have
the desired factorial height bound. This is a bound on explicit factors, not an
assumed identification of any higher derivative. -/
theorem factorial_mobius_factors_le (γ : SL(2, ℝ)) (τ : UpperHalfPlane)
    (n : ℕ) (hn : 1 ≤ n) :
    (n.factorial : ℝ) * ‖1 / UpperHalfPlane.denom (γ : GL (Fin 2) ℝ) τ ^ 2‖ *
        ‖((γ 1 0 : ℝ) : ℂ) / UpperHalfPlane.denom (γ : GL (Fin 2) ℝ) τ‖ ^ (n - 1) ≤
      (n.factorial : ℝ) * (γ • τ : UpperHalfPlane).im / τ.im ^ n := by
  calc
    _ ≤ (n.factorial : ℝ) * ‖1 / UpperHalfPlane.denom (γ : GL (Fin 2) ℝ) τ ^ 2‖ *
        (1 / τ.im) ^ (n - 1) := by
      gcongr
      exact norm_bottomLeft_div_denom_le γ τ
    _ = (n.factorial : ℝ) * ((γ • τ : UpperHalfPlane).im / τ.im) *
        (1 / τ.im) ^ (n - 1) := by
      rw [norm_one_div_denom_sq_eq_height_ratio]
    _ = _ := by
      have hp : τ.im ^ n = τ.im ^ (n - 1) * τ.im := by
        rw [← pow_succ, Nat.sub_add_cancel hn]
      rw [hp, div_pow, one_pow]
      field_simp [τ.im_ne_zero]

theorem factorial_mobius_factors_int_le (γ : SL(2, ℤ)) (τ : UpperHalfPlane)
    (n : ℕ) (hn : 1 ≤ n) :
    (n.factorial : ℝ) * ‖1 / UpperHalfPlane.denom (γ : GL (Fin 2) ℝ) τ ^ 2‖ *
        ‖(γ 1 0 : ℂ) / UpperHalfPlane.denom (γ : GL (Fin 2) ℝ) τ‖ ^ (n - 1) ≤
      (n.factorial : ℝ) * (γ • τ : UpperHalfPlane).im / τ.im ^ n := by
  have h := factorial_mobius_factors_le (γ : SL(2, ℝ)) τ n hn
  have hsmul : ((γ : SL(2, ℝ)) • τ : UpperHalfPlane) = (γ • τ : UpperHalfPlane) := rfl
  rw [hsmul] at h
  simpa using h

end GapFamily.Analytic.MobiusHigher
