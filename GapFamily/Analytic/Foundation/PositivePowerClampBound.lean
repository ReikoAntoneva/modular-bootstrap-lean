import Mathlib.Analysis.SpecialFunctions.Pow.Real

noncomputable section

namespace GapFamily.Analytic

/-- A positive lower clamp changes complex powers uniformly by a small amount
on every closed sub-half-plane with positive real part. -/
theorem positivePower_clamp_bound {p ε δ : ℝ} {s : ℂ}
    (hp : 0 < p) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hδ : 0 < δ) (hs : δ ≤ s.re) :
    ‖((max ε p : ℝ) : ℂ) ^ s - (p : ℂ) ^ s‖ ≤ 2 * ε ^ δ := by
  by_cases hεp : ε ≤ p
  · rw [max_eq_right hεp, sub_self, norm_zero]
    exact mul_nonneg zero_le_two (Real.rpow_nonneg hε.le δ)
  · have hpε : p ≤ ε := (lt_of_not_ge hεp).le
    rw [max_eq_left hpε]
    have hpow : ε ^ s.re ≤ ε ^ δ :=
      Real.rpow_le_rpow_of_exponent_ge hε hε1 hs
    have hεnorm : ‖(ε : ℂ) ^ s‖ ≤ ε ^ δ := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hε]
      exact hpow
    have hpnorm : ‖(p : ℂ) ^ s‖ ≤ ε ^ δ := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hp]
      exact (Real.rpow_le_rpow hp.le hpε (hδ.le.trans hs)).trans hpow
    calc
      ‖(ε : ℂ) ^ s - (p : ℂ) ^ s‖ ≤ ‖(ε : ℂ) ^ s‖ + ‖(p : ℂ) ^ s‖ :=
        norm_sub_le _ _
      _ ≤ ε ^ δ + ε ^ δ := add_le_add hεnorm hpnorm
      _ = 2 * ε ^ δ := (two_mul (ε ^ δ)).symm

end GapFamily.Analytic
