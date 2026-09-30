import GapFamily.Analytic.Poincare.Fourier.PoincareScalarThresholdNormalization

/-! Reality and a uniform spin bound for the actual scalar threshold coefficient. -/

noncomputable section

namespace GapFamily.Analytic.PoincareScalarFourier

open scoped ComplexConjugate

/-- The continued scalar threshold coefficient is real. -/
@[simp] theorem scalarThresholdCoefficient_im (J : ℤ) :
    (scalarThresholdCoefficient J).im = 0 := by
  unfold scalarThresholdCoefficient
  split_ifs <;> simp

@[simp] theorem conj_scalarThresholdCoefficient (J : ℤ) :
    conj (scalarThresholdCoefficient J) = scalarThresholdCoefficient J :=
  Complex.conj_eq_iff_im.mpr (scalarThresholdCoefficient_im J)

/-- Taking the real part loses none of the actual continued coefficient. -/
@[simp] theorem scalarThresholdCoefficient_re_coe (J : ℤ) :
    ((scalarThresholdCoefficient J).re : ℂ) = scalarThresholdCoefficient J := by
  apply Complex.ext
  · rfl
  · simp

/-- The elementary divisor-cardinality estimate bounds each nonzero spin. -/
theorem norm_scalarThresholdCoefficient_le_nonzero (J : ℤ) (hJ : J ≠ 0) :
    ‖scalarThresholdCoefficient J‖ ≤ 2 * |(J : ℝ)| := by
  have hd : (J.natAbs.divisors.card : ℝ) ≤ (J.natAbs : ℝ) := by
    exact_mod_cast Nat.card_divisors_le_self J.natAbs
  rw [Nat.cast_natAbs, Int.cast_abs] at hd
  simp only [scalarThresholdCoefficient, ite_eq_right hJ, norm_mul,
    Complex.norm_ofNat, norm_natCast]
  exact mul_le_mul_of_nonneg_left hd (by norm_num)

/-- One bound includes both the scalar coefficient `-1` and every divisor coefficient. -/
theorem norm_scalarThresholdCoefficient_le_max (J : ℤ) :
    ‖scalarThresholdCoefficient J‖ ≤ max 1 (2 * |(J : ℝ)|) := by
  by_cases hJ : J = 0
  · subst J
    simp
  · exact (norm_scalarThresholdCoefficient_le_nonzero J hJ).trans (le_max_right _ _)

theorem norm_scalarThresholdCoefficient_le (J : ℤ) :
    ‖scalarThresholdCoefficient J‖ ≤ 1 + 2 * |(J : ℝ)| := by
  apply (norm_scalarThresholdCoefficient_le_max J).trans
  apply max_le
  · linarith [abs_nonneg (J : ℝ)]
  · linarith

/-- The actual coefficient is uniformly bounded on every physical band. -/
theorem norm_scalarThresholdCoefficient_le_physical (J : ℤ) (B : ℝ)
    (hB : 1 ≤ B) (hJ : |(J : ℝ)| ≤ B) :
    ‖scalarThresholdCoefficient J‖ ≤ 3 * B := by
  exact (norm_scalarThresholdCoefficient_le J).trans (by linarith)

/-- The real mass functional has the same coefficient bound. -/
theorem abs_re_scalarThresholdCoefficient_le_physical (J : ℤ) (B : ℝ)
    (hB : 1 ≤ B) (hJ : |(J : ℝ)| ≤ B) :
    |(scalarThresholdCoefficient J).re| ≤ 3 * B :=
  (Complex.abs_re_le_norm _).trans (norm_scalarThresholdCoefficient_le_physical J B hB hJ)

end GapFamily.Analytic.PoincareScalarFourier
