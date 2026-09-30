import GapFamily.Analytic.Transform.CosRootHalfLaplace

noncomputable section
namespace BTZEntropy

/-- Real normalization of the chiral Gaussian transform at positive inverse temperature. -/
theorem chiralGaussianNormalization (a : ℝ) {β : ℝ} (hβ : 0 < β) :
    (Real.sqrt Real.pi : ℂ) * ((β / 2 : ℝ) : ℂ) ^ (-(1 / 2 : ℂ)) *
      Complex.exp (-((-4 * Real.pi ^ 2 * a : ℝ) : ℂ) /
        (4 * ((β / 2 : ℝ) : ℂ))) =
      ((Real.sqrt (2 * Real.pi / β) * Real.exp (2 * Real.pi ^ 2 * a / β) : ℝ) : ℂ) := by
  have hb : 0 ≤ β / 2 := by positivity
  have hc : (-(1 / 2 : ℂ)) = ((-(1 / 2 : ℝ) : ℝ) : ℂ) := by push_cast; rfl
  rw [hc, ← Complex.ofReal_cpow hb]
  have he : -((-4 * Real.pi ^ 2 * a : ℝ) : ℂ) /
      (4 * ((β / 2 : ℝ) : ℂ)) = ((2 * Real.pi ^ 2 * a / β : ℝ) : ℂ) := by
    push_cast
    field_simp
  rw [he, ← Complex.ofReal_exp, ← Complex.ofReal_mul, ← Complex.ofReal_mul]
  congr 2
  rw [Real.rpow_neg hb, ← Real.sqrt_eq_rpow, ← div_eq_mul_inv,
    ← Real.sqrt_div Real.pi_pos.le]
  congr 1
  ring

/-- The same normalization after taking the real part. -/
theorem chiralGaussianNormalization_re (a : ℝ) {β : ℝ} (hβ : 0 < β) :
    ((Real.sqrt Real.pi : ℂ) * ((β / 2 : ℝ) : ℂ) ^ (-(1 / 2 : ℂ)) *
      Complex.exp (-((-4 * Real.pi ^ 2 * a : ℝ) : ℂ) /
        (4 * ((β / 2 : ℝ) : ℂ)))).re =
      Real.sqrt (2 * Real.pi / β) * Real.exp (2 * Real.pi ^ 2 * a / β) := by
  rw [chiralGaussianNormalization a hβ]
  rfl

end BTZEntropy
