import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

noncomputable section
namespace GapFamily.Analytic.BesselCoshOrder

/-- The literal complex-order reciprocal Gaussian Mellin integrand. -/
def mellinIntegrand (κ : ℂ) (a b t : ℝ) : ℂ :=
  (t : ℂ) ^ (κ - 1) * Complex.exp (-(a : ℂ) * (t : ℂ) - (b : ℂ) / (t : ℂ))

/-- Positive scaling includes the genuine Jacobian and the exact complex-power factor. -/
theorem mellinIntegrand_scale {κ : ℂ} {a b c k t : ℝ}
    (hk : 0 < k) (ht : 0 < t) (hak : a * k = c) (hbk : b / k = c) :
    k • mellinIntegrand κ a b (k * t) = (k : ℂ) ^ κ * mellinIntegrand κ c c t := by
  have hkc : (k : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hk.ne'
  have hpow : (k : ℂ) * ((k * t : ℝ) : ℂ) ^ (κ - 1) =
      (k : ℂ) ^ κ * (t : ℂ) ^ (κ - 1) := by
    rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hk.le ht.le]
    have hp : (k : ℂ) * (k : ℂ) ^ (κ - 1) = (k : ℂ) ^ κ := by
      rw [Complex.cpow_sub κ 1 hkc, Complex.cpow_one]
      field_simp
    rw [← mul_assoc, hp]
  have her : -a * (k * t) - b / (k * t) = -c * t - c / t := by
    rw [neg_mul, ← mul_assoc, hak, div_mul_eq_div_div, hbk]
    ring
  have he : -(a : ℂ) * ((k * t : ℝ) : ℂ) - (b : ℂ) / ((k * t : ℝ) : ℂ) =
      -(c : ℂ) * (t : ℂ) - (c : ℂ) / (t : ℂ) := by
    exact_mod_cast her
  simp only [mellinIntegrand, Complex.real_smul]
  rw [he, ← mul_assoc, hpow, mul_assoc]

/-- The positive square-root scale symmetrizes both reciprocal Gaussian coefficients. -/
theorem mellin_sqrt_scale_data {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    0 < Real.sqrt b / Real.sqrt a ∧
      Real.sqrt b / Real.sqrt a = Real.sqrt (b / a) ∧
      a * (Real.sqrt b / Real.sqrt a) = Real.sqrt (a * b) ∧
      b / (Real.sqrt b / Real.sqrt a) = Real.sqrt (a * b) := by
  have hsa : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha
  have hsb : 0 < Real.sqrt b := Real.sqrt_pos.mpr hb
  refine ⟨div_pos hsb hsa, (Real.sqrt_div hb.le a).symm, ?_, ?_⟩
  · rw [Real.sqrt_mul ha.le]
    field_simp
    nlinarith [Real.sq_sqrt ha.le]
  · rw [Real.sqrt_mul ha.le]
    field_simp
    nlinarith [Real.sq_sqrt hb.le]

/-- The actual square-root substitution gives the symmetric Mellin kernel with its full factor. -/
theorem mellinIntegrand_sqrt_scale (κ : ℂ) {a b t : ℝ}
    (ha : 0 < a) (hb : 0 < b) (ht : 0 < t) :
    (Real.sqrt b / Real.sqrt a) •
        mellinIntegrand κ a b ((Real.sqrt b / Real.sqrt a) * t) =
      (Real.sqrt (b / a) : ℂ) ^ κ *
        mellinIntegrand κ (Real.sqrt (a * b)) (Real.sqrt (a * b)) t := by
  obtain ⟨hk, hkeq, hak, hbk⟩ := mellin_sqrt_scale_data ha hb
  simpa only [hkeq] using mellinIntegrand_scale (κ := κ) hk ht hak hbk

end GapFamily.Analytic.BesselCoshOrder
