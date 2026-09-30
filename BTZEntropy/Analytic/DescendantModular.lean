import BTZEntropy.Analytic.DescendantEta
import GapFamily.Analytic.Foundation.Eta

/-!
# Modular inversion of the descendant Euler product

This is the exact positive-temperature identity for the actual reciprocal Euler
product.  The exponential retains both finite `1/24` shifts from eta.
-/

noncomputable section

namespace BTZEntropy

/-- The inverse temperature obtained by the modular `S` transformation. -/
def dualTemperature (β : ℝ) : ℝ := 4 * Real.pi ^ 2 / β

theorem dualTemperature_pos {β : ℝ} (hβ : 0 < β) : 0 < dualTemperature β := by
  unfold dualTemperature
  positivity

/-- The thermal points are related by the literal complex modular inversion. -/
theorem thermalPoint_dual (β : ℝ) (hβ : 0 < β) :
    (thermalPoint (dualTemperature β) (dualTemperature_pos hβ) : ℂ) =
      -1 / (thermalPoint β hβ : ℂ) := by
  symm
  apply (div_eq_iff (thermalPoint β hβ).ne_zero).2
  change -1 = (((dualTemperature β / (2 * Real.pi) : ℝ) : ℂ) * Complex.I) *
    (((β / (2 * Real.pi) : ℝ) : ℂ) * Complex.I)
  unfold dualTemperature
  push_cast
  have hβc : (β : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hβ.ne'
  have hπc : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp
  simp [Complex.I_sq]
  ring

theorem norm_thermalPoint (β : ℝ) (hβ : 0 < β) :
    ‖(thermalPoint β hβ : ℂ)‖ = β / (2 * Real.pi) := by
  change ‖((β / (2 * Real.pi) : ℝ) : ℂ) * Complex.I‖ = _
  rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (div_pos hβ (by positivity))]

/-- Squared eta norm in terms of the positive descendant product. -/
theorem eta_norm_sq_thermalPoint (β : ℝ) (hβ : 0 < β) :
    ‖ModularForm.eta (thermalPoint β hβ : ℂ)‖ ^ 2 =
      Real.exp (-β / 12) / descendantEuler β ^ 2 := by
  rw [eta_thermalPoint, Complex.norm_real, Real.norm_eq_abs, sq_abs, mul_pow,
    inv_pow, div_eq_mul_inv]
  congr 1
  rw [← Real.exp_nat_mul]
  congr 1
  ring

/-- Exact modular inversion of the actual thermal Euler product. -/
theorem descendantEuler_sq_dual (β : ℝ) (hβ : 0 < β) :
    descendantEuler β ^ 2 =
      (β / (2 * Real.pi)) * Real.exp ((dualTemperature β - β) / 12) *
        descendantEuler (dualTemperature β) ^ 2 := by
  have hdual := dualTemperature_pos hβ
  have h := GapFamily.Analytic.eta_norm_sq_neg_inv (thermalPoint β hβ)
  rw [← thermalPoint_dual, norm_thermalPoint,
    eta_norm_sq_thermalPoint, eta_norm_sq_thermalPoint] at h
  have hcross : Real.exp (-dualTemperature β / 12) * descendantEuler β ^ 2 =
      (β / (2 * Real.pi)) * Real.exp (-β / 12) *
        descendantEuler (dualTemperature β) ^ 2 := by
    have h₁ := (descendantEuler_pos hβ).ne'
    have h₂ := (descendantEuler_pos hdual).ne'
    rw [← mul_div_assoc] at h
    exact (div_eq_div_iff (pow_ne_zero 2 h₂) (pow_ne_zero 2 h₁)).mp h
  have hexp : Real.exp (-dualTemperature β / 12) *
      Real.exp ((dualTemperature β - β) / 12) = Real.exp (-β / 12) := by
    rw [← Real.exp_add]
    congr 1
    ring
  apply mul_left_cancel₀ (Real.exp_ne_zero (-dualTemperature β / 12))
  rw [hcross]
  calc
    _ = (β / (2 * Real.pi)) *
        (Real.exp (-dualTemperature β / 12) *
          Real.exp ((dualTemperature β - β) / 12)) *
          descendantEuler (dualTemperature β) ^ 2 := by rw [hexp]
    _ = _ := by ring

/-- Expanded-temperature version of the exact descendant inversion identity. -/
theorem descendantEuler_sq_inversion (β : ℝ) (hβ : 0 < β) :
    descendantEuler β ^ 2 =
      (β / (2 * Real.pi)) * Real.exp ((4 * Real.pi ^ 2 / β - β) / 12) *
        descendantEuler (4 * Real.pi ^ 2 / β) ^ 2 :=
  descendantEuler_sq_dual β hβ

end BTZEntropy
