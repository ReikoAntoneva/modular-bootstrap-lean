import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Complex.Exponential

/-!
# The scalar Dirichlet cusp Green kernel

The finite integral defines the removable extension at spectral parameter zero.
With `κ=s-1/2`, the scalar channel is `-∂ₜ²+κ²`, since
`s(1-s)=1/4-κ²`. No modular gluing or operator realization is asserted here.
-/

noncomputable section

namespace GapFamily.Analytic

open MeasureTheory Set

/-- The removable scalar Green kernel, defined by an ordinary finite integral. -/
def cuspGreen (t₀ t u : ℝ) (κ : ℂ) : ℂ :=
  (∫ v : ℝ in |t-u|..(t+u-2*t₀), Complex.exp (-κ * v)) / 2

/-- The defining finite integral is ordinarily integrable at every complex parameter. -/
theorem cuspGreen_intervalIntegrable (t₀ t u : ℝ) (κ : ℂ) :
    IntervalIntegrable (fun v : ℝ => Complex.exp (-κ * v)) volume |t-u| (t+u-2*t₀) :=
  (by fun_prop : Continuous (fun v : ℝ => Complex.exp (-κ * v))).intervalIntegrable _ _

/-- Agreement with the outgoing closed formula away from its removable denominator. -/
theorem cuspGreen_eq_quotient (t₀ t u : ℝ) {κ : ℂ} (hκ : κ ≠ 0) :
    cuspGreen t₀ t u κ =
      (Complex.exp (-κ * (|t-u| : ℝ)) - Complex.exp (-κ * ((t+u-2*t₀ : ℝ) : ℂ))) /
        (2 * κ) := by
  unfold cuspGreen
  rw [integral_exp_mul_complex (neg_ne_zero.mpr hκ)]
  ring

/-- The threshold kernel is the actual removable value `min(t,u)-t₀`. -/
@[simp] theorem cuspGreen_zero (t₀ t u : ℝ) :
    cuspGreen t₀ t u 0 = ((min t u - t₀ : ℝ) : ℂ) := by
  unfold cuspGreen
  simp only [neg_zero, zero_mul, Complex.exp_zero, intervalIntegral.integral_const, Complex.real_smul,
    mul_one]
  rcases le_total t u with h | h
  · rw [min_eq_left h, abs_of_nonpos (sub_nonpos.mpr h)]
    push_cast
    ring
  · rw [min_eq_right h, abs_of_nonneg (sub_nonneg.mpr h)]
    push_cast
    ring

/-- Symmetry in the two scalar-channel positions. -/
theorem cuspGreen_symm (t₀ t u : ℝ) (κ : ℂ) :
    cuspGreen t₀ t u κ = cuspGreen t₀ u t κ := by
  unfold cuspGreen
  rw [abs_sub_comm t u, add_comm t u]

/-- The Dirichlet boundary value vanishes, including at the threshold parameter. -/
@[simp] theorem cuspGreen_boundary_left (t₀ u : ℝ) (hu : t₀ ≤ u) (κ : ℂ) :
    cuspGreen t₀ t₀ u κ = 0 := by
  unfold cuspGreen
  rw [abs_of_nonpos (sub_nonpos.mpr hu)]
  have heq : -(t₀-u) = t₀+u-2*t₀ := by ring
  rw [heq, intervalIntegral.integral_same, zero_div]

/-- Symmetry gives the second Dirichlet boundary value. -/
@[simp] theorem cuspGreen_boundary_right (t₀ t : ℝ) (ht : t₀ ≤ t) (κ : ℂ) :
    cuspGreen t₀ t t₀ κ = 0 := by
  rw [cuspGreen_symm, cuspGreen_boundary_left t₀ t ht]

end GapFamily.Analytic
