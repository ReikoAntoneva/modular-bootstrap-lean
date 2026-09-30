import GapFamily.Analytic.Foundation.FullVacuumRemainder
import GapFamily.Analytic.Kernel.FullKernelReality

/-! The real ordinary numerator of the actual four-seed vacuum. -/

noncomputable section

namespace GapFamily.Analytic

open scoped ComplexConjugate

/-- The real continuum numerator of the full canonical vacuum completion. -/
def vacuumNumerator (a e : ℝ) (j : ℤ) : ℝ := (vacuumFullKernel a e j).re

@[simp] theorem conj_vacuumFullKernel (a e : ℝ) (j : ℤ) :
    conj (vacuumFullKernel a e j) = vacuumFullKernel a e j := by
  simp only [vacuumFullKernel, map_add, map_sub, conj_fullKernelHol,
    Complex.conj_ofReal, map_neg, map_one, map_ofNat]

@[simp] theorem vacuumFullKernel_im (a e : ℝ) (j : ℤ) :
    (vacuumFullKernel a e j).im = 0 :=
  Complex.conj_eq_iff_im.mp (conj_vacuumFullKernel a e j)

/-- Taking the real numerator loses no part of the canonical vacuum output. -/
@[simp] theorem vacuumNumerator_coe_eq (a e : ℝ) (j : ℤ) :
    (vacuumNumerator a e j : ℂ) = vacuumFullKernel a e j := by
  apply Complex.ext
  · rfl
  · simp

/-- The complex remainder bound is exactly the real density error bound. -/
theorem abs_vacuumNumerator_sub_eq_norm (a e : ℝ) (j : ℤ) :
    |vacuumNumerator a e j - vacuumLeading a e j| =
      ‖vacuumFullRemainder a e j‖ := by
  rw [← Real.norm_eq_abs, ← Complex.norm_real, Complex.ofReal_sub,
    vacuumNumerator_coe_eq]
  rfl

@[simp] theorem vacuumNumerator_scalar_endpoint (a : ℝ) :
    vacuumNumerator a 0 0 = 0 := by
  simp [vacuumNumerator]

/-- The actual real vacuum numerator satisfies the uniform C5 approximation
with room for the subsequent marker reference correction. -/
theorem exists_vacuumNumerator_uniform_error_bound :
    ∃ A : ℝ, 100 ≤ A ∧ ∀ (a e : ℝ) (j : ℤ),
      A ≤ a → 1 ≤ e → |(j : ℝ)| ≤ e →
      |vacuumNumerator a e j - vacuumLeading a e j| ≤
        Real.exp (7 * Real.sqrt (a * e)) / 4 := by
  obtain ⟨A, hA, hbound⟩ := exists_vacuumFullRemainder_uniform_exp_bound
  refine ⟨max 100 A, le_max_left _ _, ?_⟩
  intro a e j ha he hj
  rw [abs_vacuumNumerator_sub_eq_norm]
  exact hbound a e j ((le_max_right _ _).trans ha) he hj

/-- The canonical real vacuum retains the spin-edge lower factor after its
full continued arithmetic and higher-denominator error is included. -/
theorem vacuumNumerator_lower_bound (a e : ℝ) (j : ℤ)
    (ha : 100 ≤ a) (he : |(j : ℝ)| ≤ e) :
    (2 * Real.pi ^ 4 / 625) * (e ^ 2 - (j : ℝ) ^ 2) *
        Real.exp (8 * Real.sqrt (a * e)) - ‖vacuumFullRemainder a e j‖ ≤
      vacuumNumerator a e j := by
  have hl := vacuumLeading_ge_exp a e j ha he
  have herr := (abs_le.mp (le_of_eq (abs_vacuumNumerator_sub_eq_norm a e j))).1
  linarith

end GapFamily.Analytic
