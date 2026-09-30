import GapFamily.Analytic.Cusp.Green.CuspGreenBasic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Complex.RealDeriv

/-!
# Classical scalar cusp Green equation

These are ordinary real-position derivatives of the actual finite-integral kernel.
The two one-sided derivatives have jump `-1`, appropriate to `-∂ₜ²+κ²`.
No realization of the modular Laplacian or distributional gluing is assumed.
-/

noncomputable section

namespace GapFamily.Analytic

open Set Filter
open scoped Topology

/-- The smoothly extended derivative from the side `t ≤ u`. -/
def cuspGreenLeftSlope (t₀ t u : ℝ) (κ : ℂ) : ℂ :=
  (Complex.exp (-κ * ((u-t : ℝ) : ℂ)) +
    Complex.exp (-κ * ((t+u-2*t₀ : ℝ) : ℂ))) / 2

/-- The smoothly extended derivative from the side `u ≤ t`. -/
def cuspGreenRightSlope (t₀ t u : ℝ) (κ : ℂ) : ℂ :=
  (-Complex.exp (-κ * ((t-u : ℝ) : ℂ)) +
    Complex.exp (-κ * ((t+u-2*t₀ : ℝ) : ℂ))) / 2

private theorem cuspExp_hasDerivAt (κ : ℂ) (α β t : ℝ) :
    HasDerivAt (fun v : ℝ => Complex.exp (-κ * ((α*v+β : ℝ) : ℂ)))
      ((-κ * (α : ℂ)) * Complex.exp (-κ * ((α*t+β : ℝ) : ℂ))) t := by
  convert (((((hasDerivAt_id t).const_mul α).add_const β).ofReal_comp).const_mul
    (-κ)).cexp using 1 <;> simp
  ring

private theorem cuspExp_left_hasDerivAt (κ : ℂ) (u t : ℝ) :
    HasDerivAt (fun v : ℝ => Complex.exp (-κ * ((u-v : ℝ) : ℂ)))
      (κ * Complex.exp (-κ * ((u-t : ℝ) : ℂ))) t := by
  simpa [sub_eq_add_neg, add_comm] using cuspExp_hasDerivAt κ (-1) u t

private theorem cuspExp_right_hasDerivAt (κ : ℂ) (u t : ℝ) :
    HasDerivAt (fun v : ℝ => Complex.exp (-κ * ((v-u : ℝ) : ℂ)))
      (-κ * Complex.exp (-κ * ((t-u : ℝ) : ℂ))) t := by
  simpa only [one_mul, Complex.ofReal_one, mul_one, sub_eq_add_neg] using
    cuspExp_hasDerivAt κ 1 (-u) t

private theorem cuspExp_reflected_hasDerivAt (κ : ℂ) (t₀ u t : ℝ) :
    HasDerivAt (fun v : ℝ => Complex.exp (-κ * ((v+u-2*t₀ : ℝ) : ℂ)))
      (-κ * Complex.exp (-κ * ((t+u-2*t₀ : ℝ) : ℂ))) t := by
  simpa only [one_mul, Complex.ofReal_one, mul_one, sub_eq_add_neg, add_assoc] using
    cuspExp_hasDerivAt κ 1 (u-2*t₀) t

private theorem cuspGreen_leftFormula_hasDerivAt (t₀ t u : ℝ) {κ : ℂ} (hκ : κ ≠ 0) :
    HasDerivAt (fun v : ℝ =>
      (Complex.exp (-κ * ((u-v : ℝ) : ℂ)) -
        Complex.exp (-κ * ((v+u-2*t₀ : ℝ) : ℂ))) / (2*κ))
      (cuspGreenLeftSlope t₀ t u κ) t := by
  convert ((cuspExp_left_hasDerivAt κ u t).sub
    (cuspExp_reflected_hasDerivAt κ t₀ u t)).div_const (2*κ) using 1
  unfold cuspGreenLeftSlope
  field_simp
  ring

private theorem cuspGreen_rightFormula_hasDerivAt (t₀ t u : ℝ) {κ : ℂ} (hκ : κ ≠ 0) :
    HasDerivAt (fun v : ℝ =>
      (Complex.exp (-κ * ((v-u : ℝ) : ℂ)) -
        Complex.exp (-κ * ((v+u-2*t₀ : ℝ) : ℂ))) / (2*κ))
      (cuspGreenRightSlope t₀ t u κ) t := by
  convert ((cuspExp_right_hasDerivAt κ u t).sub
    (cuspExp_reflected_hasDerivAt κ t₀ u t)).div_const (2*κ) using 1
  unfold cuspGreenRightSlope
  field_simp
  ring

/-- The ordinary derivative within the whole left closed half-line, including its endpoint. -/
theorem cuspGreen_hasDerivWithinAt_left (t₀ t u : ℝ) (ht : t ≤ u) (κ : ℂ) :
    HasDerivWithinAt (fun v : ℝ => cuspGreen t₀ v u κ)
      (cuspGreenLeftSlope t₀ t u κ) (Iic u) t := by
  by_cases hκ : κ = 0
  · subst κ
    have h := (((hasDerivAt_id t).sub_const t₀).ofReal_comp).hasDerivWithinAt
      (s := Iic u)
    have hs : cuspGreenLeftSlope t₀ t u 0 = 1 := by norm_num [cuspGreenLeftSlope]
    rw [hs]
    apply h.congr_of_mem
    · intro v hv
      simp only [cuspGreen_zero, min_eq_left (show v ≤ u from hv), id_eq]
    · exact ht
  · apply (cuspGreen_leftFormula_hasDerivAt t₀ t u hκ).hasDerivWithinAt.congr_of_mem
    · intro v hv
      rw [cuspGreen_eq_quotient _ _ _ hκ, abs_of_nonpos (sub_nonpos.mpr hv), neg_sub]
    · exact ht

/-- The ordinary derivative within the whole right closed half-line, including its endpoint. -/
theorem cuspGreen_hasDerivWithinAt_right (t₀ t u : ℝ) (ht : u ≤ t) (κ : ℂ) :
    HasDerivWithinAt (fun v : ℝ => cuspGreen t₀ v u κ)
      (cuspGreenRightSlope t₀ t u κ) (Ici u) t := by
  by_cases hκ : κ = 0
  · subst κ
    have h := (hasDerivAt_const t ((u-t₀ : ℝ) : ℂ)).hasDerivWithinAt (s := Ici u)
    have hs : cuspGreenRightSlope t₀ t u 0 = 0 := by norm_num [cuspGreenRightSlope]
    rw [hs]
    apply h.congr_of_mem
    · intro v hv
      simp only [cuspGreen_zero, min_eq_right (show u ≤ v from hv)]
    · exact ht
  · apply (cuspGreen_rightFormula_hasDerivAt t₀ t u hκ).hasDerivWithinAt.congr_of_mem
    · intro v hv
      rw [cuspGreen_eq_quotient _ _ _ hκ, abs_of_nonneg (sub_nonneg.mpr hv)]
    · exact ht

/-- Ordinary first derivative strictly to the left of the source. -/
theorem cuspGreen_hasDerivAt_left (t₀ t u : ℝ) (ht : t < u) (κ : ℂ) :
    HasDerivAt (fun v : ℝ => cuspGreen t₀ v u κ)
      (cuspGreenLeftSlope t₀ t u κ) t :=
  (cuspGreen_hasDerivWithinAt_left t₀ t u ht.le κ).hasDerivAt (Iic_mem_nhds ht)

/-- Ordinary first derivative strictly to the right of the source. -/
theorem cuspGreen_hasDerivAt_right (t₀ t u : ℝ) (ht : u < t) (κ : ℂ) :
    HasDerivAt (fun v : ℝ => cuspGreen t₀ v u κ)
      (cuspGreenRightSlope t₀ t u κ) t :=
  (cuspGreen_hasDerivWithinAt_right t₀ t u ht.le κ).hasDerivAt (Ici_mem_nhds ht)

/-- The left slope differentiates to `κ²G`, including at the threshold parameter. -/
theorem cuspGreenLeftSlope_hasDerivAt (t₀ t u : ℝ) (ht : t ≤ u) (κ : ℂ) :
    HasDerivAt (fun v : ℝ => cuspGreenLeftSlope t₀ v u κ)
      (κ^2 * cuspGreen t₀ t u κ) t := by
  by_cases hκ : κ = 0
  · subst κ
    simpa [cuspGreenLeftSlope] using hasDerivAt_const t (1 : ℂ)
  · change HasDerivAt (fun v : ℝ =>
      (Complex.exp (-κ * ((u-v : ℝ) : ℂ)) +
        Complex.exp (-κ * ((v+u-2*t₀ : ℝ) : ℂ))) / 2) _ _
    apply (((cuspExp_left_hasDerivAt κ u t).add
      (cuspExp_reflected_hasDerivAt κ t₀ u t)).div_const 2).congr_deriv
    rw [cuspGreen_eq_quotient _ _ _ hκ, abs_of_nonpos (sub_nonpos.mpr ht), neg_sub]
    field_simp
    ring

/-- The right slope differentiates to `κ²G`, including at the threshold parameter. -/
theorem cuspGreenRightSlope_hasDerivAt (t₀ t u : ℝ) (ht : u ≤ t) (κ : ℂ) :
    HasDerivAt (fun v : ℝ => cuspGreenRightSlope t₀ v u κ)
      (κ^2 * cuspGreen t₀ t u κ) t := by
  by_cases hκ : κ = 0
  · subst κ
    simpa [cuspGreenRightSlope] using hasDerivAt_const t (0 : ℂ)
  · change HasDerivAt (fun v : ℝ =>
      (-Complex.exp (-κ * ((v-u : ℝ) : ℂ)) +
        Complex.exp (-κ * ((v+u-2*t₀ : ℝ) : ℂ))) / 2) _ _
    apply (((cuspExp_right_hasDerivAt κ u t).neg.add
      (cuspExp_reflected_hasDerivAt κ t₀ u t)).div_const 2).congr_deriv
    rw [cuspGreen_eq_quotient _ _ _ hκ, abs_of_nonneg (sub_nonneg.mpr ht)]
    field_simp
    ring

/-- Ordinary second derivative off the diagonal. The derivative is taken in real position. -/
theorem cuspGreen_hasDerivAt_deriv (t₀ t u : ℝ) (ht : t ≠ u) (κ : ℂ) :
    HasDerivAt (deriv (fun v : ℝ => cuspGreen t₀ v u κ))
      (κ^2 * cuspGreen t₀ t u κ) t := by
  rcases lt_or_gt_of_ne ht with h | h
  · apply (cuspGreenLeftSlope_hasDerivAt t₀ t u h.le κ).congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds h] with v hv
    exact (cuspGreen_hasDerivAt_left t₀ v u hv κ).deriv
  · apply (cuspGreenRightSlope_hasDerivAt t₀ t u h.le κ).congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds h] with v hv
    exact (cuspGreen_hasDerivAt_right t₀ v u hv κ).deriv

/-- The classical homogeneous scalar Green equation away from its source. -/
theorem cuspGreen_scalar_equation (t₀ t u : ℝ) (ht : t ≠ u) (κ : ℂ) :
    -deriv (deriv (fun v : ℝ => cuspGreen t₀ v u κ)) t +
      κ^2 * cuspGreen t₀ t u κ = 0 := by
  rw [(cuspGreen_hasDerivAt_deriv t₀ t u ht κ).deriv]
  ring

/-- The actual derivative from the left at the source. -/
theorem cuspGreen_hasDerivWithinAt_source_left (t₀ u : ℝ) (κ : ℂ) :
    HasDerivWithinAt (fun v : ℝ => cuspGreen t₀ v u κ)
      ((1 + Complex.exp (-κ * ((u+u-2*t₀ : ℝ) : ℂ))) / 2) (Iic u) u := by
  simpa [cuspGreenLeftSlope] using cuspGreen_hasDerivWithinAt_left t₀ u u le_rfl κ

/-- The actual derivative from the right at the source. -/
theorem cuspGreen_hasDerivWithinAt_source_right (t₀ u : ℝ) (κ : ℂ) :
    HasDerivWithinAt (fun v : ℝ => cuspGreen t₀ v u κ)
      ((-1 + Complex.exp (-κ * ((u+u-2*t₀ : ℝ) : ℂ))) / 2) (Ici u) u := by
  simpa [cuspGreenRightSlope] using cuspGreen_hasDerivWithinAt_right t₀ u u le_rfl κ

/-- The right derivative minus the left derivative is `-1`, including `κ=0`. -/
theorem cuspGreen_derivative_jump (t₀ u : ℝ) (κ : ℂ) :
    cuspGreenRightSlope t₀ u u κ - cuspGreenLeftSlope t₀ u u κ = -1 := by
  simp only [cuspGreenRightSlope, cuspGreenLeftSlope, sub_self, Complex.ofReal_zero,
    mul_zero, Complex.exp_zero]
  ring

end GapFamily.Analytic
