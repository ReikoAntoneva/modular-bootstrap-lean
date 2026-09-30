/-
Copyright (c) 2025 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler

The nonparabolic reciprocal-height estimate is adapted from the final height
estimate in Mathlib/NumberTheory/ModularForms/Bounds.lean at mathlib commit
5ed2965256430c3649e86755f9576b54eca72435, as extracted in ModularSeamCover.
The closed fundamental-domain denominator bound and its consequences are
project additions.
-/

import Mathlib.NumberTheory.Modular

noncomputable section

namespace GapFamily.Analytic

open Set Matrix UpperHalfPlane ModularGroup
open scoped MatrixGroups UpperHalfPlane

theorem one_le_normSq_denom_of_mem_fd (g : SL(2, ℤ)) {τ : ℍ}
    (hτ : τ ∈ ModularGroup.fd) :
    1 ≤ Complex.normSq (UpperHalfPlane.denom g τ) := by
  have heq : Complex.normSq (UpperHalfPlane.denom g τ) =
      ((g 1 0 : ℝ) * τ.re + (g 1 1 : ℝ)) ^ 2 + (g 1 0 : ℝ) ^ 2 * τ.im ^ 2 := by
    rw [ModularGroup.denom_apply]
    simp [Complex.normSq_apply]
    ring
  rw [heq]
  have hnorm : 1 ≤ τ.re ^ 2 + τ.im ^ 2 := by
    simpa [Complex.normSq_apply, pow_two] using hτ.1
  have hre : |2 * τ.re| ≤ 1 := by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith [hτ.2]
  by_cases hc : |g 1 0| ≤ 1
  · rcases Int.abs_le_one_iff.mp hc with hc | hc | hc
    · have hd : g 1 1 ≠ 0 := fun hd => zero_ne_one <| by
        simpa only [Matrix.det_fin_two, hc, hd, mul_zero, sub_zero] using g.det_coe
      have hd2 : (1 : ℝ) ≤ (g 1 1 : ℝ) ^ 2 := by
        exact_mod_cast (one_le_sq_iff_one_le_abs (g 1 1)).mpr (Int.one_le_abs hd)
      simpa [hc] using hd2
    · have ht := Int.nneg_mul_add_sq_of_abs_le_one (g 1 1) hre
      simp only [hc, Int.cast_one, one_mul, one_pow] at *
      nlinarith
    · have hren : |-(2 * τ.re)| ≤ 1 := by simpa only [abs_neg] using hre
      have ht := Int.nneg_mul_add_sq_of_abs_le_one (g 1 1) hren
      simp only [hc, Int.cast_neg, Int.cast_one, neg_one_mul, neg_one_sq, one_mul] at *
      nlinarith
  · have hcabs : (2 : ℤ) ≤ |g 1 0| := by omega
    have hc2i : (4 : ℤ) ≤ (g 1 0) ^ 2 := by
      nlinarith [sq_abs (g 1 0)]
    have hc2 : (4 : ℝ) ≤ (g 1 0 : ℝ) ^ 2 := by exact_mod_cast hc2i
    have him := ModularGroup.three_le_four_mul_im_sq_of_mem_fd hτ
    have hmul := mul_le_mul_of_nonneg_right hc2 (sq_nonneg τ.im)
    nlinarith [sq_nonneg ((g 1 0 : ℝ) * τ.re + (g 1 1 : ℝ))]

/-- A point of the actual closed modular fundamental domain has maximal orbit height. -/
theorem modular_smul_im_le_of_mem_fd (g : SL(2, ℤ)) {τ : ℍ}
    (hτ : τ ∈ ModularGroup.fd) : (g • τ).im ≤ τ.im := by
  rw [ModularGroup.im_smul_eq_div_normSq]
  exact div_le_self τ.im_pos.le (one_le_normSq_denom_of_mem_fd g hτ)

/-- A nonzero integral lower-left entry gives the sharper reciprocal-height estimate. -/
theorem modular_smul_im_le_inv_of_lowerLeft_ne_zero (g : SL(2, ℤ)) (τ : ℍ)
    (hg : g 1 0 ≠ 0) : (g • τ).im ≤ 1 / τ.im := by
  rw [ModularGroup.im_smul_eq_div_normSq, ModularGroup.denom_apply]
  rw [show 1 / τ.im = τ.im / τ.im ^ 2 by field_simp]
  gcongr
  rw [show Complex.normSq ((g 1 0) * τ + (g 1 1)) =
    ((g 1 0) * τ.re + (g 1 1)) ^ 2 + (g 1 0) ^ 2 * τ.im ^ 2 by
      simp [Complex.normSq_apply]
      ring]
  have hc2 : (1 : ℝ) ≤ g 1 0 ^ 2 :=
    mod_cast (one_le_sq_iff_one_le_abs _).mpr (Int.one_le_abs hg)
  nlinarith

/-- Every nonparabolic translate of a point above height one lies strictly below height one. -/
theorem modular_smul_im_lt_one_of_lowerLeft_ne_zero (g : SL(2, ℤ)) (τ : ℍ)
    (hg : g 1 0 ≠ 0) (hτ : 1 < τ.im) : (g • τ).im < 1 := by
  apply (modular_smul_im_le_inv_of_lowerLeft_ne_zero g τ hg).trans_lt
  exact (div_lt_one τ.im_pos).mpr hτ

/-- On the closed fundamental domain every nonparabolic translate has height at most one. -/
theorem modular_smul_im_le_one_of_mem_fd_of_lowerLeft_ne_zero (g : SL(2, ℤ))
    {τ : ℍ} (hτ : τ ∈ ModularGroup.fd) (hg : g 1 0 ≠ 0) : (g • τ).im ≤ 1 := by
  by_cases h : τ.im ≤ 1
  · exact (modular_smul_im_le_of_mem_fd g hτ).trans h
  · exact (modular_smul_im_lt_one_of_lowerLeft_ne_zero g τ hg (lt_of_not_ge h)).le

end GapFamily.Analytic
