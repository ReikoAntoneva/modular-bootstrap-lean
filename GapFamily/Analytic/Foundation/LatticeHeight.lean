import GapFamily.Analytic.Poincare.Poincare
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Defs

/-!
# The determinant-one lattice quadratic form

This shared quadratic form connects the scalar Poincaré series to its lattice
Dirichlet series and theta function. Integer rows use the same `Fin 2 → ℤ`
index as the primitive-row and gcd decomposition in pinned mathlib.
-/

namespace GapFamily.Analytic

open Complex Matrix Matrix.SpecialLinearGroup
open scoped Real MatrixGroups

noncomputable section

/-- The positive lattice quadratic form `|mz+n|² / Im z`. -/
def latticeEnergy (z : UpperHalfPlane) (v : Fin 2 → ℤ) : ℝ :=
  Complex.normSq ((v 0 : ℂ) * z + v 1) / z.im

/-- Right multiplication by an integral unimodular matrix permutes all lattice rows. -/
def latticeRowEquiv (g : SL(2, ℤ)) : (Fin 2 → ℤ) ≃ (Fin 2 → ℤ) where
  toFun v := v ᵥ* (g : Matrix (Fin 2) (Fin 2) ℤ)
  invFun v := v ᵥ* (g⁻¹ : SL(2, ℤ))
  left_inv v := by
    simp only [Matrix.vecMul_vecMul, ← Matrix.SpecialLinearGroup.coe_mul,
      mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one, Matrix.vecMul_one]
  right_inv v := by
    simp only [Matrix.vecMul_vecMul, ← Matrix.SpecialLinearGroup.coe_mul,
      inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one, Matrix.vecMul_one]

@[simp] theorem latticeRowEquiv_apply (g : SL(2, ℤ)) (v : Fin 2 → ℤ) :
    latticeRowEquiv g v = v ᵥ* (g : Matrix (Fin 2) (Fin 2) ℤ) := rfl

theorem latticeEnergy_eq_norm_sq (z : UpperHalfPlane) (v : Fin 2 → ℤ) :
    latticeEnergy z v = ‖(v 0 : ℂ) * z + v 1‖ ^ 2 / z.im := by
  rw [latticeEnergy, Complex.normSq_eq_norm_sq]

@[simp] theorem latticeEnergy_zero (z : UpperHalfPlane) : latticeEnergy z 0 = 0 := by
  simp [latticeEnergy]

theorem latticeEnergy_nonneg (z : UpperHalfPlane) (v : Fin 2 → ℤ) :
    0 ≤ latticeEnergy z v := div_nonneg (Complex.normSq_nonneg _) z.im_pos.le

/-- Coercivity with respect to the integer-row sup norm. -/
theorem latticeEnergy_norm_lower (z : UpperHalfPlane) (v : Fin 2 → ℤ) :
    (EisensteinSeries.r z) ^ 2 / z.im * ‖v‖ ^ 2 ≤ latticeEnergy z v := by
  by_cases hv : v = 0
  · simp [hv]
  have hnorm := EisensteinSeries.r_mul_max_le z hv
  rw [latticeEnergy_eq_norm_sq]
  calc
    _ = (EisensteinSeries.r z * ‖v‖) ^ 2 / z.im := by ring
    _ ≤ _ := div_le_div_of_nonneg_right
      (pow_le_pow_left₀ (mul_nonneg (EisensteinSeries.r_pos z).le (norm_nonneg v)) hnorm 2)
      z.im_pos.le

theorem latticeEnergy_pos (z : UpperHalfPlane) {v : Fin 2 → ℤ} (hv : v ≠ 0) :
    0 < latticeEnergy z v := by
  apply lt_of_lt_of_le _ (latticeEnergy_norm_lower z v)
  exact mul_pos (div_pos (sq_pos_of_pos (EisensteinSeries.r_pos z)) z.im_pos)
    (sq_pos_of_pos (norm_pos_iff.mpr hv))

@[simp] theorem latticeEnergy_neg (z : UpperHalfPlane) (v : Fin 2 → ℤ) :
    latticeEnergy z (-v) = latticeEnergy z v := by
  simp only [latticeEnergy, Pi.neg_apply, Int.cast_neg, neg_mul, ← neg_add]
  rw [Complex.normSq_neg]

theorem latticeEnergy_nsmul (z : UpperHalfPlane) (n : ℕ) (v : Fin 2 → ℤ) :
    latticeEnergy z (n • v) = (n : ℝ) ^ 2 * latticeEnergy z v := by
  have hlin : ((n • v) 0 : ℂ) * z + (n • v) 1 =
      (n : ℂ) * ((v 0 : ℂ) * z + v 1) := by
    simp [Pi.smul_apply]
    ring
  simp only [latticeEnergy, hlin, Complex.normSq_mul, Complex.normSq_natCast]
  ring

theorem latticeEnergy_inv (z : UpperHalfPlane) (v : Fin 2 → ℤ) :
    (latticeEnergy z v)⁻¹ = z.im / Complex.normSq ((v 0 : ℂ) * z + v 1) := by
  simp [latticeEnergy, inv_div]

/-- The summand of the scalar lattice Dirichlet series. Its zero-row value is
proved to vanish in the convergence region before it is included in sums. -/
def latticeDirichletTerm (z : UpperHalfPlane) (s : ℂ) (v : Fin 2 → ℤ) : ℂ :=
  (latticeEnergy z v : ℂ) ^ (-s)

@[simp] theorem latticeDirichletTerm_zero (z : UpperHalfPlane) {s : ℂ} (hs : s ≠ 0) :
    latticeDirichletTerm z s 0 = 0 := by
  simp [latticeDirichletTerm, Complex.zero_cpow (neg_ne_zero.mpr hs)]

theorem latticeDirichletTerm_eq_height (z : UpperHalfPlane) (s : ℂ) (v : Fin 2 → ℤ) :
    latticeDirichletTerm z s v =
      ((z.im / Complex.normSq ((v 0 : ℂ) * z + v 1) : ℝ) : ℂ) ^ s := by
  rw [latticeDirichletTerm, Complex.cpow_neg,
    ← Complex.inv_cpow_ofReal_nonneg (latticeEnergy_nonneg z v),
    ← Complex.ofReal_inv, latticeEnergy_inv]

theorem norm_latticeDirichletTerm (z : UpperHalfPlane) {s : ℂ} (hs : s.re ≠ 0)
    (v : Fin 2 → ℤ) :
    ‖latticeDirichletTerm z s v‖ =
      (z.im / Complex.normSq ((v 0 : ℂ) * z + v 1)) ^ s.re := by
  by_cases hv : v = 0
  · subst v
    have hs' : s ≠ 0 := fun h => hs (by simp [h])
    simp [latticeDirichletTerm_zero z hs', Real.zero_rpow hs]
  · rw [latticeDirichletTerm_eq_height]
    apply Complex.norm_cpow_eq_rpow_re_of_pos
    rw [← latticeEnergy_inv]
    exact inv_pos.mpr (latticeEnergy_pos z hv)

theorem summable_norm_latticeDirichletTerm (z : UpperHalfPlane) {s : ℂ} (hs : 1 < s.re) :
    Summable fun v : Fin 2 → ℤ => ‖latticeDirichletTerm z s v‖ := by
  simpa only [norm_latticeDirichletTerm z (ne_of_gt (lt_trans zero_lt_one hs))] using
    summable_poincare_height z hs

theorem summable_latticeDirichletTerm (z : UpperHalfPlane) {s : ℂ} (hs : 1 < s.re) :
    Summable (latticeDirichletTerm z s) :=
  (summable_norm_latticeDirichletTerm z hs).of_norm

theorem latticeDirichletTerm_nsmul (z : UpperHalfPlane) (s : ℂ)
    (n : ℕ) (v : Fin 2 → ℤ) :
    latticeDirichletTerm z s (n • v) =
      (1 / (n : ℂ) ^ (2 * s)) * latticeDirichletTerm z s v := by
  rw [latticeDirichletTerm, latticeEnergy_nsmul, Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg (sq_nonneg _) (latticeEnergy_nonneg z v),
    Complex.ofReal_pow, Complex.ofReal_natCast,
    ← Complex.natCast_cpow_natCast_mul n 2 (-s)]
  simp only [Nat.cast_ofNat, mul_neg, Complex.cpow_neg, one_div, latticeDirichletTerm]

open UpperHalfPlane in
/-- The Möbius action on the spatial point is exactly the unimodular change of
integer row in the determinant-one quadratic form. -/
theorem latticeEnergy_smul (g : SL(2, ℤ)) (z : UpperHalfPlane) (v : Fin 2 → ℤ) :
    latticeEnergy (g • z) v = latticeEnergy z (v ᵥ* (g : Matrix (Fin 2) (Fin 2) ℤ)) := by
  have hlin : (v 0 : ℂ) * ((g • z : UpperHalfPlane) : ℂ) + v 1 =
      (denom g z)⁻¹ * (((v ᵥ* (g : Matrix (Fin 2) (Fin 2) ℤ)) 0 : ℂ) * z +
        (v ᵥ* (g : Matrix (Fin 2) (Fin 2) ℤ)) 1) := by
    simpa only [EisensteinSeries.eisSummand, neg_neg, zpow_one, zpow_neg_one] using
      EisensteinSeries.eisSummand_SL2_apply (-1) v g z
  have hden : Complex.normSq (denom g z) ≠ 0 :=
    (Complex.normSq_pos.mpr (denom_ne_zero g z)).ne'
  rw [latticeEnergy, hlin, Complex.normSq_mul, Complex.normSq_inv,
    ModularGroup.im_smul_eq_div_normSq, latticeEnergy]
  field_simp

theorem latticeEnergy_smul_eq (g : SL(2, ℤ)) (z : UpperHalfPlane) (v : Fin 2 → ℤ) :
    latticeEnergy (g • z) v = latticeEnergy z (latticeRowEquiv g v) :=
  latticeEnergy_smul g z v

end

end GapFamily.Analytic
