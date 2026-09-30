import GapFamily.Analytic.Poincare.Seed.PoincareSeedHigher

noncomputable section

namespace GapFamily.Analytic.PoincareEnergyFactorHigher

open Set UpperHalfPlane PoincareSeedHigher
open scoped Topology ContDiff

/-- A finite explicit coefficient retaining the order-zero gain in height. -/
def energyDerivativeConstant (n : ℕ) (E : ℂ) (M : ℝ) : ℝ :=
  if n = 0 then
    (2 * Real.pi * ‖E‖) * Real.exp ((2 * Real.pi * ‖E‖) * M)
  else
    (2 * Real.pi * ‖E‖) ^ n * Real.exp ((2 * Real.pi * ‖E‖) * M) * (1 + M) ^ n

theorem energyDerivativeConstant_nonneg (n : ℕ) (E : ℂ) {M : ℝ} (hM : 0 ≤ M) :
    0 ≤ energyDerivativeConstant n E M := by
  unfold energyDerivativeConstant
  split <;> positivity

private theorem norm_energyCoefficient (E : ℂ) :
    ‖-2 * (Real.pi : ℂ) * E‖ = 2 * Real.pi * ‖E‖ := by
  simp [Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]

theorem iteratedDeriv_realExp_sub_one_succ (n : ℕ) (c : ℂ) (x : ℝ) :
    iteratedDeriv (n + 1) (fun t : ℝ => Complex.exp (c * (t : ℂ)) - 1) x =
      c ^ (n + 1) * Complex.exp (c * (x : ℂ)) := by
  have he : (fun t : ℝ => Complex.exp (c * (t : ℂ)) - 1) =
      fun t : ℝ => (-1 : ℂ) + Complex.exp (c * (t : ℂ)) := by
    funext t
    ring
  rw [he, iteratedDeriv_const_add (Nat.succ_pos n), iteratedDeriv_realExp]

theorem norm_iteratedDeriv_realExp_sub_one_succ_le (n : ℕ) (c : ℂ) {y M : ℝ}
    (hy : 0 ≤ y) (hM : y ≤ M) :
    ‖iteratedDeriv (n + 1) (fun t : ℝ => Complex.exp (c * (t : ℂ)) - 1) y‖ ≤
      ‖c‖ ^ (n + 1) * Real.exp (‖c‖ * M) := by
  rw [iteratedDeriv_realExp_sub_one_succ, norm_mul, norm_pow, Complex.norm_exp]
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg (norm_nonneg c) _)
  apply Real.exp_le_exp.mpr
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  exact (mul_le_mul_of_nonneg_right (Complex.re_le_norm c) hy).trans
    (mul_le_mul_of_nonneg_left hM (norm_nonneg c))

/-- The actual exponential remainder supplies the extra height factor at order zero. -/
theorem norm_realExp_sub_one_le (c : ℂ) {y M : ℝ} (hy : 0 < y) (hM : y ≤ M) :
    ‖Complex.exp (c * (y : ℂ)) - 1‖ ≤ (‖c‖ * Real.exp (‖c‖ * M)) * y := by
  have h0 : ‖Complex.exp (c * (y : ℂ)) - 1‖ ≤
      (‖c‖ * y) * Real.exp (‖c‖ * y) := by
    simpa [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hy] using
      Complex.norm_exp_sub_sum_le_norm_mul_exp (c * (y : ℂ)) 1
  calc
    _ ≤ (‖c‖ * y) * Real.exp (‖c‖ * y) := h0
    _ ≤ (‖c‖ * y) * Real.exp (‖c‖ * M) := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg (norm_nonneg _) hy.le)
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hM (norm_nonneg _))
    _ = _ := by ring

private theorem one_le_height_order (n : ℕ) {y M : ℝ} (hy : 0 < y) (hM : y ≤ M) :
    1 ≤ (1 + M) ^ (n + 1) * y ^ (1 - ((n + 1 : ℕ) : ℝ)) := by
  have hM0 : 0 ≤ M := hy.le.trans hM
  have hp : y ^ n ≤ (1 + M) ^ (n + 1) :=
    (pow_le_pow_left₀ hy.le (by linarith : y ≤ 1 + M) n).trans
      (pow_le_pow_right₀ (by linarith : 1 ≤ 1 + M) (Nat.le_succ n))
  have he : (1 - ((n + 1 : ℕ) : ℝ)) = -(n : ℝ) := by push_cast; ring
  rw [he]
  calc
    1 = y ^ n * y ^ (-(n : ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hy]
      simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hp (Real.rpow_nonneg hy.le _)

/-- Every scalar derivative has the stated inverse-height order, including
the sharper order-zero vanishing, for arbitrary complex energy. -/
theorem norm_iteratedDeriv_energyFactor_le (n : ℕ) (E : ℂ) {y M : ℝ}
    (hy : 0 < y) (hM : y ≤ M) :
    ‖iteratedDeriv n (fun t : ℝ =>
        Complex.exp ((-2 * (Real.pi : ℂ) * E) * (t : ℂ)) - 1) y‖ ≤
      energyDerivativeConstant n E M * y ^ (1 - (n : ℝ)) := by
  cases n with
  | zero =>
      simpa [energyDerivativeConstant, norm_energyCoefficient] using
        norm_realExp_sub_one_le (-2 * (Real.pi : ℂ) * E) hy hM
  | succ n =>
      have hb := norm_iteratedDeriv_realExp_sub_one_succ_le n
        (-2 * (Real.pi : ℂ) * E) hy.le hM
      rw [norm_energyCoefficient] at hb
      refine hb.trans ?_
      have hheight := one_le_height_order n hy hM
      have hcoeff : 0 ≤ (2 * Real.pi * ‖E‖) ^ (n + 1) *
          Real.exp ((2 * Real.pi * ‖E‖) * M) := by positivity
      have hm := mul_le_mul_of_nonneg_left hheight hcoeff
      simpa only [mul_one, energyDerivativeConstant, Nat.succ_ne_zero,
        ite_false, mul_assoc] using hm

private theorem imCLM_norm_le : ‖Complex.imCLM‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro z
  simpa only [Complex.imCLM_apply, Real.norm_eq_abs, one_mul] using Complex.abs_im_le_norm z

/-- The literal spatial energy factor has the same all-order bound after the
actual real-linear height map. The bound is for the full multilinear norm. -/
theorem norm_iteratedFDeriv_energyFactor_le (n : ℕ) (E : ℂ) (τ : UpperHalfPlane)
    {M : ℝ} (hM : τ.im ≤ M) :
    ‖iteratedFDeriv ℝ n (fun z : ℂ =>
        Complex.exp ((-2 * (Real.pi : ℂ) * E) * (z.im : ℂ)) - 1) (τ : ℂ)‖ ≤
      energyDerivativeConstant n E M * τ.im ^ (1 - (n : ℝ)) := by
  let f : ℝ → ℂ := fun t => Complex.exp ((-2 * (Real.pi : ℂ) * E) * (t : ℂ)) - 1
  have hf : ContDiff ℝ n f :=
    (contDiff_const.mul Complex.ofRealCLM.contDiff).cexp.sub contDiff_const
  change ‖iteratedFDeriv ℝ n (f ∘ Complex.imCLM) (τ : ℂ)‖ ≤ _
  rw [Complex.imCLM.iteratedFDeriv_comp_right hf (τ : ℂ) le_rfl]
  calc
    _ ≤ ‖iteratedFDeriv ℝ n f τ.im‖ * ‖Complex.imCLM‖ ^ n := by
      simpa using (iteratedFDeriv ℝ n f τ.im).norm_compContinuousLinearMap_le
        (fun _ : Fin n => Complex.imCLM)
    _ ≤ ‖iteratedFDeriv ℝ n f τ.im‖ := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left
        (pow_le_one₀ (norm_nonneg _) imCLM_norm_le) (norm_nonneg _)
    _ ≤ _ := by
      rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
      exact norm_iteratedDeriv_energyFactor_le n E τ.im_pos hM

end GapFamily.Analytic.PoincareEnergyFactorHigher
