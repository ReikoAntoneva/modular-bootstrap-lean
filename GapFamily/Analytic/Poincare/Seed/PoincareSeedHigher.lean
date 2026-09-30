import GapFamily.Analytic.Poincare.PoincarePowerHigher
import GapFamily.Analytic.Poincare.PoincareTermRegularity
import Mathlib.Analysis.Calculus.ContDiff.Bounds

noncomputable section
namespace GapFamily.Analytic.PoincareSeedHigher
open Set UpperHalfPlane PoincareSeedGradient PoincarePowerHigher
open scoped Topology ContDiff

/-- The scalar complex exponential differentiated with respect to a real variable. -/
theorem iteratedDeriv_realExp (n : ℕ) (c : ℂ) (x : ℝ) :
    iteratedDeriv n (fun t : ℝ => Complex.exp (c * t)) x =
      c ^ n * Complex.exp (c * x) := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
      have he : iteratedDeriv n (fun t : ℝ => Complex.exp (c * t)) =
          fun t : ℝ => c ^ n * Complex.exp (c * t) := funext ih
      rw [iteratedDeriv_succ, he]
      have hd := (((hasDerivAt_id (x : ℂ)).const_mul c).cexp).comp_ofReal
      simp only [id_eq, mul_one] at hd
      rw [(hd.const_mul (c ^ n)).deriv]
      simp only [pow_succ]
      ring

private theorem reCLM_norm_le : ‖Complex.reCLM‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro z
  simpa only [Complex.reCLM_apply, Real.norm_eq_abs, one_mul] using Complex.abs_re_le_norm z

private theorem imCLM_norm_le : ‖Complex.imCLM‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro z
  simpa only [Complex.imCLM_apply, Real.norm_eq_abs, one_mul] using Complex.abs_im_le_norm z

/-- Phase derivatives have a global bound independent of the spatial point. -/
theorem norm_iteratedFDeriv_phase_le (n : ℕ) (J : ℤ) (z : ℂ) :
    ‖iteratedFDeriv ℝ n (fun w : ℂ =>
      Complex.exp (((2 * Real.pi * (J : ℝ) * w.re : ℝ) : ℂ) * Complex.I)) z‖ ≤
      (2 * Real.pi * |(J : ℝ)|) ^ n := by
  let c : ℂ := ((2 * Real.pi * (J : ℝ) : ℝ) : ℂ) * Complex.I
  let f : ℝ → ℂ := fun t => Complex.exp (c * t)
  have hf : ContDiff ℝ n f := by
    exact ((contDiff_const.mul Complex.ofRealCLM.contDiff) :
      ContDiff ℝ n (fun t : ℝ => c * (t : ℂ))).cexp
  have he : (fun w : ℂ =>
      Complex.exp (((2 * Real.pi * (J : ℝ) * w.re : ℝ) : ℂ) * Complex.I)) =
      f ∘ Complex.reCLM := by
    funext w
    dsimp [f, c]
    congr 1
    push_cast
    ring
  rw [he, Complex.reCLM.iteratedFDeriv_comp_right hf z le_rfl]
  calc
    _ ≤ ‖iteratedFDeriv ℝ n f z.re‖ * ‖Complex.reCLM‖ ^ n := by
      simpa using (iteratedFDeriv ℝ n f z.re).norm_compContinuousLinearMap_le
        (fun _ : Fin n => Complex.reCLM)
    _ ≤ ‖iteratedFDeriv ℝ n f z.re‖ := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left
        (pow_le_one₀ (norm_nonneg _) reCLM_norm_le) (norm_nonneg _)
    _ = _ := by
      rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_realExp, norm_mul, norm_pow]
      dsimp [c]
      have hp : ((2 * Real.pi * (J : ℝ) : ℝ) : ℂ) * Complex.I * (z.re : ℂ) =
          ((2 * Real.pi * (J : ℝ) * z.re : ℝ) : ℂ) * Complex.I := by push_cast; ring
      rw [hp, Complex.norm_exp_ofReal_mul_I]
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I,
        mul_one, abs_of_pos Real.pi_pos, abs_of_pos (by norm_num : (0 : ℝ) < 2)]

/-- The height power has the required inverse-height order after the actual
real-linear imaginary-coordinate map. -/
theorem norm_iteratedFDeriv_heightPower_le (n : ℕ) {s : ℂ} {S : ℝ} (hs : ‖s‖ ≤ S)
    (τ : UpperHalfPlane) :
    ‖iteratedFDeriv ℝ n (fun z : ℂ => (z.im : ℂ) ^ s) (τ : ℂ)‖ ≤
      (S + (n : ℝ)) ^ n * τ.im ^ (s.re - (n : ℝ)) := by
  have he := Complex.imCLM.iteratedFDerivWithin_comp_right
    (contDiffOn_realPower (n := n) s) isOpen_Ioi.uniqueDiffOn
    isOpen_upperHalfPlaneSet.uniqueDiffOn τ.im_pos le_rfl
  have hR := iteratedFDerivWithin_of_isOpen (𝕜 := ℝ)
    (f := fun y : ℝ => (y : ℂ) ^ s) n isOpen_Ioi τ.im_pos
  have hC := iteratedFDerivWithin_of_isOpen (𝕜 := ℝ)
    (f := fun z : ℂ => (z.im : ℂ) ^ s) n isOpen_upperHalfPlaneSet τ.im_pos
  change iteratedFDerivWithin ℝ n (fun z : ℂ => (z.im : ℂ) ^ s) upperHalfPlaneSet τ =
    (iteratedFDerivWithin ℝ n (fun y : ℝ => (y : ℂ) ^ s) (Ioi 0) τ.im).compContinuousLinearMap
       (fun _ : Fin n => Complex.imCLM) at he
  rw [hR, hC] at he
  rw [he]
  calc
    _ ≤ ‖iteratedFDeriv ℝ n (fun y : ℝ => (y : ℂ) ^ s) τ.im‖ * ‖Complex.imCLM‖ ^ n := by
      simpa using (iteratedFDeriv ℝ n (fun y : ℝ => (y : ℂ) ^ s) τ.im).norm_compContinuousLinearMap_le
         (fun _ : Fin n => Complex.imCLM)
    _ ≤ ‖iteratedFDeriv ℝ n (fun y : ℝ => (y : ℂ) ^ s) τ.im‖ := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left
        (pow_le_one₀ (norm_nonneg _) imCLM_norm_le) (norm_nonneg _)
    _ ≤ _ := norm_iteratedFDeriv_realPower_le n hs τ.im_pos

private theorem height_power_le (n i : ℕ) (hi : i ≤ n) {y : ℝ} (hy : 0 < y) (t : ℝ) :
    y ^ (t - (i : ℝ)) ≤ (1 + y) ^ n * y ^ (t - (n : ℝ)) := by
  have he : y ^ (t - (i : ℝ)) = y ^ (t - (n : ℝ)) * y ^ (n - i) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hy]
    congr 1
    rw [Nat.cast_sub hi]
    ring
  rw [he, mul_comm ((1 + y) ^ n)]
  apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hy.le _)
  exact (pow_le_pow_left₀ hy.le (by linarith : y ≤ 1 + y) (n - i)).trans
    (pow_le_pow_right₀ (by linarith : 1 ≤ 1 + y) (Nat.sub_le n i))

/-- An explicit finite coefficient for all spatial derivatives of the actual seed. -/
def seedDerivativeConstant (n : ℕ) (S : ℝ) (J : ℤ) : ℝ :=
  ∑ i ∈ Finset.range (n + 1),
    (n.choose i : ℝ) * (S + (i : ℝ)) ^ i * (2 * Real.pi * |(J : ℝ)|) ^ (n - i)

theorem seedDerivativeConstant_nonneg (n : ℕ) {S : ℝ} (hS : 0 ≤ S) (J : ℤ) :
    0 ≤ seedDerivativeConstant n S J := by
  apply Finset.sum_nonneg
  intro i hi
  positivity

/-- The actual nth real derivative has the explicit inverse-height order.
This includes n=0, arbitrary complex s, and every positive height. -/
theorem norm_iteratedFDeriv_rawSeed_le (n : ℕ) (J : ℤ) {s : ℂ} {S : ℝ}
    (hs : ‖s‖ ≤ S) (τ : UpperHalfPlane) :
    ‖iteratedFDeriv ℝ n (rawSeed J s) (τ : ℂ)‖ ≤
      seedDerivativeConstant n S J * (1 + τ.im) ^ n * τ.im ^ (s.re - (n : ℝ)) := by
  have hS : 0 ≤ S := (norm_nonneg s).trans hs
  have hf : ContDiffOn ℝ n (fun z : ℂ => (z.im : ℂ) ^ s) upperHalfPlaneSet := by
    intro z hz
    exact ((contDiffAt_realPower (n := n) s hz).comp z
      Complex.imCLM.contDiff.contDiffAt).contDiffWithinAt
  have hg : ContDiff ℝ n (fun z : ℂ =>
      Complex.exp (((2 * Real.pi * (J : ℝ) * z.re : ℝ) : ℂ) * Complex.I)) := by
    exact ((Complex.ofRealCLM.contDiff.comp
      (contDiff_const.mul Complex.reCLM.contDiff)).mul contDiff_const).cexp
  have hprod := norm_iteratedFDerivWithin_mul_le hf hg.contDiffOn
    isOpen_upperHalfPlaneSet.uniqueDiffOn τ.im_pos (n := n) le_rfl
  simp_rw [iteratedFDerivWithin_of_isOpen _ isOpen_upperHalfPlaneSet τ.im_pos] at hprod
  calc
    _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
        ‖iteratedFDeriv ℝ i (fun z : ℂ => (z.im : ℂ) ^ s) (τ : ℂ)‖ *
        ‖iteratedFDeriv ℝ (n - i) (fun z : ℂ =>
          Complex.exp (((2 * Real.pi * (J : ℝ) * z.re : ℝ) : ℂ) * Complex.I)) (τ : ℂ)‖ := hprod
    _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
        ((S + (i : ℝ)) ^ i * τ.im ^ (s.re - (i : ℝ))) *
        (2 * Real.pi * |(J : ℝ)|) ^ (n - i) := by
      apply Finset.sum_le_sum
      intro i hi
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left (norm_iteratedFDeriv_heightPower_le i hs τ)
          (Nat.cast_nonneg _)
      · exact norm_iteratedFDeriv_phase_le (n - i) J τ
      · exact norm_nonneg _
      · positivity
    _ ≤ ∑ i ∈ Finset.range (n + 1),
        ((n.choose i : ℝ) * (S + (i : ℝ)) ^ i * (2 * Real.pi * |(J : ℝ)|) ^ (n - i)) *
        ((1 + τ.im) ^ n * τ.im ^ (s.re - (n : ℝ))) := by
      apply Finset.sum_le_sum
      intro i hi
      have hp := height_power_le n i (Nat.le_of_lt_succ (Finset.mem_range.mp hi)) τ.im_pos s.re
      have hc : 0 ≤ (n.choose i : ℝ) * (S + (i : ℝ)) ^ i *
          (2 * Real.pi * |(J : ℝ)|) ^ (n - i) := by positivity
      convert mul_le_mul_of_nonneg_left hp hc using 1
      ring
    _ = _ := by
      rw [← Finset.sum_mul]
      unfold seedDerivativeConstant
      ring

/-- A fixed upper height makes the coefficient independent of the point while
retaining the exact inverse-height order required for composition. -/
theorem norm_iteratedFDeriv_rawSeed_le_of_height_le (n : ℕ) (J : ℤ) {s : ℂ} {S M : ℝ}
    (hs : ‖s‖ ≤ S) (τ : UpperHalfPlane) (hM : τ.im ≤ M) :
    ‖iteratedFDeriv ℝ n (rawSeed J s) (τ : ℂ)‖ ≤
      (seedDerivativeConstant n S J * (1 + M) ^ n) * τ.im ^ (s.re - (n : ℝ)) := by
  apply (norm_iteratedFDeriv_rawSeed_le n J hs τ).trans
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg τ.im_pos.le _)
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (by positivity : 0 ≤ 1 + τ.im) (by linarith : 1 + τ.im ≤ 1 + M) n)
    (seedDerivativeConstant_nonneg n ((norm_nonneg s).trans hs) J)

end GapFamily.Analytic.PoincareSeedHigher
