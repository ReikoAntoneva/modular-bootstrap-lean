import GapFamily.Analytic.Cusp.CuspHeightFundamentalDomain
import Mathlib.Topology.ContinuousMap.Bounded.Normed

noncomputable section
namespace GapFamily.Analytic

open Complex Matrix Matrix.SpecialLinearGroup Set
open scoped MatrixGroups UpperHalfPlane BoundedContinuousFunction

/-- A globally bounded positive cusp-height profile, unchanged on the closed domain. -/
def cuspTailClippedHeight (q : {q : CuspCoset // q ≠ identityCuspCoset})
    (τ : UpperHalfPlane) : ℝ := min (q.val.out • τ).im 2

theorem continuous_cuspTailClippedHeight
    (q : {q : CuspCoset // q ≠ identityCuspCoset}) :
    Continuous (cuspTailClippedHeight q) :=
  (UpperHalfPlane.continuous_im.comp
    (continuous_const_smul (toGL (SpecialLinearGroup.map (Int.castRingHom ℝ) q.val.out)))).min
      continuous_const

theorem cuspTailClippedHeight_pos (q : {q : CuspCoset // q ≠ identityCuspCoset})
    (τ : UpperHalfPlane) : 0 < cuspTailClippedHeight q τ :=
  lt_min (q.val.out • τ).im_pos (by norm_num)

theorem cuspTailClippedHeight_le_two (q : {q : CuspCoset // q ≠ identityCuspCoset})
    (τ : UpperHalfPlane) : cuspTailClippedHeight q τ ≤ 2 := min_le_right _ _

theorem cuspTailClippedHeight_eq_on_fd
    (q : {q : CuspCoset // q ≠ identityCuspCoset}) {τ : UpperHalfPlane}
    (hτ : τ ∈ ModularGroup.fd) : cuspTailClippedHeight q τ = (q.val.out • τ).im := by
  apply min_eq_left
  apply (nonidentity_cusp_height_le q.val q.property hτ).trans
  have hn := one_le_norm_int_pair _ (cuspBottomRow_ne_zero q.val)
  exact (div_le_iff₀ (lt_of_lt_of_le zero_lt_one hn)).mpr (by nlinarith)

/-- The bounded phase and input-height weight of a nonidentity zero-energy seed. -/
def cuspTailAmplitude (J : ℤ) (α : ℝ)
    (q : {q : CuspCoset // q ≠ identityCuspCoset}) (τ : UpperHalfPlane) : ℂ :=
  (((τ.im * (q.val.out • τ).im) ^ α : ℝ) : ℂ) *
    Complex.exp (((2 * Real.pi * (J : ℝ) * (q.val.out • τ).re : ℝ) : ℂ) * I)

theorem continuous_cuspTailAmplitude (J : ℤ) (α : ℝ) (hα : 0 ≤ α)
    (q : {q : CuspCoset // q ≠ identityCuspCoset}) :
    Continuous (cuspTailAmplitude J α q) := by
  have hc : Continuous (fun τ : UpperHalfPlane => q.val.out • τ) :=
    continuous_const_smul (toGL (SpecialLinearGroup.map (Int.castRingHom ℝ) q.val.out))
  have him := UpperHalfPlane.continuous_im.comp hc
  have hre := UpperHalfPlane.continuous_re.comp hc
  exact (Complex.continuous_ofReal.comp
    ((Real.continuous_rpow_const hα).comp (UpperHalfPlane.continuous_im.mul him))).mul
      (Complex.continuous_exp.comp
        ((Complex.continuous_ofReal.comp (continuous_const.mul hre)).mul continuous_const))

theorem norm_cuspTailAmplitude (J : ℤ) (α : ℝ)
    (q : {q : CuspCoset // q ≠ identityCuspCoset}) (τ : UpperHalfPlane) :
    ‖cuspTailAmplitude J α q τ‖ = (τ.im * (q.val.out • τ).im) ^ α := by
  simp [cuspTailAmplitude, Complex.norm_exp]
  positivity

theorem norm_cuspTailAmplitude_le_one (J : ℤ) (α : ℝ) (hα : 0 ≤ α)
    (q : {q : CuspCoset // q ≠ identityCuspCoset}) (τ : UpperHalfPlane) :
    ‖cuspTailAmplitude J α q τ‖ ≤ 1 := by
  rw [norm_cuspTailAmplitude]
  have hh : τ.im * (q.val.out • τ).im ≤ 1 := by
    simpa only [mul_comm] using nonidentity_cusp_height_mul_im_le_one q.val q.property τ
  simpa only [Real.one_rpow] using Real.rpow_le_rpow
    (mul_nonneg τ.im_pos.le (q.val.out • τ).im_pos.le) hh hα

def cuspTailAmplitudeBCF (J : ℤ) (α : ℝ) (hα : 0 ≤ α)
    (q : {q : CuspCoset // q ≠ identityCuspCoset}) : UpperHalfPlane →ᵇ ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (cuspTailAmplitude J α q)
    (continuous_cuspTailAmplitude J α hα q) 1 (norm_cuspTailAmplitude_le_one J α hα q)

@[simp] theorem cuspTailAmplitudeBCF_apply (J : ℤ) (α : ℝ) (hα : 0 ≤ α)
    (q : {q : CuspCoset // q ≠ identityCuspCoset}) (τ : UpperHalfPlane) :
    cuspTailAmplitudeBCF J α hα q τ = cuspTailAmplitude J α q τ := rfl

theorem norm_cuspTailAmplitudeBCF_le_one (J : ℤ) (α : ℝ) (hα : 0 ≤ α)
    (q : {q : CuspCoset // q ≠ identityCuspCoset}) :
    ‖cuspTailAmplitudeBCF J α hα q‖ ≤ 1 :=
  (BoundedContinuousFunction.norm_le (by norm_num : (0 : ℝ) ≤ 1)).mpr
    (norm_cuspTailAmplitude_le_one J α hα q)

/-- Exact factorization of a weighted actual cusp term through the clipped profile. -/
theorem weighted_complexPoincareTerm_eq_cuspTailProfile
    (J : ℤ) (α : ℝ) (s : ℂ) (q : {q : CuspCoset // q ≠ identityCuspCoset})
    {τ : UpperHalfPlane} (hτ : τ ∈ ModularGroup.fd) :
    ((τ.im ^ α : ℝ) : ℂ) * complexPoincareTerm 0 J s τ q =
      cuspTailAmplitude J α q τ *
        (cuspTailClippedHeight q τ : ℂ) ^ (s - (α : ℂ)) := by
  rw [cuspTailClippedHeight_eq_on_fd q hτ, complexPoincareTerm_out]
  simp only [complexPointSeed, cuspTailAmplitude, mul_zero, zero_mul, zero_add]
  have hp : ((τ.im ^ α : ℝ) : ℂ) * ((q.val.out • τ).im : ℂ) ^ s =
      (((τ.im * (q.val.out • τ).im) ^ α : ℝ) : ℂ) *
        ((q.val.out • τ).im : ℂ) ^ (s - (α : ℂ)) := by
    rw [Real.mul_rpow τ.im_pos.le (q.val.out • τ).im_pos.le, Complex.ofReal_mul,
      Complex.ofReal_cpow (q.val.out • τ).im_pos.le, mul_assoc,
      ← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr (q.val.out • τ).im_pos.ne')]
    congr 2
    ring
  calc
    _ = (((τ.im ^ α : ℝ) : ℂ) * ((q.val.out • τ).im : ℂ) ^ s) *
        Complex.exp (((2 * Real.pi * (J : ℝ) * (q.val.out • τ).re : ℝ) : ℂ) * I) := by
      ring
    _ = _ := by rw [hp]; ring

theorem weighted_complexPoincareTerm_eq_cuspTailAmplitudeBCF
    (J : ℤ) (α : ℝ) (hα : 0 ≤ α) (s : ℂ)
    (q : {q : CuspCoset // q ≠ identityCuspCoset})
    {τ : UpperHalfPlane} (hτ : τ ∈ ModularGroup.fd) :
    ((τ.im ^ α : ℝ) : ℂ) * complexPoincareTerm 0 J s τ q =
      cuspTailAmplitudeBCF J α hα q τ *
        (cuspTailClippedHeight q τ : ℂ) ^ (s - (α : ℂ)) :=
  weighted_complexPoincareTerm_eq_cuspTailProfile J α s q hτ

end GapFamily.Analytic
