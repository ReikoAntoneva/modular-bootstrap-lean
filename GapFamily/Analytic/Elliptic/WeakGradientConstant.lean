import GapFamily.Analytic.Elliptic.WeakGradientConstantLocal
import GapFamily.Analytic.Elliptic.WeakGradientConstantApprox
import GapFamily.Analytic.Elliptic.WeakGradientConstantGlue

/-!
# Zero weak gradient on a connected planar domain

Local compact localization, smooth convolution, almost-everywhere convergence,
and connectedness prove constancy of the original locally integrable function.
The final endpoint requires only the two real coordinate derivative tests.
-/

noncomputable section

namespace GapFamily.Analytic

open Set MeasureTheory Metric
open scoped ContDiff

/-- A locally integrable function whose derivative-test integrals vanish in
every real direction is almost everywhere constant on a connected open domain. -/
theorem exists_ae_eq_const_of_integral_fderiv_smul_eq_zero
    {U : Set ℂ} (hU : IsOpen U) (hconn : IsConnected U) {f : ℂ → ℂ}
    (hf : LocallyIntegrableOn f U volume)
    (hzero : ∀ ψ : ℂ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ U → ∀ v : ℂ, ∫ t in U, (fderiv ℝ ψ t v) • f t = 0) :
    ∃ c : ℂ, f =ᵐ[volume.restrict U] fun _ => c := by
  apply exists_ae_eq_const_of_locally_ae_eq_const_ball hconn
  intro x hx
  obtain ⟨R, hR, hRU⟩ := Metric.isOpen_iff.mp hU x hx
  let r := R / 4
  have hr : 0 < r := by dsimp [r]; positivity
  have hKU : closedBall x (3 * r) ⊆ U := by
    intro t ht
    apply hRU
    have ht' : dist t x ≤ 3 * r := ht
    change dist t x < R
    dsimp [r] at ht'
    linarith
  have hball : ball x r ⊆ closedBall x (3 * r) := by
    intro t ht
    have ht' : dist t x < r := ht
    change dist t x ≤ 3 * r
    linarith
  have hg := localized_weakGradientZero hU hf hzero x hr hKU
  obtain ⟨c, hc⟩ := exists_ae_eq_const_on_ball_of_normed_convolution_const hg.1 hr
    (normed_convolution_const_on_ball_of_test_zero hg.1 x hr hg.2)
  refine ⟨r, hr, hball.trans hKU, c, ?_⟩
  filter_upwards [hc, ae_restrict_mem measurableSet_ball] with t ht hmem
  simpa only [indicator_of_mem (hball hmem)] using ht

/-- It suffices to annihilate the two coordinate derivative tests. The
complex-valued products are integrable by local integrability and compact
test support; the theorem assumes no regular representative. -/
theorem exists_ae_eq_const_of_integral_basis_fderiv_mul_eq_zero
    {U : Set ℂ} (hU : IsOpen U) (hconn : IsConnected U) {f : ℂ → ℂ}
    (hf : LocallyIntegrableOn f U volume)
    (hx : ∀ ψ : ℂ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ U → ∫ t in U, (fderiv ℝ ψ t 1 : ℂ) * f t = 0)
    (hy : ∀ ψ : ℂ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ U → ∫ t in U, (fderiv ℝ ψ t Complex.I : ℂ) * f t = 0) :
    ∃ c : ℂ, f =ᵐ[volume.restrict U] fun _ => c := by
  apply exists_ae_eq_const_of_integral_fderiv_smul_eq_zero hU hconn hf
  intro ψ hψ hc hs v
  have hx' : (∫ t in U, fderiv ℝ ψ t 1 • f t) = 0 := by
    simpa only [Complex.real_smul] using hx ψ hψ hc hs
  have hy' : (∫ t in U, fderiv ℝ ψ t Complex.I • f t) = 0 := by
    simpa only [Complex.real_smul] using hy ψ hψ hc hs
  have hv : v = v.re • (1 : ℂ) + v.im • Complex.I := by
    simpa only [Complex.real_smul, mul_one] using (Complex.re_add_im v).symm
  have heq : (fun t => fderiv ℝ ψ t v • f t) =
      fun t => v.re • (fderiv ℝ ψ t 1 • f t) +
        v.im • (fderiv ℝ ψ t Complex.I • f t) := by
    funext t
    conv_lhs => rw [hv, map_add, map_smul, map_smul, add_smul, smul_assoc, smul_assoc]
  have hix : IntegrableOn (fun t => v.re • (fderiv ℝ ψ t 1 • f t)) U := by
    simpa only [Pi.smul_apply] using!
      (integrableOn_fderiv_smul_of_locallyIntegrableOn hU hf ψ hψ hc hs 1).smul v.re
  have hiy : IntegrableOn (fun t => v.im • (fderiv ℝ ψ t Complex.I • f t)) U := by
    simpa only [Pi.smul_apply] using!
      (integrableOn_fderiv_smul_of_locallyIntegrableOn hU hf ψ hψ hc hs Complex.I).smul v.im
  rw [heq, integral_add hix hiy, integral_smul, integral_smul, hx', hy']
  simp

end GapFamily.Analytic
