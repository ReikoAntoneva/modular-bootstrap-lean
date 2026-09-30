import GapFamily.Analytic.Cusp.Profile.CuspProfileCore

noncomputable section

namespace GapFamily.Analytic

open Real
open scoped ContDiff

/-- The literal integer Fourier phase in the horizontal cusp coordinate. -/
def cuspFourierMode (n : ℤ) (x : ℝ) : ℂ :=
  Complex.exp ((2 * (π : ℂ) * Complex.I * (n : ℂ)) * (x : ℂ))

@[simp]
theorem cuspFourierMode_add_int (n : ℤ) (x : ℝ) (k : ℤ) :
    cuspFourierMode n (x + (k : ℝ)) = cuspFourierMode n x := by
  unfold cuspFourierMode
  rw [Complex.ofReal_add, Complex.ofReal_intCast, mul_add, Complex.exp_add]
  have hk : Complex.exp ((2 * (π : ℂ) * Complex.I * (n : ℂ)) * (k : ℂ)) = 1 := by
    convert Complex.exp_int_mul_two_pi_mul_I (n * k) using 1
    congr 1
    push_cast
    ring
  rw [hk, mul_one]

theorem contDiff_cuspFourierMode (n : ℤ) : ContDiff ℝ ∞ (cuspFourierMode n) := by
  change ContDiff ℝ ∞ (fun x : ℝ => Complex.exp
    ((2 * (π : ℂ) * Complex.I * (n : ℂ)) * Complex.ofRealCLM x))
  exact (contDiff_const.mul Complex.ofRealCLM.contDiff).cexp

theorem hasDerivAt_cuspFourierMode (n : ℤ) (x : ℝ) :
    HasDerivAt (cuspFourierMode n)
      ((2 * (π : ℂ) * Complex.I * (n : ℂ)) * cuspFourierMode n x) x := by
  change HasDerivAt (fun y : ℝ => Complex.exp
    ((2 * (π : ℂ) * Complex.I * (n : ℂ)) * (y : ℂ)))
    ((2 * (π : ℂ) * Complex.I * (n : ℂ)) * Complex.exp
      ((2 * (π : ℂ) * Complex.I * (n : ℂ)) * (x : ℂ))) x
  have hc : HasDerivAt (fun y : ℝ => (y : ℂ)) (1 : ℂ) x := by
    simpa only [Complex.ofRealCLM_apply, Complex.ofReal_one] using!
      (Complex.ofRealCLM.hasDerivAt (x := x))
  simpa only [mul_one, one_mul, mul_comm] using!
    (hc.const_mul (2 * (π : ℂ) * Complex.I * (n : ℂ))).cexp

@[simp]
theorem norm_cuspFourierMode (n : ℤ) (x : ℝ) : ‖cuspFourierMode n x‖ = 1 := by
  simp [cuspFourierMode, Complex.norm_exp, Complex.mul_re, Complex.mul_im]

theorem cuspFourierMode_ne_zero (n : ℤ) (x : ℝ) : cuspFourierMode n x ≠ 0 :=
  Complex.exp_ne_zero _

@[simp]
theorem cuspFourierMode_zero (x : ℝ) : cuspFourierMode 0 x = 1 := by
  simp [cuspFourierMode]

@[simp]
theorem cuspFourierMode_at_zero (n : ℤ) : cuspFourierMode n 0 = 1 := by
  simp [cuspFourierMode]

end GapFamily.Analytic

noncomputable section
namespace GapFamily.Analytic

open Set UpperHalfPlane ModularGroup MeasureTheory ModularGradient
open scoped MatrixGroups ContDiff

/-- The actual compact seed for a vertical profile in the integer Fourier mode. -/
def cuspFourierProfileSeed (n : ℤ) (b : ℝ → ℂ) (z : ℂ) : ℂ :=
  cuspProfileSeed b z * cuspFourierMode n z.re

theorem contDiff_cuspFourierProfileSeed (n : ℤ) {b : ℝ → ℂ}
    (hb : ContDiff ℝ ∞ b) : ContDiff ℝ ∞ (cuspFourierProfileSeed n b) :=
  (contDiff_cuspProfileSeed hb).mul ((contDiff_cuspFourierMode n).comp Complex.reCLM.contDiff)

theorem cuspFourierProfileSeed_hasCompactSupport (n : ℤ) {b : ℝ → ℂ}
    (hc : HasCompactSupport b) : HasCompactSupport (cuspFourierProfileSeed n b) :=
  (cuspProfileSeed_hasCompactSupport hc).mul_right

theorem cuspFourierProfileSeed_upper_support (n : ℤ) {b : ℝ → ℂ}
    (hc : HasCompactSupport b) (hs : tsupport b ⊆ Ioi (1 : ℝ)) :
    tsupport (cuspFourierProfileSeed n b) ⊆ upperHalfPlaneSet :=
  tsupport_mul_subset_left.trans (cuspProfileSeed_upper_support hc hs)

/-- Integer periodicity factors the same mode out of every parabolic term.
The original full-SL₂ factor one half remains in modularPeriodization. -/
theorem modularPeriodization_cuspFourierProfileSeed_of_zero_nonparabolic
    (n : ℤ) (b : ℝ → ℂ) (τ : UpperHalfPlane)
    (hτ : τ.re ∈ Icc (-1/2 : ℝ) (1/2))
    (hz : ∀ γ : SL(2, ℤ), γ 1 0 ≠ 0 → b (γ • τ).im = 0) :
    modularPeriodization (cuspFourierProfileSeed n b) τ =
      b τ.im * cuspFourierMode n τ.re := by
  have hsummand (γ : SL(2, ℤ)) :
      cuspFourierProfileSeed n b (↑(γ • τ : UpperHalfPlane) : ℂ) =
        cuspProfileSeed b (↑(γ • τ : UpperHalfPlane) : ℂ) * cuspFourierMode n τ.re := by
    by_cases hc : γ 1 0 = 0
    · obtain ⟨k, hk | hk⟩ := parabolic_eq_T_zpow_or_neg hc
      · subst γ
        simp only [cuspFourierProfileSeed, coe_re, re_T_zpow_smul,
          cuspFourierMode_add_int]
      · subst γ
        simp only [SL_neg_smul, cuspFourierProfileSeed, coe_re, re_T_zpow_smul,
          cuspFourierMode_add_int]
    · simp only [cuspFourierProfileSeed, cuspProfileSeed, coe_im, hz γ hc,
        mul_zero, zero_mul]
  rw [modularPeriodization_coe]
  simp_rw [hsummand]
  rw [tsum_mul_right, ← mul_assoc, ← modularPeriodization_coe,
    modularPeriodization_cuspProfileSeed_of_zero_nonparabolic b τ hτ hz]

/-- Literal Fourier profile on every point of the closed fundamental domain. -/
theorem modularPeriodization_cuspFourierProfileSeed_eq_on_fd
    (n : ℤ) {b : ℝ → ℂ} (hs : tsupport b ⊆ Ioi (1 : ℝ))
    {τ : UpperHalfPlane} (hτ : τ ∈ fd) :
    modularPeriodization (cuspFourierProfileSeed n b) τ =
      b τ.im * cuspFourierMode n τ.re := by
  apply modularPeriodization_cuspFourierProfileSeed_of_zero_nonparabolic n b τ
    (by simpa only [neg_div, Set.mem_Icc] using abs_le.mp hτ.2)
  intro γ hγ
  by_contra hn
  have hh : 1 < (γ • τ).im := hs (subset_tsupport b hn)
  exact (not_le_of_gt hh)
    (modular_smul_im_le_one_of_mem_fd_of_lowerLeft_ne_zero γ hτ hγ)

/-- Actual compact integer-mode cusp profile in the original modular smooth core. -/
def cuspFourierProfileCore (n : ℤ) (b : ℝ → ℂ) (hb : ContDiff ℝ ∞ b)
    (hc : HasCompactSupport b) (hs : tsupport b ⊆ Ioi (1 : ℝ)) : smoothCore :=
  ⟨modularPeriodization (cuspFourierProfileSeed n b),
    modularPeriodization_mem_smoothCore_of_upper_support
      (contDiff_cuspFourierProfileSeed n hb) (cuspFourierProfileSeed_hasCompactSupport n hc)
      (cuspFourierProfileSeed_upper_support n hc hs)⟩

theorem cuspFourierProfileCore_eq_on_fd (n : ℤ) (b : ℝ → ℂ)
    (hb : ContDiff ℝ ∞ b) (hc : HasCompactSupport b) (hs : tsupport b ⊆ Ioi (1 : ℝ))
    {τ : UpperHalfPlane} (hτ : τ ∈ fd) :
    (cuspFourierProfileCore n b hb hc hs).val τ =
      b τ.im * cuspFourierMode n τ.re :=
  modularPeriodization_cuspFourierProfileSeed_eq_on_fd n hs hτ

theorem cuspFourierProfileCore_value_ae (n : ℤ) (b : ℝ → ℂ)
    (hb : ContDiff ℝ ∞ b) (hc : HasCompactSupport b) (hs : tsupport b ⊆ Ioi (1 : ℝ)) :
    value (cuspFourierProfileCore n b hb hc hs) =ᵐ[modularMeasure]
      (fun τ : UpperHalfPlane => b τ.im * cuspFourierMode n τ.re) := by
  apply (value_ae (cuspFourierProfileCore n b hb hc hs)).trans
  filter_upwards [ae_mem_fdo] with τ hτ
  exact cuspFourierProfileCore_eq_on_fd n b hb hc hs (fdo_subset_fd hτ)

end GapFamily.Analytic

namespace GapFamily.Analytic
open Set UpperHalfPlane MeasureTheory ModularGradient
open scoped ContDiff

/-- The actual hyperbolically scaled directional derivative of the compact
integer Fourier profile, as a representative of the original core gradient. -/
theorem cuspFourierProfileCore_directional_ae (n : ℤ) (b : ℝ → ℂ)
    (hb : ContDiff ℝ ∞ b) (hc : HasCompactSupport b) (hs : tsupport b ⊆ Ioi (1 : ℝ))
    (v : ℂ) :
    directional (cuspFourierProfileCore n b hb hc hs).val v =ᵐ[modularMeasure]
      (fun τ : UpperHalfPlane => (τ.im : ℂ) *
        (b τ.im * (v.re • ((2*(Real.pi : ℂ)*Complex.I*(n : ℂ)) *
          cuspFourierMode n τ.re)) +
         cuspFourierMode n τ.re * (v.im • deriv b τ.im))) := by
  have hg : ContDiff ℝ ∞ (fun z : ℂ => b z.im * cuspFourierMode n z.re) :=
    (hb.comp Complex.imCLM.contDiff).mul
      ((contDiff_cuspFourierMode n).comp Complex.reCLM.contDiff)
  have heq : (fun τ : UpperHalfPlane => (cuspFourierProfileCore n b hb hc hs).val τ)
      =ᵐ[modularMeasure] (fun τ => b τ.im * cuspFourierMode n τ.re) := by
    filter_upwards [ae_mem_fdo] with τ hτ
    exact cuspFourierProfileCore_eq_on_fd n b hb hc hs (ModularGroup.fdo_subset_fd hτ)
  have hdir := modularDirectional_ae_eq
    ((cuspFourierProfileCore n b hb hc hs).property.1.continuousOn.mono
      (fun _ hz => im_pos_of_mem_modularInterior hz)) hg.continuous.continuousOn heq v
  apply hdir.trans
  apply Filter.Eventually.of_forall
  intro τ
  have hdb := ((hb.differentiable (by simp)) τ.im).hasFDerivAt.comp
    (τ : ℂ) Complex.imCLM.hasFDerivAt
  have hdm := (hasDerivAt_cuspFourierMode n τ.re).hasFDerivAt.comp
    (τ : ℂ) Complex.reCLM.hasFDerivAt
  have hd := hdb.mul hdm
  change (τ.im : ℂ) * fderiv ℝ ((b ∘ Complex.im) * (cuspFourierMode n ∘ Complex.re)) τ v = _
  rw [hd.fderiv]
  change (τ.im : ℂ) *
    (b τ.im * (v.re • ((2*(Real.pi : ℂ)*Complex.I*(n : ℂ)) * cuspFourierMode n τ.re)) +
     cuspFourierMode n τ.re * fderiv ℝ b τ.im v.im) = _
  rw [fderiv_eq_smul_deriv]

end GapFamily.Analytic

namespace GapFamily.Analytic
open Set UpperHalfPlane MeasureTheory ModularGradient
open scoped ContDiff

theorem cuspFourierProfileCore_xComponent_ae (n : ℤ) (b : ℝ → ℂ)
    (hb : ContDiff ℝ ∞ b) (hc : HasCompactSupport b) (hs : tsupport b ⊆ Ioi (1 : ℝ)) :
    xComponent (cuspFourierProfileCore n b hb hc hs) =ᵐ[modularMeasure]
      (fun τ : UpperHalfPlane => (τ.im : ℂ) *
        (b τ.im * ((2*(Real.pi : ℂ)*Complex.I*(n : ℂ))*cuspFourierMode n τ.re))) := by
  have h := (component_ae 1 (fun F => F.property.2.2.2.1)
    (cuspFourierProfileCore n b hb hc hs)).trans
    (cuspFourierProfileCore_directional_ae n b hb hc hs 1)
  simpa only [xComponent, Complex.one_re, Complex.one_im, one_smul, zero_smul,
    mul_zero, add_zero] using h

theorem cuspFourierProfileCore_yComponent_ae (n : ℤ) (b : ℝ → ℂ)
    (hb : ContDiff ℝ ∞ b) (hc : HasCompactSupport b) (hs : tsupport b ⊆ Ioi (1 : ℝ)) :
    yComponent (cuspFourierProfileCore n b hb hc hs) =ᵐ[modularMeasure]
      (fun τ : UpperHalfPlane => (τ.im : ℂ) *
        (cuspFourierMode n τ.re * deriv b τ.im)) := by
  have h := (component_ae Complex.I (fun F => F.property.2.2.2.2)
    (cuspFourierProfileCore n b hb hc hs)).trans
    (cuspFourierProfileCore_directional_ae n b hb hc hs Complex.I)
  simpa only [yComponent, Complex.I_re, Complex.I_im, one_smul, zero_smul,
    mul_zero, zero_add] using h

/-- The scalar mode recovers the previously constructed scalar cusp core exactly. -/
@[simp] theorem cuspFourierProfileCore_zero (b : ℝ → ℂ)
    (hb : ContDiff ℝ ∞ b) (hc : HasCompactSupport b) (hs : tsupport b ⊆ Ioi (1 : ℝ)) :
    cuspFourierProfileCore 0 b hb hc hs = cuspProfileCore b hb hc hs := by
  apply Subtype.ext
  change modularPeriodization (cuspFourierProfileSeed 0 b) = modularPeriodization (cuspProfileSeed b)
  congr 1
  funext z
  simp [cuspFourierProfileSeed, cuspFourierMode]

end GapFamily.Analytic
