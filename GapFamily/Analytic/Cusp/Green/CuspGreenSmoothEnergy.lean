import GapFamily.Analytic.Cusp.Green.CuspGreenSmoothFormula
import GapFamily.Analytic.Cusp.Green.CuspGreenSolutionDecay
import GapFamily.Analytic.Cusp.Profile.CuspLogCoordinateEnergyCore
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Finite energy of the actual smooth-source Green response

The finite-integral formula is an outgoing exponential above the source support.
Its actual derivative has the same decay, proving finite mass and shifted
logarithmic derivative energy when the spectral parameter has positive real part.
-/

noncomputable section

namespace GapFamily.Analytic

open Set Filter MeasureTheory
open scoped ContDiff Topology

/-- The actual source vanishes on and above a strict support cutoff. -/
theorem cuspGreenSmoothSource_zero_above {T : ℝ} {f : ℝ → ℂ}
    (hs : tsupport f ⊆ Ioo 0 T) {u : ℝ} (hu : T ≤ u) : f u = 0 := by
  by_contra h
  have hmem : u ∈ tsupport f := subset_closure h
  have := (hs hmem).2
  linarith

/-- The exact outgoing coefficient of the actual smooth-source formula. -/
def cuspGreenSmoothOutgoing (T : ℝ) (κ : ℂ) (f : ℝ → ℂ) : ℂ :=
  ((∫ u in (0 : ℝ)..T, Complex.exp (κ * (u : ℂ)) * f u) -
    (∫ u in (0 : ℝ)..T, Complex.exp (-κ * (u : ℂ)) * f u)) / (2 * κ)

theorem cuspGreenSolutionFormula_outgoing_of_support {T t : ℝ} (ht : T ≤ t)
    (κ : ℂ) {f : ℝ → ℂ} (hf : Continuous f) (hs : tsupport f ⊆ Ioo 0 T) :
    cuspGreenSolutionFormula 0 T κ f t =
      Complex.exp (-κ * (t : ℂ)) * cuspGreenSmoothOutgoing T κ f := by
  have hp : Continuous (fun u : ℝ => Complex.exp (κ * (u : ℂ)) * f u) := by fun_prop
  have hm : Continuous (fun u : ℝ => Complex.exp (-κ * (u : ℂ)) * f u) := by fun_prop
  have hint (k : ℂ) : (∫ u in T..t, Complex.exp (k * (u : ℂ)) * f u) = 0 := by
    apply intervalIntegral.integral_zero_ae
    filter_upwards with u hu
    rw [uIoc_of_le ht] at hu
    rw [cuspGreenSmoothSource_zero_above hs hu.1.le, mul_zero]
  have hpfix : (∫ u in (0 : ℝ)..t, Complex.exp (κ * (u : ℂ)) * f u) =
      ∫ u in (0 : ℝ)..T, Complex.exp (κ * (u : ℂ)) * f u := by
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (hp.intervalIntegrable 0 T) (hp.intervalIntegrable T t), hint, add_zero]
  have hmzero : (∫ u in t..T, Complex.exp (-κ * (u : ℂ)) * f u) = 0 := by
    rw [intervalIntegral.integral_symm, hint, neg_zero]
  simp only [cuspGreenSolutionFormula, hpfix, hmzero, mul_zero, add_zero,
    Complex.ofReal_zero, mul_zero, sub_zero, cuspGreenSmoothOutgoing]
  ring

private theorem integrableOn_norm_sq_of_outgoing {g : ℝ → ℂ} (hg : Continuous g)
    {T : ℝ} (hT : 0 ≤ T) {κ A : ℂ} (hκ : 0 < κ.re)
    (htail : ∀ t, T < t → g t = Complex.exp (-κ * (t : ℂ)) * A) :
    IntegrableOn (fun t => ‖g t‖ ^ 2) (Ioi 0) := by
  have hi : IntegrableOn (fun t : ℝ => Real.exp ((-2 * κ.re) * t) * ‖A‖ ^ 2) (Ioi T) :=
    (integrableOn_exp_mul_Ioi (by linarith : -2 * κ.re < 0) T).mul_const _
  have hitail : IntegrableOn (fun t => ‖g t‖ ^ 2) (Ioi T) := by
    apply hi.congr_fun _ measurableSet_Ioi
    intro t ht
    dsimp only
    rw [htail t ht, norm_mul, mul_pow, Complex.norm_exp]
    simp only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, sub_zero]
    rw [← Real.exp_nat_mul]
    congr 2
    ring
  have hicompact : IntegrableOn (fun t => ‖g t‖ ^ 2) (Ioc 0 T) :=
    ((hg.norm.pow 2).integrableOn_Icc).mono_set Ioc_subset_Icc_self
  simpa only [Ioc_union_Ioi_eq_Ioi hT] using hicompact.union hitail

theorem cuspGreenSolutionFormula_deriv_outgoing_of_support {T t : ℝ} (ht : T < t)
    {κ : ℂ} {f : ℝ → ℂ} (hf : Continuous f)
    (hs : tsupport f ⊆ Ioo 0 T) :
    deriv (cuspGreenSolutionFormula 0 T κ f) t =
      Complex.exp (-κ * (t : ℂ)) * (-κ * cuspGreenSmoothOutgoing T κ f) := by
  have heq : cuspGreenSolutionFormula 0 T κ f =ᶠ[𝓝 t]
      (fun u : ℝ => Complex.exp (-κ * (u : ℂ)) * cuspGreenSmoothOutgoing T κ f) := by
    filter_upwards [Ioi_mem_nhds ht] with u hu
    exact cuspGreenSolutionFormula_outgoing_of_support hu.le κ hf hs
  have h : HasDerivAt (fun z : ℂ => Complex.exp (-κ * z))
      (Complex.exp (-κ * (t : ℂ)) * (-κ * 1)) (t : ℂ) :=
    (Complex.hasDerivAt_exp _).comp _ ((hasDerivAt_id _).const_mul (-κ))
  have hd := (h.comp_ofReal.mul_const (cuspGreenSmoothOutgoing T κ f)).congr_of_eventuallyEq heq
  rw [hd.deriv]
  ring

theorem cuspGreenSolutionFormula_mass_integrable {T : ℝ} (hT : 0 ≤ T)
    {κ : ℂ} (hκ : 0 < κ.re) {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f)
    (hs : tsupport f ⊆ Ioo 0 T) :
    IntegrableOn (fun t => ‖cuspGreenSolutionFormula 0 T κ f t‖ ^ 2) (Ioi 0) := by
  have hk : κ ≠ 0 := by intro h; simp [h] at hκ
  exact integrableOn_norm_sq_of_outgoing (contDiff_cuspGreenSolutionFormula 0 T hk hf).continuous
    hT hκ (fun t ht => cuspGreenSolutionFormula_outgoing_of_support ht.le κ hf.continuous hs)

theorem cuspGreenSolutionFormula_deriv_mass_integrable {T : ℝ} (hT : 0 ≤ T)
    {κ : ℂ} (hκ : 0 < κ.re) {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f)
    (hs : tsupport f ⊆ Ioo 0 T) :
    IntegrableOn (fun t => ‖deriv (cuspGreenSolutionFormula 0 T κ f) t‖ ^ 2) (Ioi 0) := by
  have hk : κ ≠ 0 := by intro h; simp [h] at hκ
  have hv : ContDiff ℝ 1 (cuspGreenSolutionFormula 0 T κ f) :=
    (contDiff_cuspGreenSolutionFormula 0 T hk hf).of_le (by simp)
  exact integrableOn_norm_sq_of_outgoing hv.continuous_deriv_one hT hκ
    (fun t ht => cuspGreenSolutionFormula_deriv_outgoing_of_support ht hf.continuous hs)

theorem cuspGreenSolutionFormula_shifted_energy_integrable {T : ℝ} (hT : 0 ≤ T)
    {κ : ℂ} (hκ : 0 < κ.re) {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f)
    (hs : tsupport f ⊆ Ioo 0 T) :
    IntegrableOn (fun t => ‖deriv (cuspGreenSolutionFormula 0 T κ f) t +
      (1 / 2 : ℝ) • cuspGreenSolutionFormula 0 T κ f t‖ ^ 2) (Ioi 0) := by
  have hk : κ ≠ 0 := by intro h; simp [h] at hκ
  exact cusp_log_core_shifted_energy_integrableOn_of_integrable
    ((contDiff_cuspGreenSolutionFormula 0 T hk hf).of_le (by simp))
    (cuspGreenSolutionFormula_mass_integrable hT hκ hf hs)
    (cuspGreenSolutionFormula_deriv_mass_integrable hT hκ hf hs)

end GapFamily.Analytic
