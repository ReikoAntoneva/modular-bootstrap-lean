import GapFamily.Analytic.Cusp.Fourier.CuspFourierProfileCore
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.ContDiff.Deriv

noncomputable section

namespace GapFamily.Analytic.CuspFourierCutoff

open Set Filter
open scoped ContDiff Topology

def cutoff (y : ℝ) : ℝ := Real.smoothTransition (y - 2)

def exponent (κ : ℂ) : ℂ := (1 / 2 : ℂ) + κ

def profile (κ : ℂ) (y : ℝ) : ℂ :=
  (y : ℂ) ^ (exponent κ + 2) * ((deriv (deriv cutoff) y : ℝ) : ℂ) +
    2 * exponent κ * (y : ℂ) ^ (exponent κ + 1) * ((deriv cutoff y : ℝ) : ℂ)

def linearProfile (y : ℝ) : ℂ :=
  2 * (y : ℂ) ^ (3 / 2 : ℂ) * ((deriv cutoff y : ℝ) : ℂ)

theorem contDiff_cutoff : ContDiff ℝ ∞ cutoff :=
  Real.smoothTransition.contDiff.comp (contDiff_id.sub contDiff_const)

theorem contDiff_deriv_cutoff : ContDiff ℝ ∞ (deriv cutoff) :=
  contDiff_cutoff.deriv'

theorem contDiff_deriv2_cutoff : ContDiff ℝ ∞ (deriv (deriv cutoff)) :=
  contDiff_deriv_cutoff.deriv'

theorem cutoff_eq_zero {y : ℝ} (hy : y ≤ 2) : cutoff y = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

theorem cutoff_eq_one {y : ℝ} (hy : 3 ≤ y) : cutoff y = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

theorem deriv_cutoff_eq_zero_of_lt {y : ℝ} (hy : y < 2) : deriv cutoff y = 0 := by
  have h : cutoff =ᶠ[𝓝 y] (fun _ => 0) := by
    filter_upwards [Iio_mem_nhds hy] with x hx using cutoff_eq_zero hx.le
  rw [h.deriv_eq]
  exact deriv_const y 0

theorem deriv_cutoff_eq_zero_of_gt {y : ℝ} (hy : 3 < y) : deriv cutoff y = 0 := by
  have h : cutoff =ᶠ[𝓝 y] (fun _ => 1) := by
    filter_upwards [Ioi_mem_nhds hy] with x hx using cutoff_eq_one hx.le
  rw [h.deriv_eq]
  exact deriv_const y 1

theorem tsupport_deriv_cutoff : tsupport (deriv cutoff) ⊆ Icc (2 : ℝ) 3 := by
  apply closure_minimal _ isClosed_Icc
  intro y hy
  by_contra hn
  simp only [mem_Icc, not_and_or, not_le] at hn
  rcases hn with hl | hr
  · exact hy (deriv_cutoff_eq_zero_of_lt hl)
  · exact hy (deriv_cutoff_eq_zero_of_gt hr)

theorem tsupport_deriv2_cutoff : tsupport (deriv (deriv cutoff)) ⊆ Icc (2 : ℝ) 3 :=
  tsupport_deriv_subset.trans tsupport_deriv_cutoff

theorem tsupport_profile (κ : ℂ) : tsupport (profile κ) ⊆ Icc (2 : ℝ) 3 := by
  apply closure_minimal _ isClosed_Icc
  intro y hy
  by_contra hn
  have hd : deriv cutoff y = 0 := image_eq_zero_of_notMem_tsupport
    (fun h => hn (tsupport_deriv_cutoff h))
  have hd2 : deriv (deriv cutoff) y = 0 := image_eq_zero_of_notMem_tsupport
    (fun h => hn (tsupport_deriv2_cutoff h))
  exact hy (by simp [profile, hd, hd2])

theorem tsupport_linearProfile : tsupport linearProfile ⊆ Icc (2 : ℝ) 3 := by
  apply closure_minimal _ isClosed_Icc
  intro y hy
  by_contra hn
  have hd : deriv cutoff y = 0 := image_eq_zero_of_notMem_tsupport
    (fun h => hn (tsupport_deriv_cutoff h))
  exact hy (by simp [linearProfile, hd])

theorem hasCompactSupport_profile (κ : ℂ) : HasCompactSupport (profile κ) :=
  isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) (tsupport_profile κ)

theorem hasCompactSupport_linearProfile : HasCompactSupport linearProfile :=
  isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) tsupport_linearProfile

theorem tsupport_profile_subset_Ioi (κ : ℂ) : tsupport (profile κ) ⊆ Ioi (1 : ℝ) := by
  intro y hy
  have h := (tsupport_profile κ hy).1
  change 1 < y
  linarith

theorem tsupport_linearProfile_subset_Ioi : tsupport linearProfile ⊆ Ioi (1 : ℝ) := by
  intro y hy
  have h := (tsupport_linearProfile hy).1
  change 1 < y
  linarith

theorem contDiffAt_ofReal_cpow (z : ℂ) {y : ℝ} (hy : 0 < y) :
    ContDiffAt ℝ ∞ (fun x : ℝ => (x : ℂ) ^ z) y := by
  have hlog : ContDiffAt ℝ ∞ (fun x : ℝ => (Real.log x : ℂ)) y :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp y (Real.contDiffAt_log.mpr hy.ne')
  have hexp : ContDiffAt ℝ ∞ (fun x : ℝ => Complex.exp ((Real.log x : ℂ) * z)) y :=
    (hlog.mul contDiffAt_const).cexp
  apply hexp.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hy] with x hx
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne'),
    Complex.ofReal_log hx.le]

theorem contDiff_profile (κ : ℂ) : ContDiff ℝ ∞ (profile κ) := by
  rw [contDiff_iff_contDiffAt]
  intro y
  by_cases hy : 0 < y
  · unfold profile
    exact ((contDiffAt_ofReal_cpow (exponent κ + 2) hy).mul
      (Complex.ofRealCLM.contDiff.contDiffAt.comp y contDiff_deriv2_cutoff.contDiffAt)).add
      ((contDiffAt_const.mul (contDiffAt_ofReal_cpow (exponent κ + 1) hy)).mul
        (Complex.ofRealCLM.contDiff.contDiffAt.comp y contDiff_deriv_cutoff.contDiffAt))
  · have hn : y ∉ tsupport (profile κ) := by
      intro h
      have h2 := (tsupport_profile κ h).1
      linarith
    exact contDiffAt_const.congr_of_eventuallyEq
      (notMem_tsupport_iff_eventuallyEq.mp hn)

theorem contDiff_linearProfile : ContDiff ℝ ∞ linearProfile := by
  rw [contDiff_iff_contDiffAt]
  intro y
  by_cases hy : 0 < y
  · unfold linearProfile
    exact (contDiffAt_const.mul (contDiffAt_ofReal_cpow (3 / 2 : ℂ) hy)).mul
      (Complex.ofRealCLM.contDiff.contDiffAt.comp y contDiff_deriv_cutoff.contDiffAt)
  · have hn : y ∉ tsupport linearProfile := by
      intro h
      have h2 := (tsupport_linearProfile h).1
      linarith
    exact contDiffAt_const.congr_of_eventuallyEq
      (notMem_tsupport_iff_eventuallyEq.mp hn)

theorem profile_factorization {y : ℝ} (hy : 0 < y) (κ : ℂ) :
    profile κ y = Complex.exp (κ * (Real.log y : ℂ)) *
      (profile 0 y + κ * linearProfile y) := by
  have hy0 : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy.ne'
  simp only [profile, linearProfile, exponent]
  rw [show (1 / 2 : ℂ) + κ + 2 = κ + (5 / 2 : ℂ) by ring,
    show (1 / 2 : ℂ) + κ + 1 = κ + (3 / 2 : ℂ) by ring,
    Complex.cpow_add _ _ hy0, Complex.cpow_add _ _ hy0,
    Complex.cpow_def_of_ne_zero hy0 κ, ← Complex.ofReal_log hy.le]
  rw [mul_comm (Real.log y : ℂ) κ]
  norm_num
  ring

theorem profile_factorization_clamped (κ : ℂ) (y : ℝ) :
    profile κ y = Complex.exp (κ * (Real.log (max 2 (min 3 y)) : ℂ)) *
      (profile 0 y + κ * linearProfile y) := by
  by_cases hy : y ∈ Icc (2 : ℝ) 3
  · have hy0 : 0 < y := lt_of_lt_of_le (by norm_num) hy.1
    simpa only [min_eq_right hy.2, max_eq_right hy.1] using profile_factorization hy0 κ
  · have hκ : profile κ y = 0 := image_eq_zero_of_notMem_tsupport
      (fun h => hy (tsupport_profile κ h))
    have h0 : profile 0 y = 0 := image_eq_zero_of_notMem_tsupport
      (fun h => hy (tsupport_profile 0 h))
    have hlinear : linearProfile y = 0 := image_eq_zero_of_notMem_tsupport
      (fun h => hy (tsupport_linearProfile h))
    simp only [hκ, h0, hlinear, mul_zero, add_zero]

end GapFamily.Analytic.CuspFourierCutoff
