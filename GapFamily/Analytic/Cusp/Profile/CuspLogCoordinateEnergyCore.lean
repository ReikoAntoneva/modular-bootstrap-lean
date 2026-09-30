import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Exact energy identity on the logarithmic cusp half-line

For a continuously differentiable compactly supported complex function vanishing
at the finite endpoint, the real cross term integrates to zero by the fundamental
theorem of calculus applied to half its squared norm.
-/

noncomputable section

namespace GapFamily.Analytic

open MeasureTheory Set Filter
open scoped Topology InnerProductSpace

theorem cusp_log_core_mass_integrable {v : ℝ → ℂ}
    (hv : ContDiff ℝ 1 v) (hc : HasCompactSupport v) :
    Integrable (fun t => ‖v t‖ ^ 2) := by
  apply (hv.continuous.norm.pow 2).integrable_of_hasCompactSupport
  convert! hc.comp_left (g := fun z : ℂ => ‖z‖ ^ 2) (by simp) using 1

theorem cusp_log_core_derivative_integrable {v : ℝ → ℂ}
    (hv : ContDiff ℝ 1 v) (hc : HasCompactSupport v) :
    Integrable (fun t => ‖deriv v t‖ ^ 2) := by
  apply ((hv.continuous_deriv le_rfl).norm.pow 2).integrable_of_hasCompactSupport
  convert! hc.deriv.comp_left (g := fun z : ℂ => ‖z‖ ^ 2) (by simp) using 1

theorem cusp_log_core_shifted_energy_integrable {v : ℝ → ℂ}
    (hv : ContDiff ℝ 1 v) (hc : HasCompactSupport v) :
    Integrable (fun t => ‖deriv v t + (1 / 2 : ℝ) • v t‖ ^ 2) := by
  have hcont : Continuous (fun t => deriv v t + (1 / 2 : ℝ) • v t) := by
    convert! (hv.continuous_deriv le_rfl).add
      (hv.continuous.const_smul (1 / 2 : ℝ)) using 1
  have hcomp : HasCompactSupport (fun t => deriv v t + (1 / 2 : ℝ) • v t) := by
    convert! hc.deriv.add
      (hc.comp_left (g := fun z : ℂ => (1 / 2 : ℝ) • z) (by simp)) using 1
  apply (hcont.norm.pow 2).integrable_of_hasCompactSupport
  convert! hcomp.comp_left (g := fun z : ℂ => ‖z‖ ^ 2) (by simp) using 1

theorem cusp_log_core_half_norm_sq_hasDerivAt {v : ℝ → ℂ}
    (hv : ContDiff ℝ 1 v) (t : ℝ) :
    HasDerivAt (fun x => ‖v x‖ ^ 2 / 2) (inner ℝ (v t) (deriv v t)) t := by
  simpa only [mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0)] using
    (((hv.differentiable one_ne_zero t).hasDerivAt).norm_sq.div_const 2)

theorem cusp_log_core_cross_integrable {v : ℝ → ℂ}
    (hv : ContDiff ℝ 1 v) (hc : HasCompactSupport v) :
    Integrable (fun t => inner ℝ (v t) (deriv v t)) := by
  have hnorm : ContDiff ℝ 1 (fun t => ‖v t‖ ^ 2 / 2) := (hv.norm_sq ℂ).div_const 2
  have hcomp : HasCompactSupport (fun t => ‖v t‖ ^ 2 / 2) := by
    simpa only [Function.comp_def] using
      hc.comp_left (g := fun z : ℂ => ‖z‖ ^ 2 / 2) (by simp)
  have heq : (fun t => inner ℝ (v t) (deriv v t)) = deriv (fun t => ‖v t‖ ^ 2 / 2) :=
    funext fun t => (cusp_log_core_half_norm_sq_hasDerivAt hv t).deriv.symm
  rw [heq]
  exact (hnorm.continuous_deriv le_rfl).integrable_of_hasCompactSupport hcomp.deriv

/-- The cross term vanishes by genuine FTC at zero and at infinity. -/
theorem cusp_log_core_cross_integral_zero {v : ℝ → ℂ}
    (hv : ContDiff ℝ 1 v) (hc : HasCompactSupport v) (hzero : v 0 = 0) :
    (∫ t in Ioi (0 : ℝ), inner ℝ (v t) (deriv v t)) = 0 := by
  have hnorm : ContDiff ℝ 1 (fun t => ‖v t‖ ^ 2 / 2) := (hv.norm_sq ℂ).div_const 2
  have hcomp : HasCompactSupport (fun t => ‖v t‖ ^ 2 / 2) := by
    simpa only [Function.comp_def] using
      hc.comp_left (g := fun z : ℂ => ‖z‖ ^ 2 / 2) (by simp)
  have hFTC := HasCompactSupport.integral_Ioi_deriv_eq hnorm hcomp 0
  have heq : deriv (fun t => ‖v t‖ ^ 2 / 2) = (fun t => inner ℝ (v t) (deriv v t)) :=
    funext fun t => (cusp_log_core_half_norm_sq_hasDerivAt hv t).deriv
  simpa only [heq, hzero, norm_zero, zero_pow (by norm_num : 2 ≠ 0), zero_div, neg_zero]
    using hFTC

theorem cusp_log_core_energy_expansion (a b : ℂ) :
    ‖a + (1 / 2 : ℝ) • b‖ ^ 2 = ‖a‖ ^ 2 + ‖b‖ ^ 2 / 4 + inner ℝ b a := by
  rw [norm_add_sq_real, real_inner_smul_right, norm_smul, real_inner_comm a b]
  norm_num
  ring

/-- The exact shifted derivative energy identity, with ordinary convergent integrals. -/
theorem cusp_log_core_energy_identity {v : ℝ → ℂ}
    (hv : ContDiff ℝ 1 v) (hc : HasCompactSupport v) (hzero : v 0 = 0) :
    (∫ t in Ioi (0 : ℝ), ‖deriv v t + (1 / 2 : ℝ) • v t‖ ^ 2) =
      ∫ t in Ioi (0 : ℝ), (‖deriv v t‖ ^ 2 + ‖v t‖ ^ 2 / 4) := by
  simp_rw [cusp_log_core_energy_expansion]
  have hadd := integral_add (μ := volume.restrict (Ioi (0 : ℝ)))
    ((cusp_log_core_derivative_integrable hv hc).integrableOn.add
      ((cusp_log_core_mass_integrable hv hc).integrableOn.div_const 4))
    (cusp_log_core_cross_integrable hv hc).integrableOn
  simp only [Pi.add_apply] at hadd
  rw [hadd, cusp_log_core_cross_integral_zero hv hc hzero, add_zero]

/-- Square integrability of the function and its derivative controls the cross term
without a compact-support assumption. -/
theorem cusp_log_core_cross_integrableOn_of_integrable {v : ℝ → ℂ}
    (hv : ContDiff ℝ 1 v)
    (hm : IntegrableOn (fun t => ‖v t‖ ^ 2) (Ioi 0))
    (hd : IntegrableOn (fun t => ‖deriv v t‖ ^ 2) (Ioi 0)) :
    IntegrableOn (fun t => inner ℝ (v t) (deriv v t)) (Ioi 0) := by
  apply (hm.add hd).mono'
    ((hv.continuous.inner hv.continuous_deriv_one).aestronglyMeasurable)
  filter_upwards with t
  exact (norm_inner_le_norm (v t) (deriv v t)).trans (by
    dsimp only [Pi.add_apply]
    nlinarith [sq_nonneg (‖v t‖ - ‖deriv v t‖), sq_nonneg ‖v t‖,
      sq_nonneg ‖deriv v t‖])

theorem cusp_log_core_shifted_energy_integrableOn_of_integrable {v : ℝ → ℂ}
    (hv : ContDiff ℝ 1 v)
    (hm : IntegrableOn (fun t => ‖v t‖ ^ 2) (Ioi 0))
    (hd : IntegrableOn (fun t => ‖deriv v t‖ ^ 2) (Ioi 0)) :
    IntegrableOn (fun t => ‖deriv v t + (1 / 2 : ℝ) • v t‖ ^ 2) (Ioi 0) := by
  apply ((hd.add (hm.div_const 4)).add
    (cusp_log_core_cross_integrableOn_of_integrable hv hm hd)).congr
  filter_upwards with t
  exact (cusp_log_core_energy_expansion (deriv v t) (v t)).symm

/-- Noncompact profiles satisfy the same FTC cancellation when their squared norm
actually tends to zero at infinity and they vanish at the finite endpoint. -/
theorem cusp_log_core_cross_integral_zero_of_tendsto {v : ℝ → ℂ}
    (hv : ContDiff ℝ 1 v)
    (hm : IntegrableOn (fun t => ‖v t‖ ^ 2) (Ioi 0))
    (hd : IntegrableOn (fun t => ‖deriv v t‖ ^ 2) (Ioi 0))
    (hzero : v 0 = 0) (htop : Tendsto (fun t => ‖v t‖ ^ 2) atTop (𝓝 0)) :
    (∫ t in Ioi (0 : ℝ), inner ℝ (v t) (deriv v t)) = 0 := by
  have hcont : Continuous (fun t => ‖v t‖ ^ 2 / 2) :=
    (hv.continuous.norm.pow 2).div_const 2
  have hFTC := integral_Ioi_of_hasDerivAt_of_tendsto
    (a := (0 : ℝ)) (m := (0 : ℝ))
    hcont.continuousAt.continuousWithinAt
    (fun t _ => cusp_log_core_half_norm_sq_hasDerivAt hv t)
    (cusp_log_core_cross_integrableOn_of_integrable hv hm hd)
    (by simpa only [zero_div] using htop.div_const 2)
  simpa only [hzero, norm_zero, zero_pow (by norm_num : 2 ≠ 0), zero_div, sub_self] using hFTC

/-- Exact energy identity for a noncompact, square-integrable profile with the
proved vanishing boundary values required by FTC. -/
theorem cusp_log_core_energy_identity_of_integrable {v : ℝ → ℂ}
    (hv : ContDiff ℝ 1 v)
    (hm : IntegrableOn (fun t => ‖v t‖ ^ 2) (Ioi 0))
    (hd : IntegrableOn (fun t => ‖deriv v t‖ ^ 2) (Ioi 0))
    (hzero : v 0 = 0) (htop : Tendsto (fun t => ‖v t‖ ^ 2) atTop (𝓝 0)) :
    (∫ t in Ioi (0 : ℝ), ‖deriv v t + (1 / 2 : ℝ) • v t‖ ^ 2) =
      ∫ t in Ioi (0 : ℝ), (‖deriv v t‖ ^ 2 + ‖v t‖ ^ 2 / 4) := by
  simp_rw [cusp_log_core_energy_expansion]
  have hadd := integral_add (hd.add (hm.div_const 4))
    (cusp_log_core_cross_integrableOn_of_integrable hv hm hd)
  simp only [Pi.add_apply] at hadd
  rw [hadd, cusp_log_core_cross_integral_zero_of_tendsto hv hm hd hzero htop, add_zero]

end GapFamily.Analytic
