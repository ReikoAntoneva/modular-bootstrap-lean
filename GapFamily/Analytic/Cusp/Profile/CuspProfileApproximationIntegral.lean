import GapFamily.Analytic.Cusp.Profile.CuspProfileApproximationBoundary
import GapFamily.Analytic.Cusp.Profile.CuspProfileApproximationEstimate

/-!+# Convergence of quantified cusp profile cutoffs

Ordinary dominated convergence converts the proved cutoff estimates into
weighted value convergence and unweighted vertical derivative convergence.
The explicit smooth cutoff family is supplied in the final construction.
-/

noncomputable section

namespace GapFamily.Analytic

open Set Filter MeasureTheory
open scoped Topology ContDiff

/-- Quantitative cutoff properties imply both actual energy-error integrals
converge to zero. Integrability of every error is part of the conclusion. -/
theorem cuspProfile_cutoff_integral_convergence {b : ℝ → ℂ} {χ : ℕ → ℝ → ℝ} {C : ℝ}
    (hb : ContDiffOn ℝ ∞ b (Ioi 0)) (hb1 : b 1 = 0)
    (hv : IntegrableOn (fun y => ‖b y‖ ^ 2 / y ^ 2) (Ioi 1))
    (hd : IntegrableOn (fun y => ‖deriv b y‖ ^ 2) (Ioi 1))
    (hχ : ∀ n, ContDiff ℝ ∞ (χ n))
    (hχ01 : ∀ n y, 0 ≤ χ n y ∧ χ n y ≤ 1)
    (hC : 0 ≤ C)
    (hχd : ∀ n y, 1 < y →
      ‖deriv (χ n) y‖ ≤ if y ≤ 2 then C / (y - 1) else C / y)
    (hχe : ∀ y, 1 < y → ∀ᶠ n in atTop, χ n y = 1 ∧ deriv (χ n) y = 0) :
    (∀ n, IntegrableOn (fun y => ‖χ n y • b y - b y‖ ^ 2 / y ^ 2) (Ioi 1) ∧
      IntegrableOn (fun y => ‖deriv (fun x => χ n x • b x) y - deriv b y‖ ^ 2) (Ioi 1)) ∧
    Tendsto (fun n => ∫ y in Ioi (1 : ℝ), ‖χ n y • b y - b y‖ ^ 2 / y ^ 2)
      atTop (𝓝 0) ∧
    Tendsto (fun n => ∫ y in Ioi (1 : ℝ),
      ‖deriv (fun x => χ n x • b x) y - deriv b y‖ ^ 2) atTop (𝓝 0) := by
  obtain ⟨L, hL, hbnd⟩ := exists_cuspProfile_boundary_bound hb hb1
  have hb' : ContDiffOn ℝ ∞ b (Ioi 1) := by
    apply hb.mono
    intro y hy
    exact lt_trans (show (0 : ℝ) < 1 by norm_num) hy
  have hprod (n : ℕ) : ContDiffOn ℝ ∞ (fun y => χ n y • b y) (Ioi 1) :=
    (hχ n).contDiffOn.smul hb'
  have hvm (n : ℕ) : AEStronglyMeasurable
      (fun y => ‖χ n y • b y - b y‖ ^ 2 / y ^ 2) (volume.restrict (Ioi 1)) := by
    apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioi
    exact (((hprod n).continuousOn.sub hb'.continuousOn).norm.pow 2).div
      (continuousOn_id.pow 2) (fun y hy => pow_ne_zero 2 (zero_lt_one.trans hy).ne')
  have hdm (n : ℕ) : AEStronglyMeasurable
      (fun y => ‖deriv (fun x => χ n x • b x) y - deriv b y‖ ^ 2)
      (volume.restrict (Ioi 1)) := by
    apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioi
    exact (((hprod n).continuousOn_deriv_of_isOpen isOpen_Ioi (by simp)).sub
      (hb'.continuousOn_deriv_of_isOpen isOpen_Ioi (by simp))).norm.pow 2
  have hvb (n : ℕ) : ∀ᵐ y ∂volume.restrict (Ioi 1),
      ‖‖χ n y • b y - b y‖ ^ 2 / y ^ 2‖ ≤ ‖b y‖ ^ 2 / y ^ 2 := by
    filter_upwards with y
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact cuspProfile_cutoff_value_error_le (hχ01 n y).1 (hχ01 n y).2 (b y)
  have hdb (n : ℕ) : ∀ᵐ y ∂volume.restrict (Ioi 1),
      ‖‖deriv (fun x => χ n x • b x) y - deriv b y‖ ^ 2‖ ≤
        cuspProfileDerivativeMajorant b C L y := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact cuspProfile_cutoff_deriv_sq_le
      ((hχ n).differentiable (by simp) y)
      ((hb'.contDiffAt (isOpen_Ioi.mem_nhds hy)).differentiableAt (by simp))
      (hχ01 n y).1 (hχ01 n y).2 hC hL hy hbnd (hχd n y hy)
  have hvlim : ∀ᵐ y ∂volume.restrict (Ioi 1),
      Tendsto (fun n => ‖χ n y • b y - b y‖ ^ 2 / y ^ 2) atTop (𝓝 (0 : ℝ)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    apply tendsto_const_nhds.congr'
    filter_upwards [hχe y hy] with n hn
    simp [hn.1]
  have hdlim : ∀ᵐ y ∂volume.restrict (Ioi 1),
      Tendsto (fun n => ‖deriv (fun x => χ n x • b x) y - deriv b y‖ ^ 2)
        atTop (𝓝 (0 : ℝ)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    apply tendsto_const_nhds.congr'
    filter_upwards [hχe y hy] with n hn
    rw [deriv_fun_smul ((hχ n).differentiable (by simp) y)
      ((hb'.contDiffAt (isOpen_Ioi.mem_nhds hy)).differentiableAt (by simp))]
    simp [hn.1, hn.2]
  have hmajor := cuspProfileDerivativeMajorant_integrable C L hv hd
  refine ⟨?_, ?_, ?_⟩
  · intro n
    exact ⟨hv.mono' (hvm n) (hvb n), hmajor.mono' (hdm n) (hdb n)⟩
  · simpa using tendsto_integral_of_dominated_convergence
      (fun y => ‖b y‖ ^ 2 / y ^ 2) hvm hv hvb hvlim
  · simpa using tendsto_integral_of_dominated_convergence
      (cuspProfileDerivativeMajorant b C L) hdm hmajor hdb hdlim

end GapFamily.Analytic
