import GapFamily.Analytic.Cusp.Profile.CuspProfileApproximation
import GapFamily.Analytic.Cusp.Profile.CuspProfileNormDifference
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
# Representative identification for actual scalar profile limits

Convergence in the actual modular L² space has an almost-everywhere convergent
subsequence. The explicit profile cutoffs then identify its limit, including
the value on and below height one.
-/

noncomputable section
namespace GapFamily.Analytic
open Set Filter MeasureTheory UpperHalfPlane ModularGradient
open scoped Topology ContDiff

theorem cuspProfile_Lp_limit_ae {f : ℕ → ModularHilbert} {u : ModularHilbert}
    {g : ℕ → UpperHalfPlane → ℂ} {v : UpperHalfPlane → ℂ}
    (hf : Tendsto f atTop (𝓝 u)) (heq : ∀ n, f n =ᵐ[modularMeasure] g n)
    (hg : ∀ τ, Tendsto (fun n => g n τ) atTop (𝓝 (v τ))) :
    u =ᵐ[modularMeasure] v := by
  obtain ⟨ns, hns, hae⟩ := (tendstoInMeasure_of_tendsto_Lp hf).exists_seq_tendsto_ae
  filter_upwards [hae, ae_all_iff.mpr heq] with τ hτ hτeq
  have hsub : Tendsto (fun n => g (ns n) τ) atTop (𝓝 (u τ)) := by
    simpa only [hτeq] using hτ
  exact tendsto_nhds_unique hsub ((hg τ).comp hns.tendsto_atTop)

theorem cuspProfileApproximation_value_tendsto (b : ℝ → ℂ) (y : ℝ) :
    Tendsto (fun n => cuspProfileApproximation b n y) atTop
      (𝓝 (if 1 < y then b y else 0)) := by
  by_cases hy : 1 < y
  · simp only [ite_eq_left hy]
    exact tendsto_const_nhds.congr' ((cuspProfileApproximation_eventually_value_deriv b hy).mono
      (fun _ h => h.1.symm))
  · simp only [ite_eq_right hy]
    exact tendsto_const_nhds.congr (fun n =>
      (cuspProfileApproximation_zero_of_le_one b n (le_of_not_gt hy)).1.symm)

theorem cuspProfileApproximation_deriv_tendsto (b : ℝ → ℂ) (y : ℝ) :
    Tendsto (fun n => deriv (cuspProfileApproximation b n) y) atTop
      (𝓝 (if 1 < y then deriv b y else 0)) := by
  by_cases hy : 1 < y
  · simp only [ite_eq_left hy]
    exact tendsto_const_nhds.congr' ((cuspProfileApproximation_eventually_value_deriv b hy).mono
      (fun _ h => h.2.symm))
  · simp only [ite_eq_right hy]
    exact tendsto_const_nhds.congr (fun n =>
      (cuspProfileApproximation_zero_of_le_one b n (le_of_not_gt hy)).2.symm)

end GapFamily.Analytic
