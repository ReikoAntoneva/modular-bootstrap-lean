import GapFamily.Analytic.Cusp.Green.CuspGreenTailKernel
import GapFamily.Analytic.Cusp.Green.CuspGreenOperatorBasic
import GapFamily.Analytic.Cusp.Profile.CuspHalfLineLaplaceTail

/-!
# The ordinary weighted half-line Green integral

The noncompact source is an actual half-line `L²` class. A finite source cutoff
splits its ordinarily integrable weighted Green response into a finite integral
and the genuine Laplace tail. The result holds at the threshold parameter.
-/

noncomputable section
namespace GapFamily.Analytic
open Set Filter MeasureTheory CuspHalfLineLaplace CuspHalfLineLaplaceTail
open scoped Topology

/-- The finite part is ordinarily integrable for every half-line Hilbert source. -/
theorem cuspGreen_weighted_integrableOn_finite (t T α : ℝ) (κ : ℂ)
    (f : HalfLineL2) :
    IntegrableOn (fun u : ℝ => cuspGreen 0 t u κ * Complex.exp (-(α : ℂ) * u) * f u)
      (Ioc 0 T) := by
  have hf : MemLp f 2 (volume.restrict (Ioc 0 T)) :=
    (Lp.memLp f).mono_measure (Measure.restrict_mono_set volume Ioc_subset_Ioi_self)
  have hcont : Continuous (fun u : ℝ =>
      cuspGreen 0 t u κ * Complex.exp (-(α : ℂ) * u)) :=
    ((continuous_cuspGreen_position 0 κ).comp (continuous_const.prodMk continuous_id)).mul
      (by fun_prop)
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Icc (0 : ℝ) T) hcont.continuousOn
  exact (hf.integrable (by norm_num)).bdd_mul hcont.aestronglyMeasurable
    ((ae_restrict_iff' measurableSet_Ioc).mpr (Filter.Eventually.of_forall
      (fun u hu => hC u (Ioc_subset_Icc_self hu))))

/-- The entire Green tail has ordinary integrability precisely supplied by the
positive real part of the shifted Laplace parameter. -/
theorem cuspGreen_weighted_integrableOn_tail {t T α : ℝ} (hT : 0 ≤ T) (htT : t ≤ T)
    {κ : ℂ} (hβ : 0 < ((α : ℂ) + κ).re) (f : HalfLineL2) :
    IntegrableOn (fun u : ℝ => cuspGreen 0 t u κ * Complex.exp (-(α : ℂ) * u) * f u)
      (Ioi T) := by
  apply ((tailLaplace_integrable hT hβ f).const_mul (cuspGreenTailValue t κ)).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  rw [cuspGreen_mul_weight_eq_tail t u α (htT.trans hu.le) κ]
  ring

/-- Exact ordinary tail integral, with the same literal `L²` source on both sides. -/
theorem cuspGreen_weighted_tail_integral {t T α : ℝ} (hT : 0 ≤ T) (htT : t ≤ T)
    {κ : ℂ} (hβ : 0 < ((α : ℂ) + κ).re) (f : HalfLineL2) :
    (∫ u : ℝ in Ioi T,
      cuspGreen 0 t u κ * Complex.exp (-(α : ℂ) * u) * f u) =
      cuspGreenTailValue t κ * tailLaplace T ((α : ℂ) + κ) f := by
  rw [tailLaplace_apply hT hβ, ← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro u hu
  dsimp only
  rw [cuspGreen_mul_weight_eq_tail t u α (htT.trans hu.le) κ]
  ring

/-- The full noncompact weighted response is an ordinary integrable function. -/
theorem cuspGreen_weighted_integrable {t T α : ℝ} (hT : 0 ≤ T) (htT : t ≤ T)
    {κ : ℂ} (hβ : 0 < ((α : ℂ) + κ).re) (f : HalfLineL2) :
    IntegrableOn (fun u : ℝ => cuspGreen 0 t u κ * Complex.exp (-(α : ℂ) * u) * f u)
      (Ioi 0) := by
  have h := integrableOn_union.mpr
    ⟨cuspGreen_weighted_integrableOn_finite t T α κ f,
      cuspGreen_weighted_integrableOn_tail hT htT hβ f⟩
  simpa only [Ioc_union_Ioi_eq_Ioi hT] using h

/-- An exact finite-collar-plus-tail formula for every actual half-line `L²`
source, including κ=0 whenever α>0. -/
theorem cuspGreen_weighted_integral_split {t T α : ℝ} (hT : 0 ≤ T) (htT : t ≤ T)
    {κ : ℂ} (hβ : 0 < ((α : ℂ) + κ).re) (f : HalfLineL2) :
    (∫ u : ℝ in Ioi 0,
      cuspGreen 0 t u κ * Complex.exp (-(α : ℂ) * u) * f u) =
      (∫ u : ℝ in Ioc 0 T,
        cuspGreen 0 t u κ * Complex.exp (-(α : ℂ) * u) * f u) +
      cuspGreenTailValue t κ * tailLaplace T ((α : ℂ) + κ) f := by
  calc
    _ = (∫ u : ℝ in Ioc 0 T,
        cuspGreen 0 t u κ * Complex.exp (-(α : ℂ) * u) * f u) +
        ∫ u : ℝ in Ioi T,
          cuspGreen 0 t u κ * Complex.exp (-(α : ℂ) * u) * f u := by
      have h := setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
        (cuspGreen_weighted_integrableOn_finite t T α κ f)
        (cuspGreen_weighted_integrableOn_tail hT htT hβ f)
      simpa only [Ioc_union_Ioi_eq_Ioi hT] using h
    _ = _ := by rw [cuspGreen_weighted_tail_integral hT htT hβ]

/-- An explicit source-truncation error bound for the actual weighted integral. -/
theorem cuspGreen_weighted_integral_remainder_le {t T α : ℝ} (hT : 0 ≤ T) (htT : t ≤ T)
    {κ : ℂ} (hβ : 0 < ((α : ℂ) + κ).re) (f : HalfLineL2) :
    ‖(∫ u : ℝ in Ioi 0,
        cuspGreen 0 t u κ * Complex.exp (-(α : ℂ) * u) * f u) -
      (∫ u : ℝ in Ioc 0 T,
        cuspGreen 0 t u κ * Complex.exp (-(α : ℂ) * u) * f u)‖ ≤
      ‖cuspGreenTailValue t κ‖ *
        (Real.exp (-((α : ℂ) + κ).re * T) / Real.sqrt (2 * ((α : ℂ) + κ).re) * ‖f‖) := by
  rw [cuspGreen_weighted_integral_split hT htT hβ f, add_sub_cancel_left, norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  exact ((tailLaplace T ((α : ℂ) + κ)).le_opNorm f).trans
    (mul_le_mul_of_nonneg_right (tailLaplace_norm_le hT hβ) (norm_nonneg f))

/-- Source truncation converges to the actual ordinary weighted Green response,
with no positivity condition on κ beyond the shifted Laplace half-plane. -/
theorem cuspGreen_weighted_integral_tendsto (t α : ℝ) {κ : ℂ}
    (hβ : 0 < ((α : ℂ) + κ).re) (f : HalfLineL2) :
    Tendsto (fun T : ℝ => ∫ u : ℝ in Ioc 0 T,
      cuspGreen 0 t u κ * Complex.exp (-(α : ℂ) * u) * f u)
      atTop (𝓝 (∫ u : ℝ in Ioi 0,
        cuspGreen 0 t u κ * Complex.exp (-(α : ℂ) * u) * f u)) := by
  have he : Tendsto (fun T : ℝ => Real.exp (-((α : ℂ) + κ).re * T)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp
      (tendsto_id.const_mul_atTop_of_neg (neg_neg_of_pos hβ))
  have hb := ((he.div_const (Real.sqrt (2 * ((α : ℂ) + κ).re))).mul_const ‖f‖).const_mul
    ‖cuspGreenTailValue t κ‖
  simp only [zero_div, zero_mul, mul_zero] at hb
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨R, hR⟩ := (Metric.tendsto_atTop.mp hb) ε hε
  refine ⟨max R (max 0 t), ?_⟩
  intro T hT
  have hT0 : 0 ≤ T := (le_max_left 0 t).trans ((le_max_right R (max 0 t)).trans hT)
  have htT : t ≤ T := (le_max_right 0 t).trans ((le_max_right R (max 0 t)).trans hT)
  have hTR : R ≤ T := (le_max_left R (max 0 t)).trans hT
  rw [dist_eq_norm, norm_sub_rev]
  exact (cuspGreen_weighted_integral_remainder_le hT0 htT hβ f).trans_lt
    (by simpa only [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity :
      0 ≤ ‖cuspGreenTailValue t κ‖ *
        (Real.exp (-((α : ℂ) + κ).re * T) / Real.sqrt (2 * ((α : ℂ) + κ).re) * ‖f‖))]
      using hR T hTR)

end GapFamily.Analytic
