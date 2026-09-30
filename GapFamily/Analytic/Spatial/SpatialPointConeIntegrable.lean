import GapFamily.Analytic.Spatial.SpatialPointKernelBasic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.MeasureTheory.Integral.Prod

/-! Absolute integrability of the complex cone density and its frequency
marginal. The estimate splits the exponential decay between the energy and
frequency variables, and uses no Fourier-transform identity. -/

noncomputable section

namespace GapFamily.Analytic.SpatialPoint

open MeasureTheory Set Real

private theorem integrable_exp_neg_mul_abs {t : ℝ} (ht : 0 < t) :
    Integrable (fun J : ℝ => exp (-t * |J|)) := by
  rw [← integrableOn_univ, ← Iic_union_Ioi (a := (0 : ℝ))]
  apply IntegrableOn.union
  · apply (integrableOn_exp_mul_Iic ht 0).congr
    filter_upwards [ae_restrict_mem measurableSet_Iic] with J hJ
    simp only [abs_of_nonpos (show J ≤ 0 from hJ), mul_neg, neg_mul, neg_neg]
  · apply (integrableOn_exp_mul_Ioi (neg_lt_zero.mpr ht) 0).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with J hJ
    rw [abs_of_pos (show 0 < J from hJ)]

/-- The full same-parameter cone density is ordinarily integrable on its
two-dimensional domain. -/
theorem integrableOn_complexPointConeDensity {s : ℂ} (hs : 1 < s.re)
    {Y : ℝ} (hY : 0 < Y) :
    IntegrableOn (fun p : ℝ × ℝ =>
      ((p.2 ^ 2 - p.1 ^ 2 : ℝ) : ℂ) ^ (s - 1) *
        Complex.exp ((-2 * Real.pi * Y * p.2 : ℝ) : ℂ))
      {p : ℝ × ℝ | |p.1| < p.2} := by
  let t : ℝ := Real.pi * Y
  have ht : 0 < t := mul_pos pi_pos hY
  have hpow : 0 < (s - 1).re := by simp only [Complex.sub_re, Complex.one_re]; linarith
  have henergy : IntegrableOn
      (fun E : ℝ => E ^ (2 * (s.re - 1)) * exp (-t * E)) (Ioi 0) := by
    simpa only [Real.rpow_one, neg_mul] using
      (integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := 2 * (s.re - 1))
        (b := t) (by linarith) zero_lt_one ht)
  have hmajorant := (integrable_exp_neg_mul_abs ht).mul_prod
    ((integrable_indicator_iff measurableSet_Ioi).mpr henergy)
  have hm : MeasurableSet {p : ℝ × ℝ | |p.1| < p.2} :=
    (isOpen_lt continuous_fst.abs continuous_snd).measurableSet
  rw [← integrable_indicator_iff hm]
  change Integrable _ (volume.prod volume)
  apply hmajorant.mono'
  · apply AEStronglyMeasurable.indicator _ hm
    apply Continuous.aestronglyMeasurable
    exact ((Complex.continuous_ofReal_cpow_const hpow).comp
      (by fun_prop : Continuous (fun p : ℝ × ℝ => p.2 ^ 2 - p.1 ^ 2))).mul
        (by fun_prop)
  · apply Filter.Eventually.of_forall
    intro p
    by_cases hp : |p.1| < p.2
    · have hE : 0 < p.2 := (abs_nonneg _).trans_lt hp
      have hb : 0 < p.2 ^ 2 - p.1 ^ 2 := by
        nlinarith [sq_abs p.1, (sq_lt_sq₀ (abs_nonneg p.1) hE.le).mpr hp]
      rw [Set.indicator_of_mem (show p ∈ {p : ℝ × ℝ | |p.1| < p.2} from hp),
        Set.indicator_of_mem (show p.2 ∈ Ioi 0 from hE)]
      simp only [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hb,
        Complex.sub_re, Complex.one_re, Complex.norm_exp, Complex.ofReal_re]
      have hpowers : (p.2 ^ 2 - p.1 ^ 2) ^ (s.re - 1) ≤
          p.2 ^ (2 * (s.re - 1)) := by
        calc
          _ ≤ (p.2 ^ 2) ^ (s.re - 1) :=
            Real.rpow_le_rpow hb.le (by nlinarith [sq_nonneg p.1]) (by linarith)
          _ = _ := by rw [← Real.rpow_two, ← Real.rpow_mul hE.le]
      have hexp : exp (-2 * Real.pi * Y * p.2) ≤
          exp (-t * |p.1|) * exp (-t * p.2) := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        dsimp [t] at *
        nlinarith [mul_le_mul_of_nonneg_left hp.le ht.le]
      calc
        _ ≤ p.2 ^ (2 * (s.re - 1)) *
            (exp (-t * |p.1|) * exp (-t * p.2)) :=
          mul_le_mul hpowers hexp (exp_pos _).le (Real.rpow_nonneg hE.le _)
        _ = _ := by ring
    · rw [Set.indicator_of_notMem (show p ∉ {p : ℝ × ℝ | |p.1| < p.2} from hp),
        norm_zero]
      apply mul_nonneg (exp_pos _).le
      exact Set.indicator_nonneg (fun E hE => mul_nonneg
        (Real.rpow_nonneg (le_of_lt (show 0 < E from hE)) _)
        (exp_pos _).le) _

/-- Integrating the complex cone density over energy gives an ordinary
integrable function of the real Fourier frequency. -/
theorem integrable_complexPointConeDensity_frequency {s : ℂ} (hs : 1 < s.re)
    {Y : ℝ} (hY : 0 < Y) :
    Integrable (fun J : ℝ => ∫ E : ℝ in Ioi |J|,
      ((E ^ 2 - J ^ 2 : ℝ) : ℂ) ^ (s - 1) *
        Complex.exp ((-2 * Real.pi * Y * E : ℝ) : ℂ)) := by
  have hm : MeasurableSet {p : ℝ × ℝ | |p.1| < p.2} :=
    (isOpen_lt continuous_fst.abs continuous_snd).measurableSet
  have hi := (integrable_indicator_iff hm).mpr (integrableOn_complexPointConeDensity hs hY)
  change Integrable _ (volume.prod volume) at hi
  convert hi.integral_prod_left using 1
  ext J
  rw [← integral_indicator measurableSet_Ioi]
  rfl

end GapFamily.Analytic.SpatialPoint
