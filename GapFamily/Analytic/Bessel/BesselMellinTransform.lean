import GapFamily.Analytic.Bessel.BesselMellinExp
import GapFamily.Analytic.Bessel.BesselMellinScale
import GapFamily.Analytic.Bessel.BesselCoshLogIntegral

noncomputable section
namespace GapFamily.Analytic.BesselCoshOrder
open MeasureTheory Set

/-- The symmetric reciprocal Gaussian Mellin kernel is ordinarily integrable at every order. -/
theorem mellinIntegrand_symmetric_integrable (κ : ℂ) {c : ℝ} (hc : 0 < c) :
    IntegrableOn (mellinIntegrand κ c c) (Ioi 0) := by
  apply (integrable_comp_exp (mellinIntegrand κ c c)).mp
  have he : (fun u : ℝ => Real.exp u • mellinIntegrand κ c c (Real.exp u)) =
      logKernel κ (2 * c) := by
    funext u
    exact mellin_exp_substitution κ c u
  rw [he]
  exact logKernel_integrable κ (show 0 < 2 * c by positivity)

/-- The symmetric Mellin integral has exactly twice the literal cosh normalization. -/
theorem integral_mellinIntegrand_symmetric (κ : ℂ) {c : ℝ} (hc : 0 < c) :
    (∫ t : ℝ in Ioi 0, mellinIntegrand κ c c t) = 2 * besselK κ (2 * c) := by
  rw [← integral_comp_exp]
  simpa only [mellinIntegrand, mellin_exp_substitution, logKernel] using
    integral_logKernel κ (show 0 < 2 * c by positivity)

/-- Ordinary absolute convergence of the actual complex-order reciprocal Gaussian Mellin kernel. -/
theorem mellinIntegrand_integrable (κ : ℂ) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IntegrableOn (mellinIntegrand κ a b) (Ioi 0) := by
  obtain ⟨hk, hkeq, hak, hbk⟩ := mellin_sqrt_scale_data ha hb
  let k : ℝ := Real.sqrt b / Real.sqrt a
  have hs : IntegrableOn (fun t : ℝ => (k : ℂ) ^ κ *
      mellinIntegrand κ (Real.sqrt (a * b)) (Real.sqrt (a * b)) t) (Ioi 0) :=
    (mellinIntegrand_symmetric_integrable κ
      (Real.sqrt_pos.mpr (mul_pos ha hb))).const_mul ((k : ℂ) ^ κ)
  have hscaled : IntegrableOn (fun t : ℝ => k • mellinIntegrand κ a b (k * t))
      (Ioi 0) := hs.congr_fun
    (fun t ht => (mellinIntegrand_scale (κ := κ) hk ht hak hbk).symm) measurableSet_Ioi
  have hu : IntegrableOn (fun t : ℝ => mellinIntegrand κ a b (k * t)) (Ioi 0) :=
    (integrable_fun_smul_iff hk.ne' _).mp hscaled
  simpa only [mul_zero] using
    (integrableOn_Ioi_comp_mul_left_iff (mellinIntegrand κ a b) 0 hk).mp hu

/-- The actual all-complex-order Mellin transform, with positive real coefficients and ordinary
Bochner integrals. The positive square root fixes the complex-power branch unambiguously. -/
theorem integral_mellinIntegrand (κ : ℂ) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (∫ t : ℝ in Ioi 0, mellinIntegrand κ a b t) =
      2 * (Real.sqrt (b / a) : ℂ) ^ κ * besselK κ (2 * Real.sqrt (a * b)) := by
  obtain ⟨hk, hkeq, hak, hbk⟩ := mellin_sqrt_scale_data ha hb
  let k : ℝ := Real.sqrt b / Real.sqrt a
  calc
    _ = k • ∫ t : ℝ in Ioi 0, mellinIntegrand κ a b (k * t) := by
      simpa only [mul_zero] using
        (integral_comp_mul_left_Ioi' (mellinIntegrand κ a b) 0 hk).symm
    _ = ∫ t : ℝ in Ioi 0, k • mellinIntegrand κ a b (k * t) :=
      (integral_smul k _).symm
    _ = ∫ t : ℝ in Ioi 0,
        (Real.sqrt (b / a) : ℂ) ^ κ *
          mellinIntegrand κ (Real.sqrt (a * b)) (Real.sqrt (a * b)) t :=
      setIntegral_congr_fun measurableSet_Ioi
        (fun t ht => mellinIntegrand_sqrt_scale κ ha hb ht)
    _ = (Real.sqrt (b / a) : ℂ) ^ κ * (2 * besselK κ (2 * Real.sqrt (a * b))) := by
      rw [integral_const_mul, integral_mellinIntegrand_symmetric κ
        (Real.sqrt_pos.mpr (mul_pos ha hb))]
    _ = _ := by ring

end GapFamily.Analytic.BesselCoshOrder
