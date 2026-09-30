import GapFamily.Analytic.Foundation.IntervalTrace
import GapFamily.Analytic.Cusp.Fourier.CuspHorizontalSlice

/-! # Ordinary integral helpers for a cusp collar

Continuity is established before integrating any trace or energy estimate.
The vertical integral has horizontal parameter, with a positive-height compact
interval of integration.
-/

noncomputable section
namespace GapFamily.Analytic

open Set MeasureTheory UpperHalfPlane

theorem continuous_cuspVerticalIntegral {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {F : ℂ → E} (hF : ContinuousOn F upperHalfPlaneSet)
    {ε : ℝ} (hε : 0 ≤ ε) :
    Continuous (fun x : ℝ => ∫ y in (1 : ℝ)..1 + ε, F (Complex.mk x y)) := by
  let G : ℝ → ℝ → E := fun x y => F (Complex.mk x (max 1 y))
  have hc : Continuous (Function.uncurry G) := by
    apply hF.comp_continuous
    · simp only [cuspPoint_eq]
      fun_prop
    · intro p
      exact lt_of_lt_of_le zero_lt_one (le_max_left 1 p.2)
  have hint := continuous_parametric_integral_of_continuous (μ := volume) hc
    (s := Icc (1 : ℝ) (1 + ε)) isCompact_Icc
  apply hint.congr
  intro x
  rw [intervalIntegral.integral_of_le (by linarith : (1 : ℝ) ≤ 1 + ε),
    ← integral_Icc_eq_integral_Ioc]
  apply setIntegral_congr_fun measurableSet_Icc
  intro y hy
  simp only [G, max_eq_right hy.1]

/-- Cauchy's integral inequality for the width-one horizontal interval. -/
theorem cusp_horizontal_integral_sq_le {g : ℝ → ℂ} (hg : Continuous g) :
    ‖∫ x in (-1/2 : ℝ)..(1/2), g x‖^2 ≤
      ∫ x in (-1/2 : ℝ)..(1/2), ‖g x‖^2 := by
  have hn := intervalIntegral.norm_integral_le_integral_norm
    (f := g) (μ := volume) (by norm_num : (-1/2 : ℝ) ≤ 1/2)
  have hnonneg : 0 ≤ ∫ x in (-1/2 : ℝ)..(1/2), ‖g x‖ :=
    intervalIntegral.integral_nonneg (by norm_num) (fun _ _ => norm_nonneg _)
  have hcs := IntervalTrace.integral_sq_le_length_mul_integral_sq
    (by norm_num : (-1/2 : ℝ) < 1/2) hg.norm.continuousOn
  exact ((sq_le_sq₀ (norm_nonneg _) hnonneg).mpr hn).trans (by norm_num at hcs ⊢; exact hcs)

end GapFamily.Analytic
