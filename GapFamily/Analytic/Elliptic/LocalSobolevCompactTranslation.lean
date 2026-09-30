import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.Mul
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Group.Integral

/-!
# Quantitative Euclidean translation control

The ordinary squared L² error of translating a smooth compactly supported
complex-valued function is bounded by the squared displacement times its actual
Euclidean derivative energy. This is the quantitative input for local smoothing.
-/

noncomputable section

namespace GapFamily.Analytic.LocalSobolev

open Set MeasureTheory
open scoped ContDiff

theorem norm_integral_sq_le_integral_norm_sq {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsProbabilityMeasure μ] {f : α → ℂ}
    (hf : Integrable f μ) (hfsq : Integrable (fun x => ‖f x‖ ^ 2) μ) :
    ‖∫ x, f x ∂μ‖ ^ 2 ≤ ∫ x, ‖f x‖ ^ 2 ∂μ := by
  exact (convexOn_univ_norm.pow (fun _ _ => norm_nonneg _) 2).map_integral_le
    (by fun_prop) isClosed_univ (Filter.Eventually.of_forall fun _ => mem_univ _)
    hf hfsq

private instance unitInterval_probability :
    IsProbabilityMeasure (volume.restrict (Icc (0 : ℝ) 1)) where
  measure_univ := by simp

/-- FTC and Jensen give a pointwise translation error controlled by the derivative
energy on the connecting line segment. -/
theorem translation_error_sq_le_segment_energy (f : ℂ → ℂ)
    (hf : ContDiff ℝ 1 f) (x h : ℂ) :
    ‖f (x + h) - f x‖ ^ 2 ≤
      ‖h‖ ^ 2 * ∫ t in Icc (0 : ℝ) 1, ‖fderiv ℝ f (x + t • h)‖ ^ 2 := by
  have hD : Continuous (fderiv ℝ f) := hf.continuous_fderiv (by norm_num)
  have hpath : Continuous (fun t : ℝ => fderiv ℝ f (x + t • h) h) := by fun_prop
  have hFTC : (∫ t in Icc (0 : ℝ) 1, fderiv ℝ f (x + t • h) h) =
      f (x + h) - f x := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one]
    have hder (t : ℝ) :
        HasDerivAt (fun t : ℝ => f (x + t • h))
          (fderiv ℝ f (x + t • h) h) t := by
      exact ((hf.differentiable (by norm_num) _).hasFDerivAt).comp_hasDerivAt t
        (by simpa using ((hasDerivAt_id t).smul_const h |>.const_add x))
    simpa using intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t _ => hder t) (hpath.intervalIntegrable 0 1)
  rw [← hFTC]
  refine (norm_integral_sq_le_integral_norm_sq
    hpath.continuousOn.integrableOn_Icc
    (hpath.norm.pow 2).continuousOn.integrableOn_Icc).trans ?_
  rw [← integral_const_mul]
  apply integral_mono
  · exact (hpath.norm.pow 2).continuousOn.integrableOn_Icc
  · exact (show Continuous (fun t : ℝ =>
      ‖h‖ ^ 2 * ‖fderiv ℝ f (x + t • h)‖ ^ 2) by fun_prop).continuousOn.integrableOn_Icc
  · intro t
    have hp := (fderiv ℝ f (x + t • h)).le_opNorm h
    calc
      _ ≤ (‖fderiv ℝ f (x + t • h)‖ * ‖h‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hp 2
      _ = _ := by ring


/-- Joint integrability of the translated derivative energy is proved from the
actual global energy integral, using translation invariance. -/
theorem integrable_segment_energy (f : ℂ → ℂ) (hf : ContDiff ℝ 1 f)
    (henergy : Integrable (fun z => ‖fderiv ℝ f z‖ ^ 2)) (h : ℂ) :
    Integrable (fun p : ℝ × ℂ => ‖fderiv ℝ f (p.2 + p.1 • h)‖ ^ 2)
      ((volume.restrict (Icc (0 : ℝ) 1)).prod volume) := by
  have hD : Continuous (fderiv ℝ f) := hf.continuous_fderiv (by norm_num)
  apply (integrable_prod_iff (show Continuous (fun p : ℝ × ℂ =>
    ‖fderiv ℝ f (p.2 + p.1 • h)‖ ^ 2) by fun_prop).aestronglyMeasurable).mpr
  constructor
  · exact Filter.Eventually.of_forall fun t => henergy.comp_add_right (t • h)
  · have htrans (t : ℝ) : (∫ z : ℂ, ‖fderiv ℝ f (z + t • h)‖ ^ 2) =
        ∫ z : ℂ, ‖fderiv ℝ f z‖ ^ 2 :=
      integral_add_right_eq_self (fun z : ℂ => ‖fderiv ℝ f z‖ ^ 2) (t • h)
    simp_rw [Real.norm_of_nonneg (sq_nonneg _), htrans]
    exact
      (integrable_const (∫ z : ℂ, ‖fderiv ℝ f z‖ ^ 2) :
        Integrable (fun _ : ℝ => ∫ z : ℂ, ‖fderiv ℝ f z‖ ^ 2)
          (volume.restrict (Icc (0 : ℝ) 1)))

/-- The ordinary squared translation error is integrable whenever the actual
derivative energy is integrable. -/
theorem integrable_translation_error_sq (f : ℂ → ℂ) (hf : ContDiff ℝ 1 f)
    (henergy : Integrable (fun z => ‖fderiv ℝ f z‖ ^ 2)) (h : ℂ) :
    Integrable (fun z => ‖f (z + h) - f z‖ ^ 2) := by
  have hmaj := (integrable_segment_energy f hf henergy h).integral_prod_right.const_mul (‖h‖ ^ 2)
  apply hmaj.mono'
  · exact (show Continuous (fun z => ‖f (z + h) - f z‖ ^ 2) by fun_prop).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun z => by
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact translation_error_sq_le_segment_energy f hf z h

/-- Quantitative L² translation estimate in the Euclidean plane, with no
assumed translation-continuity bound. -/
theorem integral_translation_error_sq_le (f : ℂ → ℂ) (hf : ContDiff ℝ 1 f)
    (henergy : Integrable (fun z => ‖fderiv ℝ f z‖ ^ 2)) (h : ℂ) :
    (∫ z : ℂ, ‖f (z + h) - f z‖ ^ 2) ≤
      ‖h‖ ^ 2 * ∫ z : ℂ, ‖fderiv ℝ f z‖ ^ 2 := by
  have hjoint := integrable_segment_energy f hf henergy h
  calc
    _ ≤ ∫ z : ℂ, ‖h‖ ^ 2 * ∫ t in Icc (0 : ℝ) 1,
        ‖fderiv ℝ f (z + t • h)‖ ^ 2 := by
      apply integral_mono (integrable_translation_error_sq f hf henergy h)
        (hjoint.integral_prod_right.const_mul _)
      intro z
      exact translation_error_sq_le_segment_energy f hf z h
    _ = ‖h‖ ^ 2 * ∫ z : ℂ, ‖fderiv ℝ f z‖ ^ 2 := by
      rw [integral_const_mul, ← integral_integral_swap
        (f := fun t z => ‖fderiv ℝ f (z + t • h)‖ ^ 2) hjoint]
      have htrans (t : ℝ) : (∫ z : ℂ, ‖fderiv ℝ f (z + t • h)‖ ^ 2) =
          ∫ z : ℂ, ‖fderiv ℝ f z‖ ^ 2 :=
        integral_add_right_eq_self (fun z : ℂ => ‖fderiv ℝ f z‖ ^ 2) (t • h)
      simp_rw [htrans]
      simp [Measure.real]

/-- Smooth compactly supported functions have actual finite derivative energy. -/
theorem integrable_fderiv_energy (f : ℂ → ℂ) (hf : ContDiff ℝ 1 f)
    (hc : HasCompactSupport f) :
    Integrable (fun z => ‖fderiv ℝ f z‖ ^ 2) := by
  apply ((hf.continuous_fderiv (by norm_num)).norm.pow 2).integrable_of_hasCompactSupport
  simpa only [pow_two] using (hc.fderiv ℝ).norm.mul_left (f := fun z => ‖fderiv ℝ f z‖)

/-- The finite-energy premise is discharged for every smooth compactly supported function. -/
theorem integral_translation_error_sq_le_of_hasCompactSupport
    (f : ℂ → ℂ) (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) (h : ℂ) :
    (∫ z : ℂ, ‖f (z + h) - f z‖ ^ 2) ≤
      ‖h‖ ^ 2 * ∫ z : ℂ, ‖fderiv ℝ f z‖ ^ 2 :=
  integral_translation_error_sq_le f hf (integrable_fderiv_energy f hf hc) h

end GapFamily.Analytic.LocalSobolev
