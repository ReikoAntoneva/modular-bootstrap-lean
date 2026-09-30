import Mathlib.Analysis.MellinTransform
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Topology.ContinuousMap.Compact

/-!
# Horizontal averaging as a bounded linear functional

The functional integrates an actual continuous function on the unit interval.
It commutes with every genuinely convergent vector-valued Mellin transform.
-/

noncomputable section

namespace GapFamily.Analytic

open MeasureTheory Set
open scoped Topology

/-- The compact horizontal fundamental interval. -/
abbrev HorizontalInterval := Set.Icc (0 : ℝ) 1

/-- Continuous clamping permits an ordinary interval integral without extending by a jump. -/
def horizontalAverage : C(HorizontalInterval, ℂ) →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun f => ∫ x : ℝ in 0..1, f (Set.projIcc 0 1 zero_le_one x)
      map_add' := by
        intro f g
        exact intervalIntegral.integral_add
          ((f.continuous.comp continuous_projIcc).intervalIntegrable 0 1)
          ((g.continuous.comp continuous_projIcc).intervalIntegrable 0 1)
      map_smul' := by
        intro c f
        exact intervalIntegral.integral_smul c _ }
    1 (by
      intro f
      simpa using intervalIntegral.norm_integral_le_of_norm_le_const
        (a := (0 : ℝ)) (b := 1)
        (fun x _ => f.norm_coe_le_norm (Set.projIcc 0 1 zero_le_one x)))

@[simp] theorem horizontalAverage_apply (f : C(HorizontalInterval, ℂ)) :
    horizontalAverage f = ∫ x : ℝ in 0..1, f (Set.projIcc 0 1 zero_le_one x) := rfl

@[simp] theorem horizontalAverage_const (c : ℂ) :
    horizontalAverage (ContinuousMap.const HorizontalInterval c) = c := by
  simp [horizontalAverage_apply]

@[simp] theorem horizontalAverage_one :
    horizontalAverage (1 : C(HorizontalInterval, ℂ)) = 1 := by
  simp [horizontalAverage_apply]

/-- This functional is the usual horizontal integral of any representative agreeing on the interval. -/
theorem horizontalAverage_eq_intervalIntegral (f : C(HorizontalInterval, ℂ)) (g : ℝ → ℂ)
    (hfg : ∀ x : HorizontalInterval, f x = g x) :
    horizontalAverage f = ∫ x : ℝ in 0..1, g x := by
  rw [horizontalAverage_apply]
  apply intervalIntegral.integral_congr
  intro x hx
  have hx' : x ∈ Icc (0 : ℝ) 1 := by simpa using hx
  change f (Set.projIcc 0 1 zero_le_one x) = g x
  rw [Set.projIcc_of_mem zero_le_one hx']
  exact hfg ⟨x, hx'⟩

/-- Applying the horizontal integral preserves a convergent Mellin-transform certificate. -/
theorem horizontalAverage_hasMellin {f : ℝ → C(HorizontalInterval, ℂ)}
    {s : ℂ} {v : C(HorizontalInterval, ℂ)} (h : HasMellin f s v) :
    HasMellin (fun t => horizontalAverage (f t)) s (horizontalAverage v) := by
  constructor
  · have hi := horizontalAverage.integrable_comp h.1
    change Integrable (fun t : ℝ => (t : ℂ) ^ (s - 1) • horizontalAverage (f t))
      (volume.restrict (Ioi 0))
    simpa only [Function.comp_def, map_smul] using hi
  · change (∫ t : ℝ in Ioi 0, (t : ℂ) ^ (s - 1) • horizontalAverage (f t)) = _
    simp_rw [← map_smul]
    rw [horizontalAverage.integral_comp_comm h.1]
    exact congrArg horizontalAverage h.2

/-- Mellin certificates depend only on the integrand at positive times. -/
theorem hasMellin_congr_Ioi {f g : ℝ → ℂ} {s v : ℂ} (hf : HasMellin f s v)
    (hfg : Set.EqOn f g (Ioi 0)) : HasMellin g s v := by
  have hweighted : Set.EqOn (fun t : ℝ => (t : ℂ) ^ (s - 1) • f t)
      (fun t : ℝ => (t : ℂ) ^ (s - 1) • g t) (Ioi 0) := by
    intro t ht
    dsimp only
    rw [hfg ht]
  refine ⟨(integrableOn_congr_fun hweighted measurableSet_Ioi).mp hf.1, ?_⟩
  exact (setIntegral_congr_fun measurableSet_Ioi hweighted).symm.trans hf.2

end GapFamily.Analytic
