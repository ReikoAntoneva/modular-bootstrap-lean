import Mathlib.Topology.EMetricSpace.BoundedVariation
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import GapFamily.Quadrature.Midpoint

/-!
# Derivative bounds for partition variation

This is the bridge from estimates of the integral of the absolute derivative to
the partition variation used in the midpoint and quadrature argument.
-/

open Set MeasureTheory

namespace GapFamily.Quadrature

/-- Total variation is bounded by the integral of the speed. The hypotheses
allow arbitrary normed real vector spaces and only require differentiability
in the interior and integrability of the norm of the derivative. -/
theorem eVariationOn_le_integral_norm_deriv {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {f : ℝ → E} {a b : ℝ}
    (hab : a ≤ b) (hf : ContinuousOn f (Icc a b))
    (hfd : DifferentiableOn ℝ f (Ioo a b))
    (hfi : IntervalIntegrable (fun x => ‖deriv f x‖) volume a b) :
    eVariationOn f (Icc a b) ≤ ENNReal.ofReal (∫ x in a..b, ‖deriv f x‖) := by
  apply iSup_le
  rintro ⟨n, u, hu, humem⟩
  have hsub (i : ℕ) : Icc (u i) (u (i + 1)) ⊆ Icc a b :=
    Icc_subset_Icc (humem i).1 (humem (i + 1)).2
  have hsubopen (i : ℕ) : Ioo (u i) (u (i + 1)) ⊆ Ioo a b :=
    Ioo_subset_Ioo (humem i).1 (humem (i + 1)).2
  have hint (i : ℕ) : IntervalIntegrable (fun x => ‖deriv f x‖) volume
      (u i) (u (i + 1)) := by
    apply hfi.mono_set
    simpa only [uIcc_of_le hab, uIcc_of_le (hu (Nat.le_succ i))] using hsub i
  have hsum : (∑ i ∈ Finset.range n, ‖f (u (i + 1)) - f (u i)‖) ≤
      ∫ x in a..b, ‖deriv f x‖ := by
    calc
      _ ≤ ∑ i ∈ Finset.range n, ∫ x in u i..u (i + 1), ‖deriv f x‖ := by
        apply Finset.sum_le_sum
        intro i _hi
        exact norm_sub_le_integral_of_norm_deriv_le_of_le (hu (Nat.le_succ i))
          (hf.mono (hsub i)) (hfd.mono (hsubopen i))
          (Filter.Eventually.of_forall fun _ _ => le_rfl) (hint i)
      _ = ∫ x in u 0..u n, ‖deriv f x‖ :=
        intervalIntegral.sum_integral_adjacent_intervals (fun i _hi => hint i)
      _ ≤ ∫ x in a..b, ‖deriv f x‖ :=
        intervalIntegral.integral_mono_interval (humem 0).1 (hu (Nat.zero_le n))
          (humem n).2 (Filter.Eventually.of_forall fun _ => norm_nonneg _) hfi
  simpa only [edist_dist, dist_eq_norm,
    ENNReal.ofReal_sum_of_nonneg (fun i _hi => norm_nonneg (f (u (i + 1)) - f (u i)))]
    using ENNReal.ofReal_le_ofReal hsum

/-- The derivative integral bound also proves finiteness of partition
variation; it is not a separate assumption. -/
theorem boundedVariationOn_of_integrable_norm_deriv {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {f : ℝ → E} {a b : ℝ}
    (hab : a ≤ b) (hf : ContinuousOn f (Icc a b))
    (hfd : DifferentiableOn ℝ f (Ioo a b))
    (hfi : IntervalIntegrable (fun x => ‖deriv f x‖) volume a b) :
    BoundedVariationOn f (Icc a b) :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    (eVariationOn_le_integral_norm_deriv hab hf hfd hfi)

/-- Real-valued form of the derivative integral bound. -/
theorem variation_le_integral_norm_deriv {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {f : ℝ → E} {a b : ℝ}
    (hab : a ≤ b) (hf : ContinuousOn f (Icc a b))
    (hfd : DifferentiableOn ℝ f (Ioo a b))
    (hfi : IntervalIntegrable (fun x => ‖deriv f x‖) volume a b) :
    (eVariationOn f (Icc a b)).toReal ≤ ∫ x in a..b, ‖deriv f x‖ := by
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top
    (eVariationOn_le_integral_norm_deriv hab hf hfd hfi)
  simpa only [ENNReal.toReal_ofReal
    (intervalIntegral.integral_nonneg hab fun _ _ => norm_nonneg _)] using h

/-- Every real polynomial has bounded partition variation on a compact
interval, with the derivative-integral bound used in C3 and source X. -/
theorem polynomial_variation_le_integral_abs_derivative (p : Polynomial ℝ)
    {a b : ℝ} (hab : a ≤ b) :
    (eVariationOn p.eval (Icc a b)).toReal ≤ ∫ x in a..b, |p.derivative.eval x| := by
  have hfi : IntervalIntegrable (fun x => ‖deriv p.eval x‖) volume a b := by
    simpa only [p.deriv] using p.derivative.differentiable.continuous.norm.intervalIntegrable a b
  simpa only [p.deriv, Real.norm_eq_abs] using
    variation_le_integral_norm_deriv hab p.differentiable.continuous.continuousOn
      p.differentiable.differentiableOn hfi

theorem polynomial_boundedVariationOn (p : Polynomial ℝ) {a b : ℝ} (hab : a ≤ b) :
    BoundedVariationOn p.eval (Icc a b) := by
  apply boundedVariationOn_of_integrable_norm_deriv hab p.differentiable.continuous.continuousOn
    p.differentiable.differentiableOn
  simpa only [p.deriv] using p.derivative.differentiable.continuous.norm.intervalIntegrable a b

/-- The quantile midpoint estimate with the derivative-integral variation
convention in source X, proved from the partition estimate rather than assumed. -/
theorem polynomial_monotone_transport_midpoint_error (p : Polynomial ℝ)
    {q : ℝ → ℝ} {a b : ℝ} {n : ℕ} (hn : 0 < n) (hab : a ≤ b)
    (hq : ContinuousOn q (Icc 0 1)) (hm : MonotoneOn q (Icc 0 1))
    (hmap : MapsTo q (Icc 0 1) (Icc a b)) :
    |(1 / (n : ℝ)) * (∑ i ∈ Finset.range n, p.eval (q (((i : ℝ) + 1 / 2) / n))) -
        ∫ x in (0 : ℝ)..1, p.eval (q x)| ≤
      (1 / (2 * (n : ℝ))) * (∫ x in a..b, |p.derivative.eval x|) := by
  exact (monotone_transport_midpoint_error hn p.differentiable.continuous.continuousOn
    (polynomial_boundedVariationOn p hab) hq hm hmap).trans
      (mul_le_mul_of_nonneg_left (polynomial_variation_le_integral_abs_derivative p hab)
        (by positivity))

end GapFamily.Quadrature
