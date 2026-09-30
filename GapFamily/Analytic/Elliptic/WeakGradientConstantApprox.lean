import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Constancy from constant smooth approximations

Normalized smooth convolutions converge almost everywhere to a locally integrable
function. If every sufficiently small convolution is constant on a ball, the
original function agrees almost everywhere with one constant on that ball.
-/

noncomputable section

open ContinuousLinearMap Metric MeasureTheory Filter
open scoped Convolution Topology

namespace GapFamily.Analytic

/-- Almost-everywhere limits of constant mollifications are constant on a ball. -/
theorem exists_ae_eq_const_on_ball_of_normed_convolution_sequence
    {g : ℂ → ℂ} (hg : LocallyIntegrable g volume)
    {x : ℂ} {r : ℝ} (hr : 0 < r)
    {φ : ℕ → ContDiffBump (0 : ℂ)}
    (hφ : Tendsto (fun n => (φ n).rOut) atTop (𝓝 0))
    (hφRatio : ∀ᶠ n in atTop, (φ n).rOut ≤ 2 * (φ n).rIn)
    (hc : ∀ n z, z ∈ ball x r →
      ((φ n).normed volume ⋆[lsmul ℝ ℝ, volume] g) z =
        ((φ n).normed volume ⋆[lsmul ℝ ℝ, volume] g) x) :
    ∃ c : ℂ, g =ᵐ[volume.restrict (ball x r)] fun _ => c := by
  have hlim := ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable hφ hφRatio hg
  have hlimBall := ae_restrict_of_ae hlim (s := ball x r)
  obtain ⟨z, hz, hlimz⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    (ne_of_gt (measure_ball_pos volume x hr)) hlimBall
  refine ⟨g z, ?_⟩
  filter_upwards [hlimBall, ae_restrict_mem measurableSet_ball] with w hw hwB
  have heq : (fun n => ((φ n).normed volume ⋆[lsmul ℝ ℝ, volume] g) w) =
      fun n => ((φ n).normed volume ⋆[lsmul ℝ ℝ, volume] g) z := by
    funext n
    exact (hc n w hwB).trans (hc n z hz).symm
  rw [heq] at hw
  exact tendsto_nhds_unique hw hlimz

private def shrinkingBump (r : ℝ) (hr : 0 < r) (n : ℕ) : ContDiffBump (0 : ℂ) where
  rIn := (r / ((n : ℝ) + 2)) / 2
  rOut := r / ((n : ℝ) + 2)
  rIn_pos := by positivity
  rIn_lt_rOut := by
    have h : 0 < r / ((n : ℝ) + 2) := by positivity
    linarith

private theorem shrinkingBump_rOut_lt (r : ℝ) (hr : 0 < r) (n : ℕ) :
    (shrinkingBump r hr n).rOut < r := by
  change r / ((n : ℝ) + 2) < r
  rw [div_lt_iff₀ (by positivity : 0 < (n : ℝ) + 2)]
  have hn : (0 : ℝ) ≤ (n : ℝ) := by positivity
  nlinarith

private theorem shrinkingBump_rOut_le (r : ℝ) (hr : 0 < r) (n : ℕ) :
    (shrinkingBump r hr n).rOut ≤ 2 * (shrinkingBump r hr n).rIn := by
  dsimp [shrinkingBump]
  linarith

private theorem shrinkingBump_tendsto (r : ℝ) (hr : 0 < r) :
    Tendsto (fun n : ℕ => (shrinkingBump r hr n).rOut) atTop (𝓝 0) := by
  simpa [shrinkingBump, Nat.cast_add] using
    (tendsto_add_atTop_iff_nat 2).2 (tendsto_const_div_atTop_nhds_zero_nat r)

/-- A locally integrable function is almost everywhere constant on a positive-radius
ball when each sufficiently small normalized smooth convolution is constant there. -/
theorem exists_ae_eq_const_on_ball_of_normed_convolution_const
    {g : ℂ → ℂ} (hg : LocallyIntegrable g volume)
    {x : ℂ} {r : ℝ} (hr : 0 < r)
    (hc : ∀ φ : ContDiffBump (0 : ℂ), φ.rOut < r → ∀ z ∈ ball x r,
      (φ.normed volume ⋆[lsmul ℝ ℝ, volume] g) z =
        (φ.normed volume ⋆[lsmul ℝ ℝ, volume] g) x) :
    ∃ c : ℂ, g =ᵐ[volume.restrict (ball x r)] fun _ => c := by
  exact exists_ae_eq_const_on_ball_of_normed_convolution_sequence hg hr
    (shrinkingBump_tendsto r hr)
    (Eventually.of_forall (shrinkingBump_rOut_le r hr))
    (fun n => hc (shrinkingBump r hr n) (shrinkingBump_rOut_lt r hr n))

end GapFamily.Analytic
