import GapFamily.Analytic.Bessel.BesselShift
import GapFamily.Analytic.Bessel.BesselUpper
import GapFamily.Analytic.Bessel.BesselLower

/-!
# Ordinary convergence and two-sided bounds for `K₀`

The modified Bessel function is the source's actual integral over `(1,∞)`.
Its square-root exponential estimates are asserted on `t ≥ 1`.
-/

noncomputable section

namespace GapFamily.Analytic

open MeasureTheory Set

/-- The source's ordinary `K₀` integral genuinely converges at every positive argument. -/
theorem besselK0_integrable {t : ℝ} (ht : 0 < t) :
    IntegrableOn (besselK0Integrand t) (Ioi 1) :=
  (integrableOn_besselK0Integrand_iff t).mpr (besselK0ShiftIntegrand_integrable ht)

/-- Integrating the short endpoint interval supplies a square-root lower bound. -/
theorem besselK0Shift_integral_ge {t : ℝ} (ht : 1 ≤ t) :
    Real.exp (-1) / (Real.sqrt 3 * Real.sqrt t) ≤
      ∫ w : ℝ in Ioi 0, besselK0ShiftIntegrand t w := by
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have hi := besselK0ShiftIntegrand_integrable ht0
  have hsub : Ioc (0 : ℝ) (1 / t) ⊆ Ioi 0 := fun _ hx => hx.1
  calc
    _ = ∫ _ : ℝ in Ioc 0 (1 / t), Real.exp (-1) / Real.sqrt (3 / t) :=
      (besselK0Shift_lower_constant_integral ht0).symm
    _ ≤ ∫ w : ℝ in Ioc 0 (1 / t), besselK0ShiftIntegrand t w :=
      setIntegral_mono_on (integrableOn_const (ne_of_lt measure_Ioc_lt_top)) (hi.mono_set hsub) measurableSet_Ioc
        (fun _ hw => besselK0ShiftIntegrand_lower ht hw)
    _ ≤ ∫ w : ℝ in Ioi 0, besselK0ShiftIntegrand t w :=
      setIntegral_mono_set hi (Filter.Eventually.of_forall (fun w => by
        exact div_nonneg (Real.exp_pos _).le (Real.sqrt_nonneg _)))
        (Filter.Eventually.of_forall hsub)

/-- Explicit upper bound at every positive argument, obtained from the Gamma majorant. -/
theorem besselK0_le {t : ℝ} (ht : 0 < t) :
    besselK0 t ≤ (Real.sqrt Real.pi / Real.sqrt 2) *
      (Real.exp (-t) / Real.sqrt t) := by
  rw [besselK0_eq_shiftIntegral]
  calc
    _ ≤ Real.exp (-t) * (Real.sqrt Real.pi / (Real.sqrt 2 * Real.sqrt t)) :=
      mul_le_mul_of_nonneg_left (besselK0Shift_integral_le ht) (Real.exp_pos _).le
    _ = _ := by ring

/-- Explicit lower bound on `t≥1`; no false small-argument asymptotic is asserted. -/
theorem besselK0_ge {t : ℝ} (ht : 1 ≤ t) :
    (Real.exp (-1) / Real.sqrt 3) * (Real.exp (-t) / Real.sqrt t) ≤ besselK0 t := by
  rw [besselK0_eq_shiftIntegral]
  calc
    _ = Real.exp (-t) * (Real.exp (-1) / (Real.sqrt 3 * Real.sqrt t)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (besselK0Shift_integral_ge ht) (Real.exp_pos _).le

/-- The lower and upper constants are uniform throughout the large-argument range. -/
theorem besselK0_bounds {t : ℝ} (ht : 1 ≤ t) :
    (Real.exp (-1) / Real.sqrt 3) * (Real.exp (-t) / Real.sqrt t) ≤ besselK0 t ∧
      besselK0 t ≤ (Real.sqrt Real.pi / Real.sqrt 2) *
        (Real.exp (-t) / Real.sqrt t) :=
  ⟨besselK0_ge ht, besselK0_le (lt_of_lt_of_le zero_lt_one ht)⟩

/-- A positive Fourier-factor denominator on the range used by the arithmetic argument. -/
theorem besselK0_pos {t : ℝ} (ht : 1 ≤ t) : 0 < besselK0 t :=
  lt_of_lt_of_le (by have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht; positivity)
    (besselK0_ge ht)

end GapFamily.Analytic
