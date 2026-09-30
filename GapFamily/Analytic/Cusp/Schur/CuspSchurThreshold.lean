import GapFamily.Analytic.Cusp.Schur.CuspSchurDenominatorAnalytic
import GapFamily.Analytic.Cusp.MeanZero.CuspMeanZeroGap

/-!
# The actual scalar threshold denominator

The proved constrained geometric gap discharges quarter-pencil regularity and
constant-pairing positivity. This gives scalar analyticity and nonvanishing at
threshold, including an analytic reciprocal. The physical agreement theorem
transfers nonvanishing back to the actual denominator in the physical half-plane.
No W-valued or unweighted full-resolvent continuation at threshold is asserted.
-/

noncomputable section
namespace GapFamily.Analytic.CuspSchur
open Filter
open scoped Topology

theorem continuedDenominator_threshold_re_neg : (continuedDenominator 0).re < 0 :=
  continuedDenominator_zero_re_neg cuspMeanZero_quarter_constant_pairing_nonneg

theorem continuedDenominator_threshold_ne_zero : continuedDenominator 0 ≠ 0 :=
  continuedDenominator_zero_ne_zero cuspMeanZero_quarter_constant_pairing_nonneg

theorem continuedDenominator_threshold_analyticAt : AnalyticAt ℂ continuedDenominator 0 :=
  continuedDenominator_analyticAt_zero cuspMeanZeroPencil_isUnit_quarter

theorem continuedDenominator_threshold_eventually_ne_zero :
    ∀ᶠ κ in 𝓝 (0 : ℂ), continuedDenominator κ ≠ 0 :=
  continuedDenominator_eventually_ne_zero cuspMeanZeroPencil_isUnit_quarter
    cuspMeanZero_quarter_constant_pairing_nonneg

theorem continuedDenominator_inverse_analyticAt_threshold :
    AnalyticAt ℂ (fun κ => (continuedDenominator κ)⁻¹) 0 :=
  continuedDenominator_threshold_analyticAt.inv continuedDenominator_threshold_ne_zero

/-- Nearby physical scalar denominators are genuinely nonzero. This is not a
claim that the W form-space response extends to the boundary point. -/
theorem actualSchurDenominator_eventually_ne_zero_physical :
    ∀ᶠ κ in 𝓝 (0 : ℂ), 0 < κ.re →
      actualSchurDenominator ((1 / 4 : ℂ) - κ ^ 2) ≠ 0 := by
  filter_upwards [continuedDenominator_threshold_eventually_ne_zero] with κ hκ hphysical
  rw [actualSchurDenominator_eq_continued hphysical]
  exact hκ

end GapFamily.Analytic.CuspSchur
