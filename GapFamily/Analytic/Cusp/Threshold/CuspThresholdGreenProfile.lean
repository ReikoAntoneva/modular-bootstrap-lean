import GapFamily.Analytic.Cusp.Green.CuspGreenWeightedLocal
import Mathlib.Topology.Order.ProjIcc

/-! The actual weighted threshold Green integral as a logarithmic profile. -/
noncomputable section
namespace GapFamily.Analytic.CuspThresholdGreenProfile
open Set Filter MeasureTheory CuspHalfLineLaplace
open scoped Topology

/-- This is the ordinary weighted integral of the actual removable Green kernel. -/
def greenProfile (α : ℝ) (f : HalfLineL2) (t : ℝ) : ℂ :=
  ∫ u : ℝ in Ioi 0,
    cuspGreen 0 t u 0 * Complex.exp (-(α : ℂ) * u) * f u

theorem greenProfile_integrable {α : ℝ} (hα : 0 < α) (f : HalfLineL2) (t : ℝ) :
    IntegrableOn (fun u : ℝ =>
      cuspGreen 0 t u 0 * Complex.exp (-(α : ℂ) * u) * f u) (Ioi 0) :=
  cuspGreen_weighted_integrable (le_max_left 0 t) (le_max_right 0 t)
    (by simpa using hα) f

/-- Every output collar agrees with the same actual noncompact source integral. -/
theorem greenProfile_eq_local {α L T : ℝ} (hα : 0 < α)
    (hT : 0 ≤ T) (hLT : L ≤ T) (f : HalfLineL2) (t : CuspGreenCollar 0 L) :
    greenProfile α f t = cuspGreenWeightedLocalOperator α hα.le L T 0 f t :=
  (cuspGreenWeightedLocalOperator_apply hα.le hT hLT (by simpa using hα) f t).symm

/-- The actual profile is continuous on every nonnegative compact interval. -/
theorem greenProfile_continuousOn_Icc {α L : ℝ} (hα : 0 < α) (hL : 0 ≤ L)
    (f : HalfLineL2) : ContinuousOn (greenProfile α f) (Icc 0 L) := by
  apply continuousOn_iff_continuous_domRestrict.mpr
  have he : (fun t : CuspGreenCollar 0 L => greenProfile α f t) =
      (cuspGreenWeightedLocalOperator α hα.le L L 0 f : C(CuspGreenCollar 0 L, ℂ)) := by
    funext t
    exact greenProfile_eq_local hα hL le_rfl f t
  change Continuous (fun t : CuspGreenCollar 0 L => greenProfile α f t)
  rw [he]
  exact ContinuousMap.continuous _

/-- Every positive logarithmic height has actual continuity of the integral. -/
theorem greenProfile_continuousAt {α t : ℝ} (hα : 0 < α) (ht : 0 < t)
    (f : HalfLineL2) : ContinuousAt (greenProfile α f) t :=
  (greenProfile_continuousOn_Icc hα (by linarith : 0 ≤ t + 1) f).continuousAt
    (Icc_mem_nhds ht (by linarith))

theorem greenProfile_continuousOn {α : ℝ} (hα : 0 < α) (f : HalfLineL2) :
    ContinuousOn (greenProfile α f) (Ioi 0) :=
  fun _ ht => (greenProfile_continuousAt hα ht f).continuousWithinAt

end GapFamily.Analytic.CuspThresholdGreenProfile
