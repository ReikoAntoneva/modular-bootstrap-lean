import GapFamily.Analytic.Cusp.CuspPoincareResidualSource
import GapFamily.Analytic.Cusp.Profile.CuspWeightedInput

/-! The actual decay multiplier removes the residual source's proved height weight. -/
noncomputable section
namespace GapFamily.Analytic
open MeasureTheory

/-- The weighted Hilbert source becomes the literal unweighted residual source under
actual cusp-height decay. This is an equality of the constructed L² vectors. -/
theorem cuspWeightedInput_poincareResidualSource (J : ℤ) (α : ℝ) (hα : 0 ≤ α)
    {κ : ℂ} (hκ : α - 1 / 2 < κ.re) :
    cuspWeightedInput α hα (cuspPoincareResidualSource J α hα κ) =
      cuspPoincareResidualSource J 0 (by norm_num) κ := by
  have hκ0 : (0 : ℝ) - 1 / 2 < κ.re := by linarith
  apply Lp.ext
  filter_upwards [cuspWeightedInput_ae α hα (cuspPoincareResidualSource J α hα κ),
    cuspPoincareResidualSource_ae J α hα hκ,
    cuspPoincareResidualSource_ae J 0 (by norm_num) hκ0] with τ hw hαrep h0rep
  rw [hw, hαrep, h0rep]
  have hc : ((τ.im ^ (-α) : ℝ) : ℂ) * ((τ.im ^ α : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, ← Real.rpow_add τ.im_pos]
    simp
  rw [← mul_assoc, hc]
  simp

end GapFamily.Analytic
