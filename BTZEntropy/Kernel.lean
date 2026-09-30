import BTZEntropy.Observable
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed

/-!
# A normalized smooth kernel

A fixed bump on the real line gives an actual member of `SmoothKernel`.
The normalization divides by a strictly positive Lebesgue integral.
The differentiability order is `∞`, denoting every finite order of
differentiability, rather than the analytic order `ω`.
-/

noncomputable section

open MeasureTheory
open scoped ContDiff

namespace BTZEntropy

/-- A fixed bump, equal to one on the closed unit ball and supported in radius two. -/
def standardBump : ContDiffBump (0 : ℝ) where
  rIn := 1
  rOut := 2
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

/-- The normalization factor is strictly positive. -/
theorem standardBump_integral_pos : 0 < ∫ x, standardBump x :=
  standardBump.integral_pos

/-- A nonnegative, compactly supported, normalized `C∞` kernel of fixed width. -/
def standardKernel : SmoothKernel where
  toFun := standardBump.normed volume
  smooth := standardBump.contDiff_normed (n := (⊤ : ℕ∞))
  nonneg := standardBump.nonneg_normed
  compactSupport := standardBump.hasCompactSupport_normed
  normalized := standardBump.integral_normed

instance : Nonempty SmoothKernel := ⟨standardKernel⟩

/-- The example has a genuine nonempty open support. -/
theorem support_standardKernel :
    Function.support standardKernel = Metric.ball (0 : ℝ) 2 :=
  standardBump.support_normed_eq

/-- Its closed support is the fixed compact interval of radius two. -/
theorem tsupport_standardKernel :
    tsupport standardKernel = Metric.closedBall (0 : ℝ) 2 :=
  standardBump.tsupport_normed_eq

end BTZEntropy
