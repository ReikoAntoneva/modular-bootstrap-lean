import GapFamily.Analytic.Cusp.Schur.CuspSchurPhysical
import GapFamily.Analytic.Cusp.Scalar.CuspConstantResponsePencil

/-!
# A scalar continued Schur denominator

The actual W constant pairing is rational on the physical half-plane. After
cancellation against the squared spectral parameter its contribution is a
polynomial. The resulting scalar expression makes sense at threshold without
an assertion of a W-valued inverse there. Quarter-response positivity remains
an explicit premise of the threshold nonvanishing statement.
-/

noncomputable section
namespace GapFamily.Analytic.CuspSchur
open ModularGradient
open scoped ComplexOrder

/-- Scalar continuation after cancelling the explicit W constant pairing.
The actual constrained response is retained; no scalar form vector is continued. -/
def continuedDenominator (κ : ℂ) : ℂ :=
  -((1 / 4 : ℂ) - κ ^ 2) * ((Real.pi / 3 : ℝ) : ℂ) -
    ((1 / 4 : ℂ) - κ ^ 2) ^ 2 * inner ℂ modularConstant
      (meanZeroCuspEmbedding (cuspMeanZeroPencilSolution ((1 / 4 : ℂ) - κ ^ 2)
        modularConstant)) - (κ - (1 / 2 : ℂ)) ^ 2

/-- Agreement uses the actual physical scalar response pairing. This scalar
identity itself does not require invertibility of the constrained pencil. -/
theorem actualSchurDenominator_eq_continued {κ : ℂ} (hκ : 0 < κ.re) :
    actualSchurDenominator ((1 / 4 : ℂ) - κ ^ 2) = continuedDenominator κ := by
  have hk : κ + (1 / 2 : ℂ) ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    norm_num at hr
    linarith
  have hw := cuspScalarPencilSolution_constant_pairing hκ
  change inner ℂ modularConstant (formEmbedding
    (cuspScalarPencilSolution ((1 / 4 : ℂ) - κ ^ 2) modularConstant : FormDomain)) = _ at hw
  have hc : ((1 / 4 : ℂ) - κ ^ 2) ^ 2 * (1 / (κ + 1 / 2) ^ 2) =
      (κ - 1 / 2) ^ 2 := by
    rw [show (1 / 4 : ℂ) - κ ^ 2 = (1 / 2 - κ) * (κ + 1 / 2) by ring,
      mul_pow, mul_assoc, mul_one_div_cancel (pow_ne_zero 2 hk), mul_one]
    ring
  rw [actualSchurDenominator, schurDenominator_normalization,
    zeroTraceResponse_apply, map_add, inner_add_right, hw, mul_add, hc]
  simp only [continuedDenominator, meanZeroCuspEmbedding_apply]
  ring

/-- The exact scalar threshold value; no evaluation of the totalized W inverse occurs. -/
theorem continuedDenominator_zero :
    continuedDenominator 0 = -((Real.pi / 12 : ℝ) : ℂ) -
      (1 / 16 : ℂ) * inner ℂ modularConstant
        (meanZeroCuspEmbedding (cuspMeanZeroPencilSolution (1 / 4) modularConstant)) - 1 / 4 := by
  norm_num [continuedDenominator]
  ring

/-- Positivity of the actual constrained quarter pairing gives a strict negative scalar value. -/
theorem continuedDenominator_zero_re_neg
    (hV : 0 ≤ inner ℂ modularConstant
      (meanZeroCuspEmbedding (cuspMeanZeroPencilSolution (1 / 4) modularConstant))) :
    (continuedDenominator 0).re < 0 := by
  have hVr := (Complex.nonneg_iff.mp hV).1
  rw [continuedDenominator_zero]
  norm_num [Complex.sub_re, Complex.neg_re, Complex.mul_re]
  nlinarith [Real.pi_pos]

/-- Threshold nonvanishing is conditional only on the displayed actual V pairing. -/
theorem continuedDenominator_zero_ne_zero
    (hV : 0 ≤ inner ℂ modularConstant
      (meanZeroCuspEmbedding (cuspMeanZeroPencilSolution (1 / 4) modularConstant))) :
    continuedDenominator 0 ≠ 0 := by
  intro h
  have hn := continuedDenominator_zero_re_neg hV
  rw [h, Complex.zero_re] at hn
  exact lt_irrefl 0 hn

end GapFamily.Analytic.CuspSchur
