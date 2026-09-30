import GapFamily.Analytic.Cusp.Green.CuspGreenTailObserved
import GapFamily.Analytic.Cusp.Green.CuspGreenTailFramePrimitive
import GapFamily.Analytic.Cusp.Profile.CuspCollarPrimitiveInterval

/-!
# The observed tail vector in the actual collar primitive

The bounded primitive applied to the `Lp` realization of the continuous
tail vector is its ordinary finite-interval integral. The hyperbolic-cosine
identity includes the removable parameter zero.
-/

noncomputable section

namespace GapFamily.Analytic

open Set MeasureTheory

/-- The actual measured-collar primitive evaluates the ordinary integral of the tail vector. -/
theorem cuspCollarPrimitive_cuspGreenTailObserved_integral (L : ℝ) (κ : ℂ)
    (t : CuspGreenCollar 0 L) :
    cuspCollarPrimitive L L
      (ContinuousMap.toLp 2 (cuspGreenCollarMeasure 0 L) ℂ (cuspGreenTailObserved L κ)) t =
      ∫ v : ℝ in (0 : ℝ)..(t : ℝ), cuspGreenTailValue v κ :=
  cuspCollarPrimitive_toLp_eq_intervalIntegral L (cuspGreenTailObserved L κ)
    (fun v => cuspGreenTailValue v κ) (cuspGreenTailObserved_apply L κ) t

/-- The ordinary open-closed integral has the same actual `Lp` primitive value. -/
theorem cuspCollarPrimitive_cuspGreenTailObserved_integral_Ioc (L : ℝ) (κ : ℂ)
    (t : CuspGreenCollar 0 L) :
    cuspCollarPrimitive L L
      (ContinuousMap.toLp 2 (cuspGreenCollarMeasure 0 L) ℂ (cuspGreenTailObserved L κ)) t =
      ∫ v : ℝ in Ioc 0 (t : ℝ), cuspGreenTailValue v κ := by
  rw [cuspCollarPrimitive_cuspGreenTailObserved_integral,
    intervalIntegral.integral_of_le t.property.1]

/-- The tail primitive reconstructs the cosine frame at every spectral parameter. -/
theorem cuspCollarPrimitive_cuspGreenTailObserved_eq_cosh (L : ℝ) (κ : ℂ)
    (t : CuspGreenCollar 0 L) :
    1 + κ ^ 2 * cuspCollarPrimitive L L
      (ContinuousMap.toLp 2 (cuspGreenCollarMeasure 0 L) ℂ (cuspGreenTailObserved L κ)) t =
      Complex.cosh (κ * (t : ℝ)) := by
  rw [cuspCollarPrimitive_cuspGreenTailObserved_integral]
  exact cuspGreenTailValue_integral_eq_cosh t κ

end GapFamily.Analytic
