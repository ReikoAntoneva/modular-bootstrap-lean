import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

/-! The continuous fundamental lemma on an arbitrary open subset of the complex plane. -/
noncomputable section
namespace GapFamily.Analytic.PoincareWeak

open Set MeasureTheory
open scoped ContDiff

/-- A continuous complex residual vanishes pointwise on an open set if its ordinary
integral against every real smooth compact test supported there vanishes. -/
theorem eqOn_zero_of_continuousOn_integral_contDiff_smul_eq_zero
    {U : Set ℂ} {f : ℂ → ℂ} (hU : IsOpen U) (hf : ContinuousOn f U)
    (h : ∀ g : ℂ → ℝ, ContDiff ℝ ∞ g → HasCompactSupport g → tsupport g ⊆ U →
      (∫ z : ℂ, g z • f z ∂volume) = 0) : EqOn f 0 U := by
  have hae : ∀ᵐ z ∂(volume : Measure ℂ), z ∈ U → f z = 0 :=
    hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      (hf.locallyIntegrableOn hU.measurableSet) h
  have hrestrict : f =ᵐ[(volume : Measure ℂ).restrict U] (0 : ℂ → ℂ) :=
    (ae_restrict_iff' hU.measurableSet).mpr hae
  exact Measure.eqOn_open_of_ae_eq hrestrict hU hf continuousOn_const

end GapFamily.Analytic.PoincareWeak
