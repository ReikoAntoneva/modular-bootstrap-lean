import GapFamily.Analytic.Bessel.BesselBasic
import Mathlib.MeasureTheory.Group.Integral

/-!
# Translation of the ordinary Bessel integral

Lebesgue translation carries `(0,∞)` exactly to `(1,∞)`. This proves both the
integral identity and the equivalence of genuine integrability, independently
of any convergence theorem for the shifted integrand.
-/

noncomputable section

namespace GapFamily.Analytic

open MeasureTheory Set

private theorem add_one_preimage_Ioi :
    (fun w : ℝ => w + 1) ⁻¹' Ioi 1 = Ioi 0 := by
  ext w
  simp

/-- The actual Bessel integral after the translation `v = w + 1`. -/
theorem besselK0_eq_shiftIntegral (t : ℝ) :
    besselK0 t = Real.exp (-t) *
      ∫ w : ℝ in Ioi 0, besselK0ShiftIntegrand t w := by
  have h := ((measurePreserving_add_right (volume : Measure ℝ) 1).restrict_preimage_emb
    (MeasurableEquiv.addRight (1 : ℝ)).measurableEmbedding (Ioi 1)).integral_comp
      (MeasurableEquiv.addRight (1 : ℝ)).measurableEmbedding (besselK0Integrand t)
  rw [add_one_preimage_Ioi] at h
  simpa only [besselK0, besselK0Integrand_add_one, integral_const_mul] using h.symm

/-- Integrability of the shifted expression is exactly integrability of the
ordinary Bessel integrand; the nonzero factor `exp(-t)` is harmless. -/
theorem integrableOn_besselK0Integrand_iff (t : ℝ) :
    IntegrableOn (besselK0Integrand t) (Ioi 1) ↔
      IntegrableOn (besselK0ShiftIntegrand t) (Ioi 0) := by
  have h := (measurePreserving_add_right (volume : Measure ℝ) 1).integrableOn_comp_preimage
    (MeasurableEquiv.addRight (1 : ℝ)).measurableEmbedding
      (f := besselK0Integrand t) (s := Ioi 1)
  rw [add_one_preimage_Ioi] at h
  rw [← h]
  simp only [Function.comp_def, besselK0Integrand_add_one, IntegrableOn]
  exact integrable_const_mul_iff (isUnit_iff_ne_zero.mpr (Real.exp_ne_zero _)) _

end GapFamily.Analytic
