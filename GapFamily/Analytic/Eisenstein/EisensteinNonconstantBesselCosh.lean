import GapFamily.Analytic.Bessel.Bessel
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-!
# Hyperbolic-cosine representation of the order-zero Bessel integral

The actual defining integral over `(1,∞)` is transported along `cosh`.
The integrability statement records ordinary convergence for positive argument.
-/

noncomputable section

namespace GapFamily.Analytic

open MeasureTheory Set

private theorem cosh_image_Ioi_zero : Real.cosh '' Ioi 0 = Ioi 1 := by
  ext x
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact Real.one_lt_cosh.mpr (ne_of_gt hu)
  · intro hx
    exact ⟨Real.arcosh x, Real.arcosh_pos hx, Real.cosh_arcosh (le_of_lt hx)⟩

private theorem cosh_besselK0Integrand (t : ℝ) {u : ℝ} (hu : 0 < u) :
    |Real.sinh u| • besselK0Integrand t (Real.cosh u) =
      Real.exp (-t * Real.cosh u) := by
  have hs : 0 < Real.sinh u := Real.sinh_pos_iff.mpr hu
  rw [smul_eq_mul, besselK0Integrand, ← Real.sinh_sq, Real.sqrt_sq_eq_abs,
    abs_of_pos hs]
  field_simp

/-- The defining Bessel integral equals its hyperbolic-cosine representation. -/
theorem besselK0_eq_coshIntegral (t : ℝ) :
    besselK0 t = ∫ u : ℝ in Ioi 0, Real.exp (-t * Real.cosh u) := by
  unfold besselK0
  rw [← cosh_image_Ioi_zero]
  rw [integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
    (fun u _ => (Real.hasDerivAt_cosh u).hasDerivWithinAt)
    (Real.cosh_injOn.mono Ioi_subset_Ici_self)]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro u hu
  exact cosh_besselK0Integrand t hu

/-- The hyperbolic-cosine Bessel integral ordinarily converges at every positive argument. -/
theorem besselK0_coshIntegrable {t : ℝ} (ht : 0 < t) :
    IntegrableOn (fun u : ℝ => Real.exp (-t * Real.cosh u)) (Ioi 0) := by
  have hi := besselK0_integrable ht
  rw [← cosh_image_Ioi_zero,
    integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi
      (fun u _ => (Real.hasDerivAt_cosh u).hasDerivWithinAt)
      (Real.cosh_injOn.mono Ioi_subset_Ici_self)] at hi
  exact hi.congr_fun (fun u hu => cosh_besselK0Integrand t hu) measurableSet_Ioi

end GapFamily.Analytic
