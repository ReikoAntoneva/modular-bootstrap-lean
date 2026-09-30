import GapFamily.Analytic.Cusp.Scalar.CuspScalarFormProjection

/-!
# Literal core representative of the actual scalar cusp projection

The actual projection restricts the modular value, applies the genuine ordinary
horizontal average, and extends it by zero below height one.
-/

noncomputable section

namespace GapFamily.Analytic

open Set MeasureTheory UpperHalfPlane ModularGradient

/-- The actual ambient scalar projection of a genuine smooth core value. -/
theorem cuspScalarProjection_value_ae (F : smoothCore) :
    cuspScalarProjection (value F) =ᵐ[modularMeasure]
      fun τ : UpperHalfPlane => if 1 < τ.im then cuspHorizontalAverage F.val τ.im else 0 := by
  have ha := cuspAverage_core_ae 1 le_rfl F
  change cuspAverage 1 le_rfl (cuspRestrict 1 (value F))
    =ᵐ[modularMeasure.restrict {τ : UpperHalfPlane | 1 < τ.im}]
      (fun τ : UpperHalfPlane => cuspHorizontalAverage F.val τ.im) at ha
  have hi := (ae_eq_restrict_iff_indicator_ae_eq (measurableSet_highCusp 1)).mp ha
  rw [cuspScalarProjection_apply]
  filter_upwards [cuspZeroExtend_ae 1 (cuspAverage 1 le_rfl (cuspRestrict 1 (value F))), hi]
    with τ hz hτ
  rw [hz, hτ]
  by_cases hh : 1 < τ.im <;> simp [hh]

end GapFamily.Analytic
