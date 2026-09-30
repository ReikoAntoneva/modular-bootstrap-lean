import GapFamily.Construction.FiniteRepairState

/-! Thermal integrability supplies ordinary numerator integrability on every
bounded energy interval, including intervals meeting a physical threshold.
-/

namespace GapFamily.Construction.FiniteRepairState

open Set MeasureTheory Analytic

/-- On a finite energy interval the reciprocal thermal weight is bounded,
so a thermally integrable state has an ordinarily integrable numerator. -/
theorem integrableOn_numerator (s : FiniteRepairState) (hi : s.ThermalIntegrable)
    (j : ℤ) (L V : ℝ) :
    IntegrableOn (s.numerator j) (Ioo L V) (referenceMeasure j) := by
  have ht : Integrable (fun E => Real.exp (-E) * s.numerator j E)
      (referenceMeasure j) := by
    simpa only [neg_one_mul] using hi j 1 zero_lt_one
  have hb : ∀ᵐ E ∂(referenceMeasure j).restrict (Ioo L V),
      ‖Real.exp E‖ ≤ Real.exp V := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with E hE
    rw [Real.norm_of_nonneg (Real.exp_pos E).le]
    exact Real.exp_le_exp.mpr hE.2.le
  have hp : Integrable (fun E => Real.exp E * (Real.exp (-E) * s.numerator j E))
      ((referenceMeasure j).restrict (Ioo L V)) :=
    ht.restrict.bdd_mul (by fun_prop) hb
  exact hp.congr (Filter.Eventually.of_forall fun E => by
    dsimp only
    rw [← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul])

end GapFamily.Construction.FiniteRepairState
