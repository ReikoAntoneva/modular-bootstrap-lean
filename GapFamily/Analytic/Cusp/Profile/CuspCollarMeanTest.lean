import GapFamily.Analytic.Cusp.Fourier.CuspHorizontalHilbertBasic

/-!
# The literal cusp collar mean test

The inverse-square hyperbolic density is cancelled by the height-squared weight
on the finite collar. The resulting bounded measurable function defines an
actual vector in the cusp L² space above height one.
-/

noncomputable section

namespace GapFamily.Analytic

open Set MeasureTheory UpperHalfPlane

/-- The literal Riesz weight for the mean on the collar of width `ε`. -/
def cuspCollarMeanWeight (ε : ℝ) (τ : UpperHalfPlane) : ℂ :=
  {τ : UpperHalfPlane | 1 < τ.im ∧ τ.im < 1 + ε}.indicator
    (fun τ => ((ε⁻¹ * τ.im ^ 2 : ℝ) : ℂ)) τ

theorem measurableSet_cuspCollar (ε : ℝ) :
    MeasurableSet {τ : UpperHalfPlane | 1 < τ.im ∧ τ.im < 1 + ε} :=
  ((isOpen_lt continuous_const UpperHalfPlane.continuous_im).inter
    (isOpen_lt UpperHalfPlane.continuous_im continuous_const)).measurableSet

theorem measurable_cuspCollarMeanWeight (ε : ℝ) : Measurable (cuspCollarMeanWeight ε) := by
  apply Measurable.indicator _ (measurableSet_cuspCollar ε)
  exact (Complex.continuous_ofReal.comp
    (continuous_const.mul (UpperHalfPlane.continuous_im.pow 2))).measurable

theorem norm_cuspCollarMeanWeight_le (ε : ℝ) (hε : 0 < ε) (τ : UpperHalfPlane) :
    ‖cuspCollarMeanWeight ε τ‖ ≤ (1 + ε) ^ 2 / ε := by
  by_cases hτ : 1 < τ.im ∧ τ.im < 1 + ε
  · simp only [cuspCollarMeanWeight, indicator_apply, mem_ofPred_eq, hτ, and_self, ite_true,
      Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_nonneg (mul_nonneg (inv_nonneg.mpr hε.le) (sq_nonneg _))]
    calc
      ε⁻¹ * τ.im ^ 2 ≤ ε⁻¹ * (1 + ε) ^ 2 := by
        gcongr
        exact hτ.2.le
      _ = (1 + ε) ^ 2 / ε := by ring
  · simp only [cuspCollarMeanWeight, indicator_apply, mem_ofPred_eq, hτ, ite_false,
      norm_zero]
    positivity

/-- The collar test has genuine finite L² norm for the restricted modular measure. -/
theorem cuspCollarMeanWeight_memLp (ε : ℝ) (hε : 0 < ε) :
    MemLp (cuspCollarMeanWeight ε) 2
      (modularMeasure.restrict {τ : UpperHalfPlane | 1 < τ.im}) :=
  MemLp.of_bound (measurable_cuspCollarMeanWeight ε).aestronglyMeasurable
    ((1 + ε) ^ 2 / ε)
    (Filter.Eventually.of_forall (norm_cuspCollarMeanWeight_le ε hε))

/-- The collar mean Riesz test in the actual high-cusp Hilbert space. -/
def cuspCollarMeanTest (ε : ℝ) (hε : 0 < ε) : cuspHilbert 1 :=
  (cuspCollarMeanWeight_memLp ε hε).toLp (cuspCollarMeanWeight ε)

theorem cuspCollarMeanTest_ae (ε : ℝ) (hε : 0 < ε) :
    cuspCollarMeanTest ε hε =ᵐ[modularMeasure.restrict {τ : UpperHalfPlane | 1 < τ.im}]
      cuspCollarMeanWeight ε :=
  MemLp.coeFn_toLp (cuspCollarMeanWeight_memLp ε hε)

end GapFamily.Analytic
