import GapFamily.Analytic.Cusp.MeanZero.CuspMeanZeroForm

/-!
# The constant channel and horizontal cusp averaging

The bounded horizontal averaging map fixes the actual restricted constant
channel. Positive high-cusp measure ensures that this fixed vector is nonzero.
-/

noncomputable section

namespace GapFamily.Analytic

open MeasureTheory Set UpperHalfPlane ModularGradient

/-- The ordinary horizontal integral has unit length and fixes constants. -/
theorem cuspHorizontalAverage_const (c : ℂ) (y : ℝ) :
    cuspHorizontalAverage (fun _ => c) y = c := by
  norm_num [cuspHorizontalAverage, cuspHorizontalSlice, intervalIntegral.integral_const]

/-- Horizontal averaging fixes the actual constant modular Hilbert vector. -/
theorem cuspAverage_modularConstant (H : ℝ) (hH : 1 ≤ H) :
    cuspAverage H hH (cuspRestrict H modularConstant) = cuspRestrict H modularConstant := by
  change cuspAverage H hH (cuspCoreValue H (constantCore 1)) = cuspCoreValue H (constantCore 1)
  rw [cuspAverage_core]
  apply Lp.ext
  filter_upwards [cuspCoreAverage_ae H hH (constantCore 1),
    cuspCoreValue_ae H (constantCore 1)] with τ ha hv
  rw [ha, hv]
  exact cuspHorizontalAverage_const 1 τ.im

/-- An explicit strip above `H + 1` has positive hyperbolic measure and is
contained in the actual modular high cusp. -/
theorem modularMeasure_highCusp_pos (H : ℝ) (hH : 1 ≤ H) :
    0 < modularMeasure {τ : UpperHalfPlane | H < τ.im} := by
  have hpos : 0 < H + 1 := by linarith
  have hsub : cuspStrip (H + 1) ⊆
      {τ : UpperHalfPlane | H < τ.im} ∩ ModularGroup.fd := by
    intro τ hτ
    change |τ.re| ≤ (1 : ℝ) / 2 ∧ H + 1 ≤ τ.im at hτ
    refine ⟨by dsimp; linarith [hτ.2], ?_⟩
    change 1 ≤ Complex.normSq (τ : ℂ) ∧ |τ.re| ≤ (1 : ℝ) / 2
    refine ⟨?_, hτ.1⟩
    change 1 ≤ τ.re * τ.re + τ.im * τ.im
    nlinarith [sq_nonneg τ.re, hτ.2]
  rw [modularMeasure, Measure.restrict_apply (measurableSet_highCusp H)]
  have hp : 0 < (volume : Measure UpperHalfPlane) (cuspStrip (H + 1)) := by
    rw [volume_cuspStrip _ hpos]
    exact ENNReal.ofReal_pos.mpr (one_div_pos.mpr hpos)
  exact hp.trans_le (measure_mono hsub)

/-- Restricting the actual constant channel to a positive-measure high cusp
does not produce the zero Hilbert vector. -/
theorem cuspRestrict_modularConstant_ne_zero_of_one_le (H : ℝ) (hH : 1 ≤ H) :
    cuspRestrict H modularConstant ≠ 0 := by
  intro hzero
  have hrep := (cuspRestrict_ae H modularConstant).trans
    (ae_restrict_of_ae modularConstant_ae)
  rw [hzero] at hrep
  have hfalse : ∀ᵐ τ ∂modularMeasure.restrict {τ : UpperHalfPlane | H < τ.im}, False := by
    filter_upwards [hrep,
      Lp.coeFn_zero (E := ℂ) (p := 2)
        (μ := modularMeasure.restrict {τ : UpperHalfPlane | H < τ.im})] with τ hτ hz
    exact zero_ne_one (hz.symm.trans hτ)
  have hmass : modularMeasure {τ : UpperHalfPlane | H < τ.im} = 0 := by
    simpa only [ae_iff, not_false_eq_true, Set.ofPred_true,
      Measure.restrict_apply_univ] using hfalse
  exact (modularMeasure_highCusp_pos H hH).ne' hmass

theorem cuspRestrict_modularConstant_ne_zero :
    cuspRestrict 1 modularConstant ≠ 0 :=
  cuspRestrict_modularConstant_ne_zero_of_one_le 1 le_rfl

end GapFamily.Analytic
