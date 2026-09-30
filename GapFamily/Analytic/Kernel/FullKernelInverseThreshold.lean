import GapFamily.Analytic.Kernel.LowBandThresholdFunctional
import GapFamily.Analytic.Kernel.FullKernelInverseSmoothing

/-! The inverse threshold mass is expressed using only bounded ordinary-L1
mass and smoothing maps. This formula is suitable for holomorphic input
columns without declaring mass continuous on the scalar Hilbert row. -/

noncomputable section

open MeasureTheory Set
open scoped BigOperators

namespace GapFamily.Analytic

open PoincareScalarFourier

def correctedInverseThresholdExpression {ι : Type*} [Fintype ι]
    (J : ι → ℤ) (B : ℝ) (hB : 0 ≤ B)
    (f : LowBandHilbert J B) (g : CorrectedKernelSmoothingSpace J B) : ℂ :=
  lowBandThresholdFunctional J B g - correctedSmoothingThresholdFunctional J B hB
    (Ring.inverse (correctedLowBandIdentityPlus J B) f)

/-- The bounded expression equals the actual ordinary weighted mass of the
inverse whenever the L1 and Hilbert input represent the same function. -/
theorem correctedInverseThresholdExpression_eq_integral
    {ι : Type*} [Fintype ι] (J : ι → ℤ) (B : ℝ) (hB : 0 ≤ B)
    (hunit : IsUnit (correctedLowBandIdentityPlus J B))
    (f : LowBandHilbert J B) (g : CorrectedKernelSmoothingSpace J B)
    (hfg : ∀ i, ⇑(f i) =ᵐ[(referenceMeasure (J i)).restrict (Ioo |(J i : ℝ)| B)] ⇑(g i)) :
    correctedInverseThresholdExpression J B hB f g =
      ∑ i, scalarThresholdCoefficient (J i) * ∫ e,
        Ring.inverse (correctedLowBandIdentityPlus J B) f i e
        ∂(referenceMeasure (J i)).restrict (Ioo |(J i : ℝ)| B) := by
  rw [correctedInverseThresholdExpression, lowBandThresholdFunctional_apply,
    correctedSmoothingThresholdFunctional_apply, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← mul_sub, ← integral_sub (L1.integrable_coeFn (g i))
    (correctedKernelResponse_integrable_lowBand J B hB _ (J i))]
  congr 1
  apply integral_congr_ae
  filter_upwards [hfg i, correctedLowBandInverse_coeFn_eq_sub J B hunit f i,
    correctedLowBandOperator_coeFn J B hB
      (Ring.inverse (correctedLowBandIdentityPlus J B) f) i] with e hfg hu hr
  rw [hu, hfg, hr]

/-- Holomorphic input columns give a holomorphic actual inverse mass by this
bounded formula; the ordinary representative equality is a separate theorem. -/
theorem differentiable_correctedInverseThresholdExpression
    {ι : Type*} [Fintype ι] (J : ι → ℤ) (B : ℝ) (hB : 0 ≤ B)
    (f : ℂ → LowBandHilbert J B) (g : ℂ → CorrectedKernelSmoothingSpace J B)
    (hf : Differentiable ℂ f) (hg : Differentiable ℂ g) :
    Differentiable ℂ (fun z => correctedInverseThresholdExpression J B hB (f z) (g z)) :=
  ((lowBandThresholdFunctional J B).differentiable.comp hg).sub
    ((correctedSmoothingThresholdFunctional J B hB).differentiable.comp
      ((Ring.inverse (correctedLowBandIdentityPlus J B)).differentiable.comp hf))

end GapFamily.Analytic
