import GapFamily.Analytic.Cusp.Scalar.CuspConstantPairingFunctional
import GapFamily.Analytic.Cusp.Scalar.CuspConstantResponseReciprocity
import GapFamily.Analytic.Cusp.Scalar.CuspConstantCoefficientPairing

noncomputable section
open Filter Set MeasureTheory
open scoped Topology
namespace GapFamily.Analytic

/-- On the physical half-plane the analytic scalar functional is the constant
observation of the actual W-valued pencil solution for every height-supported source. -/
theorem cuspScalarPencilSolution_constant_pairing_eq_functional
    {T : ℝ} (hT : 0 ≤ T) {κ : ℂ} (hκ : 0 < κ.re)
    (F : ModularHilbert) (hF : modularHighCut (Real.exp T) F = 0) :
    inner ℂ modularConstant
      (scalarCuspEmbedding (cuspScalarPencilSolution (1 / 4 - κ ^ 2) F)) =
      cuspConstantPairingFunctional T κ F := by
  rw [cuspScalarPencilSolution_constant_reciprocity hκ F]
  exact (cuspConstantScalarForm_coefficient_pairing hT hκ F hF).trans
    (cuspConstantPairingFunctional_apply T κ F).symm

/-- The physical constant observation is exactly an ordinary convergent integral
against the nonconjugated logarithmic profile. -/
theorem cuspScalarPencilSolution_constant_pairing_integral
    {T : ℝ} (hT : 0 ≤ T) {κ : ℂ} (hκ : 0 < κ.re)
    (F : ModularHilbert) (hF : modularHighCut (Real.exp T) F = 0) :
    inner ℂ modularConstant
      (scalarCuspEmbedding (cuspScalarPencilSolution (1 / 4 - κ ^ 2) F)) =
      ∫ t : CuspGreenCollar 0 T,
        cuspConstantLogResponse κ t * cuspGreenSourceCoefficient T F t
          ∂cuspGreenCollarMeasure 0 T :=
  (cuspScalarPencilSolution_constant_pairing_eq_functional hT hκ F hF).trans
    (cuspConstantPairingFunctional_apply T κ F)

/-- The physical scalar observation has the continued threshold value, without
asserting a global W-valued solution at threshold. -/
theorem cuspScalarPencilSolution_constant_pairing_tendsto_zero
    {T : ℝ} (hT : 0 ≤ T) (F : ModularHilbert)
    (hF : modularHighCut (Real.exp T) F = 0) :
    Tendsto (fun κ : ℂ => inner ℂ modularConstant
      (scalarCuspEmbedding (cuspScalarPencilSolution (1 / 4 - κ ^ 2) F)))
      (𝓝[{κ : ℂ | 0 < κ.re}] (0 : ℂ))
      (𝓝 (cuspConstantPairingFunctional T 0 F)) := by
  have hc : Tendsto (fun κ : ℂ => cuspConstantPairingFunctional T κ F)
      (𝓝 (0 : ℂ)) (𝓝 (cuspConstantPairingFunctional T 0 F)) :=
    (ContinuousLinearMap.apply ℂ ℂ F).continuous.continuousAt.tendsto.comp
      (cuspConstantPairingFunctional_tendsto_zero T)
  apply (hc.mono_left nhdsWithin_le_nhds).congr'
  filter_upwards [self_mem_nhdsWithin] with κ hκ
  exact (cuspScalarPencilSolution_constant_pairing_eq_functional hT hκ F hF).symm

end GapFamily.Analytic
