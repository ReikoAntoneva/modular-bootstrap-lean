import GapFamily.Analytic.Cusp.Schur.CuspLocalSchurBasic
import GapFamily.Analytic.Cusp.Schur.CuspLocalSchurExpansion

/-!
# Physical identification of the finite-height Schur continuation

Each local ingredient is identified with its actual physical response. The
result is an equality of bounded finite-height compressions of the literal
Schur family, including its algebraic totalization at singular parameters.
-/

noncomputable section
namespace GapFamily.Analytic.CuspSchurLocal
open ModularGradient

/-- The local zero-trace term is the sum of the two actual compressed responses. -/
theorem localZeroTrace_eq_physical {L T : ℝ} (hL : 0 ≤ L) (hT : 0 ≤ T)
    {κ : ℂ} (hκ : 0 < κ.re) (f : ModularHilbert) :
    localZeroTrace L T κ f = modularLowCut (Real.exp L)
      (meanZeroCuspEmbedding (cuspMeanZeroPencilSolution (parameter κ)
          (modularLowCut (Real.exp T) f)) +
        scalarCuspEmbedding (cuspScalarPencilSolution (parameter κ)
          (modularLowCut (Real.exp T) f))) := by
  rw [localZeroTrace, cuspGreenLocalizedOutput_eq_physical hL hT hκ]
  simp only [add_apply, ContinuousLinearMap.comp_apply, map_add,
    constrainedResponse, parameter]

/-- The actual constant pairing of the scalar response supplies the local numerator. -/
theorem localNumerator_eq_physical {T : ℝ} (hT : 0 ≤ T) {κ : ℂ}
    (hκ : 0 < κ.re) (f : ModularHilbert) :
    localNumerator T κ f =
      inner ℂ modularConstant (modularLowCut (Real.exp T) f) + parameter κ *
        (inner ℂ modularConstant (meanZeroCuspEmbedding
          (cuspMeanZeroPencilSolution (parameter κ) (modularLowCut (Real.exp T) f))) +
        inner ℂ modularConstant (scalarCuspEmbedding
          (cuspScalarPencilSolution (parameter κ) (modularLowCut (Real.exp T) f)))) := by
  have hp := cuspScalarPencilSolution_constant_pairing_eq_functional hT hκ
    (modularLowCut (Real.exp T) f) (modularHighCut_lowCut (Real.exp T) f)
  change inner ℂ modularConstant (modularLowCut (Real.exp T) f) + parameter κ *
      (inner ℂ modularConstant (meanZeroCuspEmbedding
        (cuspMeanZeroPencilSolution (parameter κ) (modularLowCut (Real.exp T) f))) +
        cuspConstantPairingFunctional T κ (modularLowCut (Real.exp T) f)) = _
  rw [← hp]
  rfl

/-- The actual local constant response supplies the finite-height correction vector. -/
theorem localTraceVector_eq_physical {L : ℝ} (hL : 0 ≤ L) {κ : ℂ}
    (hκ : 0 < κ.re) :
    localTraceVector L κ = modularLowCut (Real.exp L)
      (modularConstant + parameter κ •
        (meanZeroCuspEmbedding (cuspMeanZeroPencilSolution (parameter κ) modularConstant) +
          scalarCuspEmbedding (cuspScalarPencilSolution (parameter κ) modularConstant))) := by
  rw [localTraceVector, cuspConstantLocalResponse_eq_lowCut hL hκ, map_add, map_smul, map_add]
  rfl

/-- On the physical half-plane the local operator is exactly the actual finite-height
Schur compression. This is an identity of the literal totalized families; it does
not assert an inverse at a singular parameter. -/
theorem continuedLocalSchur_eq_physical {L T : ℝ} (hL : 0 ≤ L) (hT : 0 ≤ T)
    {κ : ℂ} (hκ : 0 < κ.re) :
    continuedLocalSchur L T κ =
      ((modularLowCut (Real.exp L)).comp
        (CuspSchur.actualSchurResolvent (parameter κ))).comp
          (modularLowCut (Real.exp T)) := by
  have hd : CuspSchur.actualSchurDenominator (parameter κ) =
      CuspSchur.continuedDenominator κ := CuspSchur.actualSchurDenominator_eq_continued hκ
  apply ContinuousLinearMap.ext
  intro f
  change localZeroTrace L T κ f +
      ((CuspSchur.continuedDenominator κ)⁻¹ * localNumerator T κ f) • localTraceVector L κ =
    modularLowCut (Real.exp L)
      (CuspSchur.actualSchurResolvent (parameter κ) (modularLowCut (Real.exp T) f))
  conv_rhs =>
    rw [actualSchurResolvent_expansion (parameter κ) (modularLowCut (Real.exp T) f)]
    rw [(modularLowCut (Real.exp L)).map_add, (modularLowCut (Real.exp L)).map_smul]
  rw [localZeroTrace_eq_physical (L := L) (T := T) (κ := κ) hL hT hκ f]
  rw [localNumerator_eq_physical (T := T) (κ := κ) hT hκ f]
  conv_lhs =>
    arg 2
    arg 2
    rw [localTraceVector_eq_physical (L := L) (κ := κ) hL hκ]
  conv_rhs =>
    arg 2
    arg 1
    arg 2
    rw [hd]
  simp only [div_eq_mul_inv, mul_comm]

end GapFamily.Analytic.CuspSchurLocal
