import GapFamily.Analytic.Kernel.FullKernelSmoothingSeed
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! Continuity of the actual signed response at every real output energy.
Compact physical input support passes to both Jordan measures, where ordinary
parametric integration of the jointly continuous kernel applies. -/

noncomputable section

open MeasureTheory Set
open scoped BigOperators

namespace GapFamily.Analytic

private theorem continuous_correctedKernel_measureIntegral
    (μ : Measure ℝ) [IsFiniteMeasure μ] (J j : ℤ) (M : ℝ)
    (hs : ∀ᵐ E ∂μ, |(J : ℝ)| ≤ E ∧ E ≤ M) :
    Continuous (fun e : ℝ => ∫ E, correctedKernel j J e E ∂μ) := by
  have hr : μ.restrict (Icc |(J : ℝ)| M) = μ :=
    Measure.restrict_eq_self_of_ae_mem hs
  have hc : Continuous (fun e : ℝ => ∫ E in Icc |(J : ℝ)| M,
      correctedKernel j J e E ∂μ) :=
    continuous_parametric_integral_of_continuous
      (f := fun e E => correctedKernel j J e E) (continuous_correctedKernel j J) isCompact_Icc
  simpa only [hr] using hc

/-- A compactly supported physical signed row has a continuous actual response
on the whole real output axis. -/
theorem continuous_correctedSignedRowResponse (ν : SignedMeasure ℝ) (J j : ℤ)
    (M : ℝ) (hs : ∀ᵐ E ∂ν.variation, |(J : ℝ)| ≤ E ∧ E ≤ M) :
    Continuous (correctedSignedRowResponse ν J j) := by
  have hparts := hs
  rw [← SignedMeasure.totalVariation_eq_variation, SignedMeasure.totalVariation,
    ae_add_measure_iff] at hparts
  have heq : correctedSignedRowResponse ν J j = fun e =>
      (∫ E, correctedKernel j J e E ∂ν.toJordanDecomposition.posPart) -
        ∫ E, correctedKernel j J e E ∂ν.toJordanDecomposition.negPart := by
    funext e
    exact signedIntegral_eq_jordan (correctedSignedRowResponse_integrable ν J j M hs e)
  rw [heq]
  exact (continuous_correctedKernel_measureIntegral ν.toJordanDecomposition.posPart J j M
    hparts.1).sub
      (continuous_correctedKernel_measureIntegral ν.toJordanDecomposition.negPart J j M hparts.2)

/-- Ordinary finite signed superposition preserves actual response continuity. -/
theorem continuous_correctedSignedResponse {ι : Type*} [Fintype ι]
    (ν : ι → SignedMeasure ℝ) (J : ι → ℤ) (j : ℤ) (M : ℝ)
    (hs : ∀ i, ∀ᵐ E ∂(ν i).variation, |(J i : ℝ)| ≤ E ∧ E ≤ M) :
    Continuous (correctedSignedResponse ν J j) :=
  continuous_finsetSum Finset.univ fun i _ =>
    continuous_correctedSignedRowResponse (ν i) (J i) j M (hs i)

/-- The same continuity statement for an explicit finite input set. -/
theorem continuous_sum_correctedSignedRowResponse {ι : Type*} (s : Finset ι)
    (ν : ι → SignedMeasure ℝ) (J : ι → ℤ) (j : ℤ) (M : ℝ)
    (hs : ∀ i ∈ s, ∀ᵐ E ∂(ν i).variation, |(J i : ℝ)| ≤ E ∧ E ≤ M) :
    Continuous (fun e : ℝ => ∑ i ∈ s, correctedSignedRowResponse (ν i) (J i) j e) :=
  continuous_finsetSum s fun i hi =>
    continuous_correctedSignedRowResponse (ν i) (J i) j M (hs i hi)

end GapFamily.Analytic
