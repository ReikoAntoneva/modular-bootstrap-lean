import GapFamily.Analytic.Poincare.Fourier.PoincareCorrectedSignedOutput
import GapFamily.Analytic.Poincare.Fourier.PoincareCorrectedSignedReconstruction
import GapFamily.Analytic.Poincare.Fourier.PoincareThermalOutputMeasure

/-! The ordinary Fourier coefficient of the actual corrected modular seed is
the thermal mass of its literal signed output measure. The measure retains
the original signed input, the actual ordinary response density, and the
separate threshold atom.
-/
noncomputable section
namespace GapFamily.Analytic.PoincareEnergyFourier
open Set MeasureTheory PoincareEnergyContinuation PoincareFourier

private theorem laplace_exp_ofReal (y e : ℝ) :
    Complex.exp (-2 * (Real.pi : ℂ) * (y : ℂ) * (e : ℂ)) =
      (Real.exp (-(2 * Real.pi * y) * e) : ℂ) := by
  rw [show -2 * (Real.pi : ℂ) * (y : ℂ) * (e : ℂ) =
    ((-(2 * Real.pi * y) * e : ℝ) : ℂ) by push_cast; ring,
    Complex.ofReal_exp]

private theorem scalarThresholdCoefficient_ofReal_re (J : ℤ) :
    ((PoincareScalarFourier.scalarThresholdCoefficient J).re : ℂ) =
      PoincareScalarFourier.scalarThresholdCoefficient J := by
  unfold PoincareScalarFourier.scalarThresholdCoefficient
  split_ifs <;> simp

/-- The actual corrected Fourier coefficient equals the total thermal mass
of its literal ordinary signed output measure, with no density representation
assumed for the input. -/
theorem correctedRowSeed_fourier_eq_thermalOutputMeasure
    (ν : SignedMeasure ℝ) (J j : ℤ) (B : ℝ)
    (hs : ∀ᵐ E ∂ν.variation, |(J : ℝ)| ≤ E ∧ E ≤ B)
    (y : ℝ) (hy : 0 < y) :
    (∫ x in (0 : ℝ)..1, cuspFourierMode (-j) x *
      correctedRowSeed ν J (rowPoint y hy x)) =
      (Real.sqrt y : ℂ) *
        (correctedThermalRowOutputMeasure ν J j (2 * Real.pi * y) univ : ℂ) := by
  have ht : 0 < 2 * Real.pi * y := by positivity
  have hI : (∫ᵛ E : ℝ,
      Complex.exp (-2 * (Real.pi : ℂ) * (y : ℂ) * (E : ℂ)) ∂<•ν) =
      (((∫ᵛ E : ℝ, Real.exp (-(2 * Real.pi * y) * E) ∂<•ν) : ℝ) : ℂ) := by
    simp_rw [laplace_exp_ofReal]
    exact signedIntegral_complex_ofReal (signedIntegrable_thermalInput ν J B hs ht)
  have hR (e : ℝ) : ((correctedSignedRowResponse ν J j e).re : ℂ) =
      correctedSignedRowResponse ν J j e := by
    apply Complex.ext
    · rfl
    · simpa only [Complex.ofReal_im] using (correctedSignedRowResponse_im ν J j B hs e).symm
  have hC : (∫ e : ℝ,
      Complex.exp (-2 * (Real.pi : ℂ) * (y : ℂ) * (e : ℂ)) *
        correctedSignedRowResponse ν J j e ∂referenceMeasure j) =
      (((∫ e : ℝ, Real.exp (-(2 * Real.pi * y) * e) *
        (correctedSignedRowResponse ν J j e).re ∂referenceMeasure j) : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    apply integral_congr_ae
    filter_upwards with e
    rw [Complex.ofReal_mul, hR, laplace_exp_ofReal]
  rw [correctedRowSeed_fourier_eq_full_laplace ν J j B hs y hy,
    correctedThermalRowOutputMeasure_univ ν J j B hs ht, hI, hC]
  by_cases hj : j = J <;> by_cases h0 : j = 0 <;>
    subst_vars <;>
    simp_all only [ite_true, ite_false, Complex.ofReal_add, Complex.ofReal_mul,
      Complex.ofReal_zero, scalarThresholdCoefficient_ofReal_re] <;> ring

/-- The actual finite corrected modular seed has exactly the thermal signed
output obtained by adding the original input rows and their ordinary responses. -/
theorem correctedSeedSuperposition_fourier_eq_thermalOutputMeasure
    (S : Finset ℤ) (ν : ℤ → SignedMeasure ℝ) (j : ℤ) (B : ℝ)
    (hs : ∀ J ∈ S, ∀ᵐ E ∂(ν J).variation, |(J : ℝ)| ≤ E ∧ E ≤ B)
    (y : ℝ) (hy : 0 < y) :
    (∫ x in (0 : ℝ)..1, cuspFourierMode (-j) x *
      correctedSeedSuperposition S ν (rowPoint y hy x)) =
      (Real.sqrt y : ℂ) *
        (correctedThermalFiniteOutputMeasure S ν j (2 * Real.pi * y) univ : ℂ) := by
  simp only [correctedSeedSuperposition, Finset.mul_sum]
  rw [intervalIntegral.integral_finsetSum
    (fun J hJ => intervalIntegrable_correctedRowSeed_fourier y hy (ν J) j J B (hs J hJ)),
    correctedThermalFiniteOutputMeasure_apply, Complex.ofReal_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun J hJ =>
    correctedRowSeed_fourier_eq_thermalOutputMeasure (ν J) J j B (hs J hJ) y hy

/-- The complete literal finite thermal output reconstructs the actual modular
seed at every point. Both the input and the threshold atom remain signed measures. -/
theorem hasSum_correctedSeedSuperposition_thermalOutputMeasure
    (S : Finset ℤ) (ν : ℤ → SignedMeasure ℝ) (B : ℝ)
    (hs : ∀ J ∈ S, ∀ᵐ E ∂(ν J).variation, |(J : ℝ)| ≤ E ∧ E ≤ B)
    (y : ℝ) (hy : 0 < y) (x : ℝ) :
    HasSum (fun j : ℤ => (Real.sqrt y : ℂ) *
      (correctedThermalFiniteOutputMeasure S ν j (2 * Real.pi * y) univ : ℂ) *
        cuspFourierMode j x)
      (correctedSeedSuperposition S ν (rowPoint y hy x)) := by
  apply (hasSum_correctedSeedSuperposition_row y hy S ν B hs x).congr_fun
  intro j
  unfold correctedFiniteFourierCoefficient
  rw [correctedSeedSuperposition_fourier_eq_thermalOutputMeasure S ν j B hs y hy]

/-- The corrected ordinary finite signed superposition has exactly the output
`σ + (Rσ)dω + threshold atom`, with rank constant `12 m_g / sqrt 2`.
The thermal signed measures are finite and the complete spin series converges. -/
theorem hasSum_finiteSeedSuperposition_add_scalarMoment_output
    (S : Finset ℤ) (ν : ℤ → SignedMeasure ℝ) (B : ℝ)
    (hs : ∀ J ∈ S, ∀ᵐ E ∂(ν J).variation, |(J : ℝ)| ≤ E ∧ E ≤ B)
    (y : ℝ) (hy : 0 < y) (x : ℝ) :
    HasSum (fun j : ℤ => (Real.sqrt y : ℂ) *
      (correctedThermalFiniteOutputMeasure S ν j (2 * Real.pi * y) univ : ℂ) *
        cuspFourierMode j x)
      (finiteSeedSuperposition S ν (rowPoint y hy x) +
        ((12 * scalarSignedSqrtMoment S ν / Real.sqrt 2 : ℝ) : ℂ)) := by
  simpa only [correctedSeedSuperposition_eq_add_scalarMoment S ν B hs] using
    hasSum_correctedSeedSuperposition_thermalOutputMeasure S ν B hs y hy x

end GapFamily.Analytic.PoincareEnergyFourier
