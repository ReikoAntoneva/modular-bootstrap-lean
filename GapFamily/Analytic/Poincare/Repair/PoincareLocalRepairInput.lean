import GapFamily.Analytic.Foundation.FiniteSeedThreshold
import GapFamily.Analytic.Foundation.SignedPhysicalSupport
import GapFamily.Analytic.Poincare.Fourier.PoincareCorrectedSeedLinearity
import GapFamily.Analytic.Poincare.Fourier.PoincareSignedOutputMeasure

/-! The finite ordinary signed input of exact local repair. The inverse
correction and anchor remain signed measures; the modular function is the
actual corrected finite Poincaré superposition of their literal combination.
-/
noncomputable section
namespace GapFamily.Analytic
open Set MeasureTheory PoincareEnergyContinuation PoincareEnergyFourier PoincareFourier
open scoped MatrixGroups

/-- The literal finite signed family `ν - μ + a(μ) θ`. -/
def localRepairInput (S : Finset ℤ) (ν μ θ : ℤ → SignedMeasure ℝ) :
    ℤ → SignedMeasure ℝ :=
  ν - μ + finiteSignedThresholdMass S μ • θ

/-- The normalized anchor cancels the correction's entire threshold mass. -/
theorem localRepairInput_threshold (S : Finset ℤ) (ν μ θ : ℤ → SignedMeasure ℝ)
    (hθ : finiteSignedThresholdMass S θ = 1) :
    finiteSignedThresholdMass S (localRepairInput S ν μ θ) =
      finiteSignedThresholdMass S ν := by
  simp only [localRepairInput, finiteSignedThresholdMass_add,
    finiteSignedThresholdMass_sub, finiteSignedThresholdMass_smul, hθ, mul_one]
  ring

/-- Ordinary zeroth moment cancellation removes the repaired seed's threshold atom. -/
theorem localRepairInput_threshold_eq_zero (S : Finset ℤ) (ν μ θ : ℤ → SignedMeasure ℝ)
    (hθ : finiteSignedThresholdMass S θ = 1)
    (hν : ∀ J ∈ S, (∫ᵛ _E : ℝ, (1 : ℝ) ∂<•(ν J)) = 0) :
    finiteSignedThresholdMass S (localRepairInput S ν μ θ) = 0 := by
  rw [localRepairInput_threshold S ν μ θ hθ]
  exact finiteSignedThresholdMass_eq_zero_of_zeroth_moment S ν hν

/-- The repair introduces no input atom when its inverse and anchor are atomless. -/
theorem localRepairInput_singleton (S : Finset ℤ) (ν μ θ : ℤ → SignedMeasure ℝ)
    (J : ℤ) (e : ℝ) (hμ : μ J {e} = 0) (hθ : θ J {e} = 0) :
    localRepairInput S ν μ θ J {e} = ν J {e} := by
  simp [localRepairInput, hμ, hθ]

/-- Physical compact support is proved for the actual repaired signed measure. -/
theorem localRepairInput_physicalSupport (S : Finset ℤ) (ν μ θ : ℤ → SignedMeasure ℝ)
    (M : ℝ)
    (hν : ∀ J ∈ S, ∀ᵐ E ∂(ν J).variation, |(J : ℝ)| ≤ E ∧ E ≤ M)
    (hμ : ∀ J ∈ S, ∀ᵐ E ∂(μ J).variation, |(J : ℝ)| ≤ E ∧ E ≤ M)
    (hθ : ∀ J ∈ S, ∀ᵐ E ∂(θ J).variation, |(J : ℝ)| ≤ E ∧ E ≤ M) :
    ∀ J ∈ S, ∀ᵐ E ∂(localRepairInput S ν μ θ J).variation,
      |(J : ℝ)| ≤ E ∧ E ≤ M := by
  intro J hJ
  exact signedPhysicalSupport_add _ _ J M
    (signedPhysicalSupport_sub _ _ J M (hν J hJ) (hμ J hJ))
    (signedPhysicalSupport_smul _ J M _ (hθ J hJ))

/-- The repair function is the actual corrected finite Poincaré superposition. -/
def localRepairSeed (S : Finset ℤ) (ν μ θ : ℤ → SignedMeasure ℝ)
    (τ : UpperHalfPlane) : ℂ :=
  correctedSeedSuperposition S (localRepairInput S ν μ θ) τ

/-- The actual repair is exactly modular invariant. -/
theorem localRepairSeed_smul (S : Finset ℤ) (ν μ θ : ℤ → SignedMeasure ℝ)
    (τ : UpperHalfPlane) (g : SL(2, ℤ)) :
    localRepairSeed S ν μ θ (g • τ) = localRepairSeed S ν μ θ τ :=
  correctedSeedSuperposition_smul S (localRepairInput S ν μ θ) τ g

/-- Signed input algebra agrees with the actual modular functions. -/
theorem localRepairSeed_eq_sub_add (S : Finset ℤ) (ν μ θ : ℤ → SignedMeasure ℝ)
    (M : ℝ)
    (hν : ∀ J ∈ S, ∀ᵐ E ∂(ν J).variation, |(J : ℝ)| ≤ E ∧ E ≤ M)
    (hμ : ∀ J ∈ S, ∀ᵐ E ∂(μ J).variation, |(J : ℝ)| ≤ E ∧ E ≤ M)
    (hθ : ∀ J ∈ S, ∀ᵐ E ∂(θ J).variation, |(J : ℝ)| ≤ E ∧ E ≤ M)
    (τ : UpperHalfPlane) :
    localRepairSeed S ν μ θ τ =
      correctedSeedSuperposition S ν τ - correctedSeedSuperposition S μ τ +
        (finiteSignedThresholdMass S μ) • correctedSeedSuperposition S θ τ := by
  have hsub : ∀ J ∈ S, ∀ᵐ E ∂((ν - μ) J).variation, |(J : ℝ)| ≤ E ∧ E ≤ M :=
    fun J hJ => signedPhysicalSupport_sub _ _ J M (hν J hJ) (hμ J hJ)
  have hsmul : ∀ J ∈ S, ∀ᵐ E ∂((finiteSignedThresholdMass S μ • θ) J).variation,
      |(J : ℝ)| ≤ E ∧ E ≤ M :=
    fun J hJ => signedPhysicalSupport_smul _ J M _ (hθ J hJ)
  unfold localRepairSeed localRepairInput
  change correctedSeedSuperposition S
    (fun J => (ν J - μ J) + finiteSignedThresholdMass S μ • θ J) τ = _
  rw [correctedSeedSuperposition_add S (fun J => ν J - μ J)
      (fun J => finiteSignedThresholdMass S μ • θ J)
      M hsub hsmul τ,
    correctedSeedSuperposition_sub S ν μ M hν hμ τ,
    correctedSeedSuperposition_smul_input]

/-- The actual repaired seed has its complete convergent signed-measure output. -/
theorem hasSum_localRepairSeed_output (S : Finset ℤ) (ν μ θ : ℤ → SignedMeasure ℝ)
    (M : ℝ)
    (hν : ∀ J ∈ S, ∀ᵐ E ∂(ν J).variation, |(J : ℝ)| ≤ E ∧ E ≤ M)
    (hμ : ∀ J ∈ S, ∀ᵐ E ∂(μ J).variation, |(J : ℝ)| ≤ E ∧ E ≤ M)
    (hθ : ∀ J ∈ S, ∀ᵐ E ∂(θ J).variation, |(J : ℝ)| ≤ E ∧ E ≤ M)
    (y : ℝ) (hy : 0 < y) (x : ℝ) :
    HasSum (fun j : ℤ => (Real.sqrt y : ℂ) *
      (correctedThermalFiniteOutputMeasure S (localRepairInput S ν μ θ)
        j (2 * Real.pi * y) univ : ℂ) * cuspFourierMode j x)
      (localRepairSeed S ν μ θ (rowPoint y hy x)) :=
  hasSum_correctedSeedSuperposition_thermalOutputMeasure S _ M
    (localRepairInput_physicalSupport S ν μ θ M hν hμ hθ) y hy x

end GapFamily.Analytic
