import GapFamily.Analytic.Poincare.Repair.PoincareLocalRepairInput
import GapFamily.Analytic.Poincare.Fourier.PoincareLowBandOutput

/-! Exact ordinary output algebra for local repair. These identities concern
the actual kernel density measures and actual reconstructed Poincaré seed.
The inverse and anchor are instantiated in the following local-repair module.
-/
noncomputable section
namespace GapFamily.Analytic
open Set MeasureTheory

/-- Low-band output is linear on the actual repair input. -/
theorem localRepairInput_lowBandOutput (S : Finset ℤ) (ν μ θ : ℤ → SignedMeasure ℝ)
    (j : ℤ) (M B : ℝ)
    (hν : ∀ J ∈ S, ∀ᵐ E ∂(ν J).variation, |(J : ℝ)| ≤ E ∧ E ≤ M)
    (hμ : ∀ J ∈ S, ∀ᵐ E ∂(μ J).variation, |(J : ℝ)| ≤ E ∧ E ≤ M)
    (hθ : ∀ J ∈ S, ∀ᵐ E ∂(θ J).variation, |(J : ℝ)| ≤ E ∧ E ≤ M) :
    finiteCorrectedLowBandOutput S (localRepairInput S ν μ θ) j M B
      (localRepairInput_physicalSupport S ν μ θ M hν hμ hθ) =
      finiteCorrectedLowBandOutput S ν j M B hν -
        finiteCorrectedLowBandOutput S μ j M B hμ +
        finiteSignedThresholdMass S μ • finiteCorrectedLowBandOutput S θ j M B hθ := by
  have hsub : ∀ J ∈ S, ∀ᵐ E ∂((ν - μ) J).variation, |(J : ℝ)| ≤ E ∧ E ≤ M :=
    fun J hJ => signedPhysicalSupport_sub _ _ J M (hν J hJ) (hμ J hJ)
  have hsmul : ∀ J ∈ S, ∀ᵐ E ∂((finiteSignedThresholdMass S μ • θ) J).variation,
      |(J : ℝ)| ≤ E ∧ E ≤ M :=
    fun J hJ => signedPhysicalSupport_smul _ J M _ (hθ J hJ)
  calc
    _ = finiteCorrectedLowBandOutput S (fun J => ν J - μ J) j M B hsub +
        finiteCorrectedLowBandOutput S (fun J => finiteSignedThresholdMass S μ • θ J)
          j M B hsmul :=
      finiteCorrectedLowBandOutput_add S (fun J => ν J - μ J)
        (fun J => finiteSignedThresholdMass S μ • θ J) j M B hsub hsmul
    _ = _ := by
      rw [finiteCorrectedLowBandOutput_sub S ν μ j M B hν hμ,
        finiteCorrectedLowBandOutput_smul]

/-- The actual inverse cancellation and zero-output anchor make the repaired
low-band measure exactly the original direct input. -/
theorem localRepairInput_lowBandOutput_eq_direct
    (S : Finset ℤ) (ν μ θ : ℤ → SignedMeasure ℝ) (j : ℤ) (M B : ℝ)
    (hν : ∀ J ∈ S, ∀ᵐ E ∂(ν J).variation, |(J : ℝ)| ≤ E ∧ E ≤ M)
    (hμ : ∀ J ∈ S, ∀ᵐ E ∂(μ J).variation, |(J : ℝ)| ≤ E ∧ E ≤ M)
    (hθ : ∀ J ∈ S, ∀ᵐ E ∂(θ J).variation, |(J : ℝ)| ≤ E ∧ E ≤ M)
    (hcancel : finiteCorrectedLowBandOutput S μ j M B hμ =
      correctedSignedOutputMeasure (fun J : S => ν J) Subtype.val j M B
        (fun J => hν J J.property))
    (hanchor : finiteCorrectedLowBandOutput S θ j M B hθ = 0) :
    finiteCorrectedLowBandOutput S (localRepairInput S ν μ θ) j M B
      (localRepairInput_physicalSupport S ν μ θ M hν hμ hθ) =
      if j ∈ S then (ν j).restrict (Ioo |(j : ℝ)| B) else 0 := by
  rw [localRepairInput_lowBandOutput S ν μ θ j M B hν hμ hθ,
    hcancel, hanchor, smul_zero, add_zero]
  exact add_sub_cancel_right _ _

/-- Every output atom of a moment-cancelling repair is exactly an original
input atom. No threshold or edge atom is produced by either correction. -/
theorem localRepairInput_thermalOutput_singleton
    (S : Finset ℤ) (ν μ θ : ℤ → SignedMeasure ℝ) (j : ℤ) (M : ℝ)
    (hν : ∀ J ∈ S, ∀ᵐ E ∂(ν J).variation, |(J : ℝ)| ≤ E ∧ E ≤ M)
    (hμ : ∀ J ∈ S, ∀ᵐ E ∂(μ J).variation, |(J : ℝ)| ≤ E ∧ E ≤ M)
    (hθ : ∀ J ∈ S, ∀ᵐ E ∂(θ J).variation, |(J : ℝ)| ≤ E ∧ E ≤ M)
    (hμatom : ∀ J ∈ S, ∀ e : ℝ, μ J {e} = 0)
    (hθatom : ∀ J ∈ S, ∀ e : ℝ, θ J {e} = 0)
    (hanchor : finiteSignedThresholdMass S θ = 1)
    (hmoment : ∀ J ∈ S, (∫ᵛ _E : ℝ, (1 : ℝ) ∂<•(ν J)) = 0)
    {t : ℝ} (ht : 0 < t) (e : ℝ) :
    correctedThermalFiniteOutputMeasure S (localRepairInput S ν μ θ) j t {e} =
      if j ∈ S then Real.exp (-t * e) * ν j {e} else 0 := by
  rw [correctedThermalFiniteOutputMeasure_singleton S _ j M
    (localRepairInput_physicalSupport S ν μ θ M hν hμ hθ) ht e,
    localRepairInput_threshold_eq_zero S ν μ θ hanchor hmoment]
  simp only [ite_self, add_zero]
  by_cases hj : j ∈ S
  · rw [ite_eq_left hj, ite_eq_left hj,
      localRepairInput_singleton S ν μ θ j e (hμatom j hj e) (hθatom j hj e)]
  · simp only [ite_eq_right hj]

end GapFamily.Analytic
