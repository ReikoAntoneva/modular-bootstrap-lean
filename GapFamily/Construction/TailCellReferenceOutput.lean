import GapFamily.Construction.TailCellStateUpdate
import GapFamily.Construction.ReferenceOutput

/-! Literal one-cell updates preserve ordinary output for any actual modular
reference and any prescribed marker, including energy zero. -/

noncomputable section
namespace GapFamily.Construction.FiniteRepairState
open Set MeasureTheory Analytic

variable (s : FiniteRepairState) {J : ℤ} {k : ℕ}
  (cell : TailCell J (s.front J) k (s.numerator J))
  (B : ℝ) (hB : 1 ≤ B) (hJ : |(J : ℝ)| ≤ s.front J) (hcut : cell.right < B)

theorem addTailCell_referenceSeed {a : ℝ} (ref : ReferenceOutput a) (τ : UpperHalfPlane) :
    (s.addTailCell cell B hB hJ hcut).referenceSeed ref τ =
      s.referenceSeed ref τ + cell.repairSeed B hB hJ hcut τ := by
  change ref.seed τ + repairHistorySeed
    (s.history ++ [cell.repairDatum B hB hJ hcut]) τ = _
  simp only [repairHistorySeed_append, repairHistorySeed_cons,
    repairHistorySeed_nil, add_zero]
  change _ = (ref.seed τ + repairHistorySeed s.history τ) + _
  rw [add_assoc]
  rfl

theorem addTailCell_referenceThermalOutput {a : ℝ} (ref : ReferenceOutput a)
    (j : ℤ) (t : ℝ) :
    (s.addTailCell cell B hB hJ hcut).referenceThermalOutput ref j t =
      s.referenceThermalOutput ref j t + cell.repairOutput B hB hJ hcut j t := by
  change ref.thermalOutput j t + repairHistoryThermalOutput
    (s.history ++ [cell.repairDatum B hB hJ hcut]) j t = _
  simp only [repairHistoryThermalOutput_append, repairHistoryThermalOutput_cons,
    repairHistoryThermalOutput_nil, add_zero]
  change _ = (ref.thermalOutput j t + repairHistoryThermalOutput s.history j t) + _
  rw [add_assoc]
  rfl

theorem addTailCell_hasReferenceOutput {a : ℝ} (ref : ReferenceOutput a) (δ : ℝ)
    (ho : s.HasReferenceOutput ref δ) (hi : s.ThermalIntegrable) :
    (s.addTailCell cell B hB hJ hcut).HasReferenceOutput ref δ := by
  intro j t ht
  rw [addTailCell_referenceThermalOutput, ho j t ht, addTailCell_atomicThermalOutput]
  exact cell.thermalReplacement_preserves_old B hB hJ hcut
    (s.atomicThermalOutput δ j t) j ht (hi j t ht)

theorem addTailCell_referenceOutput_invariant {a : ℝ} (ref : ReferenceOutput a) (δ : ℝ)
    (ho : s.HasReferenceOutput ref δ) (hi : s.ThermalIntegrable) (hc : s.Cleared)
    (hf : ∀ j : ℤ, s.front j ≤ max B |(j : ℝ)|) :
    (s.addTailCell cell B hB hJ hcut).HasReferenceOutput ref δ ∧
      (s.addTailCell cell B hB hJ hcut).ThermalIntegrable ∧
      (s.addTailCell cell B hB hJ hcut).Cleared :=
  ⟨s.addTailCell_hasReferenceOutput cell B hB hJ hcut ref δ ho hi,
    s.addTailCell_thermalIntegrable cell B hB hJ hcut hi,
    s.addTailCell_cleared cell B hB hJ hcut hc hf⟩

end GapFamily.Construction.FiniteRepairState
