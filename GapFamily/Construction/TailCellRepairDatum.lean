import GapFamily.Construction.TailCellRepair
import GapFamily.Construction.CanonicalRepairDatum

/-! An actual tail cell supplies the concrete datum used in finite repair histories. -/

noncomputable section
namespace GapFamily.Construction
open Set MeasureTheory Analytic

namespace TailCell
variable {J : ℤ} {L : ℝ} {k : ℕ} {q : ℝ → ℝ} (cell : TailCell J L k q)
  (B : ℝ) (hB : 1 ≤ B) (hJ : |(J : ℝ)| ≤ L) (hcut : cell.right < B)

/-- The datum consists of the actual single-row residual of the constructed cell;
all local-repair hypotheses follow from its support and matched zeroth moment. -/
def repairDatum : CanonicalRepairDatum where
  cutoffB := B
  cutoff_one := hB
  input := cell.rowInput
  physicalSupport := cell.rowInput_physicalSupport B hB hJ hcut
  masszero := cell.rowInput_integral_one B
  inside := cell.rowInput_inside B hcut

@[simp] theorem repairDatum_cutoffB : (cell.repairDatum B hB hJ hcut).cutoffB = B := rfl
@[simp] theorem repairDatum_input : (cell.repairDatum B hB hJ hcut).input = cell.rowInput := rfl
@[simp] theorem repairDatum_repairInput :
    (cell.repairDatum B hB hJ hcut).repairInput = cell.repairInput B hB hJ hcut := rfl
@[simp] theorem repairDatum_seed :
    (cell.repairDatum B hB hJ hcut).seed = cell.repairSeed B hB hJ hcut := rfl
@[simp] theorem repairDatum_thermalOutput :
    (cell.repairDatum B hB hJ hcut).thermalOutput = cell.repairOutput B hB hJ hcut := rfl

theorem summable_repairOutput_totalVariation {t : ℝ} (ht : 0 < t) :
    Summable (fun j : ℤ => (cell.repairOutput B hB hJ hcut j t).variation.real univ) :=
  (cell.repairDatum B hB hJ hcut).summable_thermalOutput_totalVariation ht

theorem continuous_repairSeed : Continuous (cell.repairSeed B hB hJ hcut) :=
  (cell.repairDatum B hB hJ hcut).continuous_seed

end TailCell
end GapFamily.Construction
