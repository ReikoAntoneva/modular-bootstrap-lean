import GapFamily.Construction.ReferenceOutput
import GapFamily.Construction.FixedCutoffReference

/-! The independent-cutoff modular construction supplies the generic reference
interface, with the threshold case included. -/

noncomputable section
namespace GapFamily.Construction.ReferenceOutput

def fixedCutoff (a B δ : ℝ) (ha : 2 ≤ a) (hB : 1 ≤ B)
    (hδ : 0 ≤ δ) (hδB : δ ≤ B) : ReferenceOutput a where
  seed := fixedCutoffReferenceSeed a B δ ha hB hδ hδB
  thermalOutput := fixedCutoffReferenceThermalMeasure a B δ ha hB hδ hδB
  seed_smul := fixedCutoffReferenceSeed_smul a B δ ha hB hδ hδB
  hasSum_seed_output := hasSum_fixedCutoffReferenceSeed_thermalMeasure a B δ ha hB hδ hδB

end GapFamily.Construction.ReferenceOutput
