import GapFamily.Construction.RealPermanentSpectrumData
import GapFamily.Construction.RealTailThermal

/-!
# Thermal convergence of the real-parameter permanent spectrum

The disjoint actual cells prove summability of the literal tail lists. The
same list-indexed permanent spectrum therefore has convergent thermal sums
at every positive temperature, including all repeated unit occurrences.
-/

noncomputable section

namespace GapFamily.Construction.RealTailLocalData

variable {a U : ℝ} {T : ℕ} {degree : ℕ → ℕ}
  (d : RealTailLocalData a U T degree)
  (b : ℝ) (hb : 0 ≤ b) (hbT : b ≤ (T : ℝ)) (initial : FiniteRepairState)
  (hinitial : ∀ p ∈ initial.nodes, b ≤ p.1 ∧ |(p.2 : ℝ)| ≤ p.1)

theorem summable_permanentSpectrumData_layerThermal
    (ha : 100 ≤ a) (hT : 1 ≤ (T : ℝ)) {t : ℝ} (ht : 0 < t) :
    Summable ((d.permanentSpectrumData b hb hbT initial hinitial).layerThermal t) := by
  change Summable (fun m =>
    (d.permanentSpectrumData b hb hbT initial hinitial).layerThermal t m)
  simpa only [permanentSpectrumData_layerThermal] using
    d.summable_absoluteLayerBlock_thermal initial ha hT ht

theorem permanentSpectrumData_thermal_summable
    (ha : 100 ≤ a) (hT : 1 ≤ (T : ℝ)) {t : ℝ} (ht : 0 < t) :
    Summable (fun i : (d.permanentSpectrumData b hb hbT initial hinitial).Node =>
      Real.exp (-t * (d.permanentSpectrumData b hb hbT initial hinitial).energy i)) :=
  (d.permanentSpectrumData b hb hbT initial hinitial).thermal_summable t
    (d.summable_permanentSpectrumData_layerThermal b hb hbT initial hinitial ha hT ht)

end GapFamily.Construction.RealTailLocalData
