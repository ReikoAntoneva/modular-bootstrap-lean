import GapFamily.Construction.PermanentSpectrumData
import GapFamily.NodeFirstPrimary

/-! A strict separation of the initial and emitted blocks from the marker
proves uniqueness and unit multiplicity in the actual permanent spectrum. -/

noncomputable section

namespace GapFamily.Construction.PermanentSpectrumData

variable {b : ℝ} (D : PermanentSpectrumData b)

/-- All nonmarker occurrences have strictly larger shifted energy. -/
theorem energy_strict_of_block_strict
    (hinitial : ∀ i, b < D.initialEnergy i)
    (hlayer : ∀ m i, b < D.layerEnergy m i)
    (i : D.Node) (hi : i ≠ D.marker) : b < D.energy i := by
  rcases i with u | i | ⟨m, i⟩
  · exact False.elim (hi (by cases u; rfl))
  · exact hinitial i
  · exact hlayer m i

/-- Regrouping the actual strict blocks retains one scalar marker of
multiplicity one as the sole primary at the first dimension. -/
theorem hasUnitScalarGap (c : ℝ)
    (hinitial : ∀ i, b < D.initialEnergy i)
    (hlayer : ∀ m i, b < D.layerEnergy m i) :
    HasUnitScalarGap (D.spectrum c) (shift c + b) :=
  nodeSpectrum_hasUnitScalarGap c D.energy D.spin b D.marker D.energy_marker
    D.spin_marker (D.energy_strict_of_block_strict hinitial hlayer)

/-- A literal list construction supplies strictness without changing the
repeated-node indices or their subsequent fibre counts. -/
theorem ofLists_hasUnitScalarGap (hb : 0 ≤ b)
    (initial : List (ℝ × ℤ)) (layer : ℕ → List (ℝ × ℤ))
    (hinitial : ∀ p ∈ initial, b ≤ p.1 ∧ |(p.2 : ℝ)| ≤ p.1)
    (hlayer : ∀ (m : ℕ) p, p ∈ layer m → b ≤ p.1 ∧ |(p.2 : ℝ)| ≤ p.1 ∧
      (m : ℝ) ≤ p.1 ∧ p.1 < (m : ℝ) + 2)
    (hinitStrict : ∀ p ∈ initial, b < p.1)
    (hlayerStrict : ∀ m p, p ∈ layer m → b < p.1) (c : ℝ) :
    HasUnitScalarGap ((ofLists hb initial layer hinitial hlayer).spectrum c)
      (shift c + b) := by
  apply hasUnitScalarGap
  · intro i
    exact hinitStrict _ (List.get_mem initial i)
  · intro m i
    exact hlayerStrict m _ (List.get_mem (layer m) i)

end GapFamily.Construction.PermanentSpectrumData
