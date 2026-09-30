import GapFamily.Layer
import GapFamily.NodeSpectrum

/-! Permanent unit nodes with their actual physical energy and integer spin.
Coincident nodes remain distinct until the existing finite-fibre regrouping
constructs the public spectrum and its natural multiplicities. -/
noncomputable section
namespace GapFamily.Construction
open Set

/-- The concrete permanent blocks produced by the cell schedule. Every field
is finite node data or a physical location bound, never modularity or existence
of the desired public spectrum. The marker has energy `b` and spin zero. -/
structure PermanentSpectrumData (b : ℝ) where
  marker_nonneg : 0 ≤ b
  initialCount : ℕ
  layerCount : ℕ → ℕ
  initialEnergy : Fin initialCount → ℝ
  initialSpin : Fin initialCount → ℤ
  layerEnergy : ∀ m, Fin (layerCount m) → ℝ
  layerSpin : ∀ m, Fin (layerCount m) → ℤ
  initial_lower : ∀ i, b ≤ initialEnergy i
  initial_cone : ∀ i, |(initialSpin i : ℝ)| ≤ initialEnergy i
  layer_lower : ∀ m i, b ≤ layerEnergy m i
  layer_cone : ∀ m i, |(layerSpin m i : ℝ)| ≤ layerEnergy m i
  layer_escape : ∀ (m : ℕ) i, (m : ℝ) ≤ layerEnergy m i
  layer_upper : ∀ (m : ℕ) i, layerEnergy m i < (m : ℝ) + 2

namespace PermanentSpectrumData
variable {b : ℝ} (D : PermanentSpectrumData b)

abbrev Node := Layer.Node D.initialCount D.layerCount

def marker : D.Node := Layer.marker D.initialCount D.layerCount

def energy : D.Node → ℝ := Layer.energy b D.initialEnergy D.layerEnergy

def spin : D.Node → ℤ :=
  Sum.elim (fun _ => 0) (Sum.elim D.initialSpin (fun p => D.layerSpin p.1 p.2))

def spectrum (c : ℝ) : Spectrum := nodeSpectrum c D.energy D.spin

@[simp] theorem energy_marker : D.energy D.marker = b := rfl
@[simp] theorem spin_marker : D.spin D.marker = 0 := rfl

theorem node_countable : Countable D.Node := inferInstance

theorem energy_lower (i : D.Node) : b ≤ D.energy i := by
  rcases i with _ | i | ⟨m, i⟩
  · exact le_rfl
  · exact D.initial_lower i
  · exact D.layer_lower m i

theorem energy_cone (i : D.Node) : |(D.spin i : ℝ)| ≤ D.energy i := by
  rcases i with _ | i | ⟨m, i⟩
  · simpa only [energy, spin, Layer.energy, Sum.elim_inl, Int.cast_zero, abs_zero]
      using D.marker_nonneg
  · exact D.initial_cone i
  · exact D.layer_cone m i

theorem layer_energy_mem (m : ℕ) (i : Fin (D.layerCount m)) :
    D.energy (Sum.inr (Sum.inr ⟨m, i⟩)) ∈ Ico (m : ℝ) (m + 2) :=
  ⟨D.layer_escape m i, D.layer_upper m i⟩

theorem energy_sublevel_finite (B : ℝ) : {i : D.Node | D.energy i ≤ B}.Finite :=
  Layer.finite_energy_sublevel b D.initialEnergy D.layerEnergy D.layer_escape B

theorem support_countable (c : ℝ) : (D.spectrum c).support.Countable :=
  Set.countable_range (nodeCoordinate c D.energy D.spin)

theorem support_locally_finite (c B : ℝ) :
    {p ∈ (D.spectrum c).support | dimension p ≤ B}.Finite :=
  coordinateSpectrum_locally_finite
    (nodeCoordinate_locallyFinite c D.energy D.spin D.energy_sublevel_finite) B

/-- Multiplicity is the actual positive natural count of a finite node fibre. -/
theorem multiplicity_pos (c : ℝ) (p : ℝ × ℝ) (hp : p ∈ (D.spectrum c).support) :
    0 < (D.spectrum c).multiplicity p :=
  coordinateSpectrum_multiplicity_pos
    (nodeCoordinate_locallyFinite c D.energy D.spin D.energy_sublevel_finite) p hp

theorem pure_bound (c : ℝ) : ∀ p ∈ (D.spectrum c).support,
    shift c / 2 ≤ p.1 ∧ shift c / 2 ≤ p.2 :=
  nodeSpectrum_pure_bound c D.energy D.spin D.energy_cone

theorem hasGap (c : ℝ) : HasGap (D.spectrum c) (shift c + b) :=
  nodeSpectrum_hasGap c D.energy D.spin b D.energy_lower ⟨D.marker, D.energy_marker⟩

theorem firstDimension_eq (c : ℝ) : firstDimension (D.spectrum c) = shift c + b :=
  (D.hasGap c).firstDimension_eq

/-- The literal unit-node thermal mass in one finite layer. -/
def layerThermal (t : ℝ) (m : ℕ) : ℝ :=
  ∑ i : Fin (D.layerCount m), Real.exp (-t * D.layerEnergy m i)

/-- A proved summable layer thermal total gives the genuine complete node
series, retaining the marker and every node of the finite initial block. -/
theorem thermal_summable (t : ℝ) (hlayer : Summable (D.layerThermal t)) :
    Summable (fun i : D.Node => Real.exp (-t * D.energy i)) := by
  change Summable (fun m => ∑ i : Fin (D.layerCount m),
    Real.exp (-t * D.layerEnergy m i)) at hlayer
  apply Layer.summable_node
  simpa only [energy, Layer.energy, Sum.elim_inr,
    Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using hlayer

theorem spectrum_thermal_summable (c y : ℝ)
    (hlayer : Summable (D.layerThermal (2 * Real.pi * y))) :
    Summable (fun p : (D.spectrum c).support =>
      ((D.spectrum c).multiplicity p : ℝ) *
        Real.exp (-2 * Real.pi * y * dimension p)) := by
  apply nodeSpectrum_thermal_summable c D.energy D.spin D.energy_sublevel_finite
  convert D.thermal_summable (2 * Real.pi * y) hlayer using 1
  funext i
  congr 1
  ring

/-- The schedule may supply finite lists directly. Indexing by `Fin length`
retains repetitions and unit multiplicities, with no quotient or fresh choice. -/
def ofLists (hb : 0 ≤ b) (initial : List (ℝ × ℤ)) (layer : ℕ → List (ℝ × ℤ))
    (hinitial : ∀ p ∈ initial, b ≤ p.1 ∧ |(p.2 : ℝ)| ≤ p.1)
    (hlayer : ∀ (m : ℕ) p, p ∈ layer m → b ≤ p.1 ∧ |(p.2 : ℝ)| ≤ p.1 ∧
      (m : ℝ) ≤ p.1 ∧ p.1 < (m : ℝ) + 2) : PermanentSpectrumData b where
  marker_nonneg := hb
  initialCount := initial.length
  layerCount := fun m => (layer m).length
  initialEnergy := fun i => (initial.get i).1
  initialSpin := fun i => (initial.get i).2
  layerEnergy := fun m i => ((layer m).get i).1
  layerSpin := fun m i => ((layer m).get i).2
  initial_lower := fun i => (hinitial _ (List.get_mem initial i)).1
  initial_cone := fun i => (hinitial _ (List.get_mem initial i)).2
  layer_lower := fun m i => (hlayer m _ (List.get_mem (layer m) i)).1
  layer_cone := fun m i => (hlayer m _ (List.get_mem (layer m) i)).2.1
  layer_escape := fun m i => (hlayer m _ (List.get_mem (layer m) i)).2.2.1
  layer_upper := fun m i => (hlayer m _ (List.get_mem (layer m) i)).2.2.2

end PermanentSpectrumData
end GapFamily.Construction
