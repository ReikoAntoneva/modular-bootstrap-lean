import GapFamily.Construction.TailCellExistence
import GapFamily.Analytic.Foundation.SignedThermalDensity

/-! Thermal variation of the actual atoms-minus-continuum tail-cell residual.
All pairings are integrable for the positive measures that occur in the bound.
-/

noncomputable section

open Set MeasureTheory Real
open scoped BigOperators Classical
open GapFamily.Analytic

namespace GapFamily.Construction

/-- A nonnegative test against the variation of a finite list of unit atoms
is bounded by its literal finite sum, retaining all node multiplicities. -/
theorem unitAtomSignedMeasure_integral_variation_le {N : ℕ} (node : Fin N → ℝ)
    (f : ℝ → ℝ) (hf : ∀ E, 0 ≤ f E) :
    (∫ E, f E ∂(unitAtomSignedMeasure node).variation) ≤ ∑ i, f (node i) := by
  have hvar : (unitAtomSignedMeasure node).variation ≤ ∑ i, Measure.dirac (node i) := by
    simpa only [unitAtomSignedMeasure, Measure.variation_toSignedMeasure] using
      VectorMeasure.variation_finsetSum_le Finset.univ
        (fun i => (Measure.dirac (node i)).toSignedMeasure)
  have hi (i : Fin N) : Integrable f (Measure.dirac (node i)) :=
    integrable_dirac (by finiteness)
  have hiSum : Integrable f (∑ i, Measure.dirac (node i)) :=
    integrable_finsetSum_measure.mpr (fun i _ => hi i)
  calc
    _ ≤ ∫ E, f E ∂(∑ i, Measure.dirac (node i)) :=
      integral_mono_measure hvar (Filter.Eventually.of_forall hf) hiSum
    _ = _ := by
      rw [integral_finsetSum_measure (fun i _ => hi i)]
      simp only [integral_dirac]

/-- The positive variation measure of an ordinary signed density integrates
the absolute value of that density. -/
theorem integral_signedDensity_variation_eq {μ : Measure ℝ} {q : ℝ → ℝ}
    (hq : Integrable q μ) (f : ℝ → ℝ) :
    (∫ E, f E ∂(μ.withDensityᵥ q).variation) = ∫ E, f E * |q E| ∂μ := by
  rw [Measure.variation_withDensityᵥ hq,
    integral_withDensity_eq_integral_toReal_smul₀
      hq.aestronglyMeasurable.enorm (Filter.Eventually.of_forall (fun _ => enorm_lt_top))]
  simp only [toReal_enorm, Real.norm_eq_abs, smul_eq_mul, mul_comm]

/-- The actual open cell is concentrated on nonnegative energies when its
left endpoint is nonnegative. No finiteness of the bare reference measure is used. -/
theorem TailCell.reference_ae_nonneg {j : ℤ} {L : ℝ} {k : ℕ} {q : ℝ → ℝ}
    (cell : TailCell j L k q) (hL : 0 ≤ L) :
    ∀ᵐ E ∂(referenceMeasure j).restrict (Ioo L cell.right), 0 ≤ E := by
  filter_upwards [referenceMeasure_cell_ae_mem_Icc j L cell.right] with E hE
  exact hL.trans hE.1

/-- The exponentially weighted absolute continuum is an ordinary integrable
density on the actual open tail cell. -/
theorem TailCell.thermal_density_integrable {j : ℤ} {L t : ℝ} {k : ℕ} {q : ℝ → ℝ}
    (cell : TailCell j L k q) (hL : 0 ≤ L) (ht : 0 ≤ t) :
    IntegrableOn (fun E => exp (-t * E) * |q E|) (Ioo L cell.right) (referenceMeasure j) :=
  signedDensity_integrable_thermal_mul cell.density_integrable.abs
    (cell.reference_ae_nonneg hL) ht

/-- The thermal weight is integrable for the positive variation measure of
the actual ordinary signed continuum. -/
theorem TailCell.thermal_density_variation_integrable
    {j : ℤ} {L t : ℝ} {k : ℕ} {q : ℝ → ℝ}
    (cell : TailCell j L k q) (hL : 0 ≤ L) (ht : 0 ≤ t) :
    Integrable (fun E => exp (-t * E))
      (((referenceMeasure j).restrict (Ioo L cell.right)).withDensityᵥ q).variation :=
  signedDensity_integrable_thermal cell.density_integrable (cell.reference_ae_nonneg hL) ht

/-- Every actual finite atomic thermal pairing is integrable. -/
theorem TailCell.thermal_atom_variation_integrable
    {j : ℤ} {L t : ℝ} {k : ℕ} {q : ℝ → ℝ} (cell : TailCell j L k q) :
    Integrable (fun E => exp (-t * E)) (unitAtomSignedMeasure cell.node).variation :=
  unitAtomSignedMeasure_integrable cell.node _

/-- The actual residual has an integrable thermal pairing with its positive
variation measure. -/
theorem TailCell.thermal_residual_integrable
    {j : ℤ} {L t : ℝ} {k : ℕ} {q : ℝ → ℝ}
    (cell : TailCell j L k q) (hL : 0 ≤ L) (ht : 0 ≤ t) :
    Integrable (fun E => exp (-t * E)) cell.residual.variation := by
  exact VectorMeasure.Integrable.sub_vectorMeasure
    (cell.thermal_atom_variation_integrable (t := t))
    (cell.thermal_density_variation_integrable hL ht)

/-- Thermal variation of the actual residual is bounded by the node thermal
sum plus the ordinary thermal absolute continuum mass. -/
theorem TailCell.thermal_variation_le {j : ℤ} {L t : ℝ} {k : ℕ} {q : ℝ → ℝ}
    (cell : TailCell j L k q) (hL : 0 ≤ L) (ht : 0 ≤ t) :
    (∫ E, exp (-t * E) ∂cell.residual.variation) ≤
      (∑ i, exp (-t * cell.node i)) +
        ∫ E in Ioo L cell.right, exp (-t * E) * |q E| ∂referenceMeasure j := by
  have hA := cell.thermal_atom_variation_integrable (t := t)
  have hD := cell.thermal_density_variation_integrable hL ht
  have hvar : cell.residual.variation ≤ (unitAtomSignedMeasure cell.node).variation +
      (((referenceMeasure j).restrict (Ioo L cell.right)).withDensityᵥ q).variation :=
    VectorMeasure.variation_sub_le
  calc
    _ ≤ ∫ E, exp (-t * E) ∂((unitAtomSignedMeasure cell.node).variation +
        (((referenceMeasure j).restrict (Ioo L cell.right)).withDensityᵥ q).variation) :=
      integral_mono_measure hvar (Filter.Eventually.of_forall (fun E => (exp_pos _).le))
        (hA.add_measure hD)
    _ = (∫ E, exp (-t * E) ∂(unitAtomSignedMeasure cell.node).variation) +
        ∫ E in Ioo L cell.right, exp (-t * E) * |q E| ∂referenceMeasure j := by
      rw [integral_add_measure hA hD,
        integral_signedDensity_variation_eq cell.density_integrable]
    _ ≤ _ := add_le_add
      (unitAtomSignedMeasure_integral_variation_le cell.node (fun E => exp (-t * E))
        (fun E => (exp_pos _).le)) le_rfl

end GapFamily.Construction
