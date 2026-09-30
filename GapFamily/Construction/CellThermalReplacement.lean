import GapFamily.Construction.CellCoordinateMeasure
import GapFamily.Construction.CellThermalContinuumRemoval
import GapFamily.Analytic.Foundation.SignedThermalDensity
import GapFamily.Analytic.Poincare.Fourier.PoincareThermalOutputMeasure

/-!
# Literal thermal replacement on one physical cell

The actual residual measure is thermally tilted before it is decomposed into
its finite unit-node measure and its ordinary signed density. Compact cell
integrability suffices; no positivity of the numerator is needed.
-/

noncomputable section
namespace GapFamily.Construction

open MeasureTheory Set Analytic
open scoped BigOperators Classical

/-- Thermal weighting respects signed subtraction whenever both actual signed
integrals converge. -/
theorem thermalSignedInputMeasure_sub_of_integrable (ν μ : SignedMeasure ℝ) (t : ℝ)
    (hν : ν.Integrable (fun E => Real.exp (-t * E)))
    (hμ : μ.Integrable (fun E => Real.exp (-t * E))) :
    thermalSignedInputMeasure (ν - μ) t =
      thermalSignedInputMeasure ν t - thermalSignedInputMeasure μ t := by
  ext s hs
  unfold thermalSignedInputMeasure
  rw [VectorMeasure.withDensity_apply (hν.sub_vectorMeasure hμ),
    _root_.sub_apply, VectorMeasure.withDensity_apply hν, VectorMeasure.withDensity_apply hμ,
    VectorMeasure.restrict_sub]
  exact VectorMeasure.integral_sub_vectorMeasure hν.restrict hμ.restrict

/-- Every finite unit-node measure has a genuine thermal integral, at any real
thermal parameter, retaining all repeated atoms. -/
theorem unitAtomSignedMeasure_thermal_integrable {N : ℕ} (node : Fin N → ℝ) (t : ℝ) :
    (unitAtomSignedMeasure node).Integrable (fun E => Real.exp (-t * E)) :=
  unitAtomSignedMeasure_integrable node _

/-- The thermally weighted atom list is literally the finite sum of weighted
Dirac measures at its actual nodes. -/
theorem thermalSignedInputMeasure_unitAtomSignedMeasure {N : ℕ}
    (node : Fin N → ℝ) (t : ℝ) :
    thermalSignedInputMeasure (unitAtomSignedMeasure node) t =
      ∑ i, VectorMeasure.dirac (node i) (Real.exp (-t * node i)) := by
  ext s hs
  rw [thermalSignedInputMeasure,
    VectorMeasure.withDensity_apply (unitAtomSignedMeasure_thermal_integrable node t),
    ← VectorMeasure.integral_indicator hs, integral_unitAtomSignedMeasure]
  simp only [FunLike.coe_sum, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : node i ∈ s
  · simp [hi, hs]
  · simp [hi, hs]

/-- The mass of the weighted finite node measure is the actual finite Boltzmann sum. -/
theorem thermalSignedInputMeasure_unitAtomSignedMeasure_univ {N : ℕ}
    (node : Fin N → ℝ) (t : ℝ) :
    thermalSignedInputMeasure (unitAtomSignedMeasure node) t univ =
      ∑ i, Real.exp (-t * node i) := by
  rw [thermalSignedInputMeasure_univ, integral_unitAtomSignedMeasure]

/-- On a finite physical cell the density, its signed thermal pairing, and the
ordinary thermal numerator are all genuinely integrable. The parameter need
not be positive because the cell is compact. -/
theorem cellDensity_thermal_integrable (j : ℤ) (L V t : ℝ) {q : ℝ → ℝ}
    (hq : IntegrableOn q (Ioo L V) (referenceMeasure j)) :
    (((referenceMeasure j).restrict (Ioo L V)).withDensityᵥ q).Integrable
        (fun E => Real.exp (-t * E)) ∧
      IntegrableOn (fun E => Real.exp (-t * E) * q E) (Ioo L V) (referenceMeasure j) := by
  have hc : Continuous (fun E : ℝ => Real.exp (-t * E)) := by fun_prop
  obtain ⟨C, hC⟩ := referenceMeasure_cell_continuous_bounded j L V hc
  obtain ⟨hν, hp, _⟩ := signedDensity_integral_of_norm_bdd hq hc.aestronglyMeasurable hC
  exact ⟨hν, hp.congr (Filter.Eventually.of_forall (fun E => mul_comm (q E) _))⟩

/-- Global ordinary thermal integrability implies unweighted integrability on
every finite cell: the inverse thermal weight is bounded on the closed cell. -/
theorem cellDensity_integrable_of_thermal (j : ℤ) (L V t : ℝ) {q : ℝ → ℝ}
    (hq : Integrable (fun E => Real.exp (-t * E) * q E) (referenceMeasure j)) :
    IntegrableOn q (Ioo L V) (referenceMeasure j) := by
  exact integrableOn_density_of_thermal_integrable hq L V

/-- The literal cell residual has an ordinary thermal integral. -/
theorem cellResidualMeasure_thermal_integrable {N : ℕ} (j : ℤ) (L V t : ℝ)
    {q : ℝ → ℝ} (node : Fin N → ℝ)
    (hq : IntegrableOn q (Ioo L V) (referenceMeasure j)) :
    (cellResidualMeasure j L V q node).Integrable (fun E => Real.exp (-t * E)) :=
  (unitAtomSignedMeasure_thermal_integrable node t).sub_vectorMeasure
    (cellDensity_thermal_integrable j L V t hq).1

/-- The exact thermal signed measure of the actual cell residual is the finite
weighted node measure minus the ordinary weighted continuum on the open cell. -/
theorem thermalSignedInputMeasure_cellResidualMeasure {N : ℕ} (j : ℤ) (L V t : ℝ)
    {q : ℝ → ℝ} (node : Fin N → ℝ)
    (hq : IntegrableOn q (Ioo L V) (referenceMeasure j)) :
    thermalSignedInputMeasure (cellResidualMeasure j L V q node) t =
      thermalSignedInputMeasure (unitAtomSignedMeasure node) t -
        ((referenceMeasure j).restrict (Ioo L V)).withDensityᵥ
          (fun E => Real.exp (-t * E) * q E) := by
  rw [cellResidualMeasure, thermalSignedInputMeasure_sub_of_integrable _ _ t
    (unitAtomSignedMeasure_thermal_integrable node t)
    (cellDensity_thermal_integrable j L V t hq).1]
  congr 1
  exact signedDensity_withDensity_mul hq (cellDensity_thermal_integrable j L V t hq).1

/-- The full explicit Dirac-minus-density form retains every node occurrence. -/
theorem thermalSignedInputMeasure_cellResidualMeasure_eq_sum {N : ℕ}
    (j : ℤ) (L V t : ℝ) {q : ℝ → ℝ} (node : Fin N → ℝ)
    (hq : IntegrableOn q (Ioo L V) (referenceMeasure j)) :
    thermalSignedInputMeasure (cellResidualMeasure j L V q node) t =
      (∑ i, VectorMeasure.dirac (node i) (Real.exp (-t * node i))) -
        ((referenceMeasure j).restrict (Ioo L V)).withDensityᵥ
          (fun E => Real.exp (-t * E) * q E) := by
  rw [thermalSignedInputMeasure_cellResidualMeasure j L V t node hq,
    thermalSignedInputMeasure_unitAtomSignedMeasure]

/-- Adding the actual cell residual replaces precisely the removed continuum
by the actual finite node measure. The new continuum uses `[L,V)`, retaining
its right endpoint pointwise, and is ordinarily thermally integrable. -/
theorem thermalCellReplacement {N : ℕ} (j : ℤ) (L V t : ℝ)
    {q : ℝ → ℝ} (node : Fin N → ℝ)
    (hq : Integrable (fun E => Real.exp (-t * E) * q E) (referenceMeasure j)) :
    (referenceMeasure j).withDensityᵥ (fun E => Real.exp (-t * E) * q E) +
        thermalSignedInputMeasure (cellResidualMeasure j L V q node) t =
      thermalSignedInputMeasure (unitAtomSignedMeasure node) t +
        (referenceMeasure j).withDensityᵥ
          (fun E => Real.exp (-t * E) * removeCellDensity L V q E) := by
  rw [thermalSignedInputMeasure_cellResidualMeasure j L V t node
      (cellDensity_integrable_of_thermal j L V t hq),
    thermal_removeCellDensity_withDensity j L V t hq]
  abel

/-- The same replacement as a completely explicit equality of signed measures. -/
theorem thermalCellReplacement_eq_sum {N : ℕ} (j : ℤ) (L V t : ℝ)
    {q : ℝ → ℝ} (node : Fin N → ℝ)
    (hq : Integrable (fun E => Real.exp (-t * E) * q E) (referenceMeasure j)) :
    (referenceMeasure j).withDensityᵥ (fun E => Real.exp (-t * E) * q E) +
        thermalSignedInputMeasure (cellResidualMeasure j L V q node) t =
      (∑ i, VectorMeasure.dirac (node i) (Real.exp (-t * node i))) +
        (referenceMeasure j).withDensityᵥ
          (fun E => Real.exp (-t * E) * removeCellDensity L V q E) := by
  rw [thermalCellReplacement j L V t node hq, thermalSignedInputMeasure_unitAtomSignedMeasure]

/-- Every old signed atom measure is retained literally during the replacement. -/
theorem thermalCellReplacement_preserves_old {N : ℕ} (old : SignedMeasure ℝ)
    (j : ℤ) (L V t : ℝ) {q : ℝ → ℝ} (node : Fin N → ℝ)
    (hq : Integrable (fun E => Real.exp (-t * E) * q E) (referenceMeasure j)) :
    (old + (referenceMeasure j).withDensityᵥ (fun E => Real.exp (-t * E) * q E)) +
        thermalSignedInputMeasure (cellResidualMeasure j L V q node) t =
      (old + thermalSignedInputMeasure (unitAtomSignedMeasure node) t) +
        (referenceMeasure j).withDensityᵥ
          (fun E => Real.exp (-t * E) * removeCellDensity L V q E) := by
  rw [add_assoc, thermalCellReplacement j L V t node hq, ← add_assoc]

end GapFamily.Construction
