import GapFamily.Construction.InitialCellPhysical
import GapFamily.Construction.TailCellVariation

/-!
# Actual signed residual of an initial reference cell

The selected endpoint carries its positive integer mass of literal unit
atoms. Its atoms-minus-continuum residual has zero mass, compact variation
support, and ordinarily integrable vanishing coordinate moments. The valid
total-variation bound uses the absolute continuum mass even when it is signed.
-/

noncomputable section

open Set MeasureTheory Real
open GapFamily.Analytic
open scoped BigOperators

namespace GapFamily.Construction

/-- A finite signed initial cell, with its endpoint selected in the unit
window above `U` and exactly its positive integer mass of unit atoms. -/
structure InitialReferenceCell (j : ℤ) (L U : ℝ) (k : ℕ) (q : ℝ → ℝ) where
  right : ℝ
  right_mem : right ∈ Icc U (U + 1)
  count : ℕ
  count_pos : 0 < count
  node : Fin count → ℝ
  node_mem : ∀ i, node i ∈ Icc L right
  node_strict : ∀ i, node i ∈ Ioo L right
  density_integrable : IntegrableOn q (Ioo L right) (referenceMeasure j)
  mass_eq : (∫ E in Ioo L right, q E ∂referenceMeasure j) = (count : ℝ)
  residual_mass : cellResidualMeasure j L right q node univ = 0
  residual_support : (cellResidualMeasure j L right q node).variation (Icc L right)ᶜ = 0
  moment : ∀ p : Polynomial ℝ, p.natDegree ≤ k →
    (cellResidualMeasure j L right q node).Integrable
      (fun E => p.eval (rootCoord |(j : ℝ)| E)) ∧
    (∫ᵛ E, p.eval (rootCoord |(j : ℝ)| E)
      ∂<•cellResidualMeasure j L right q node) = 0

/-- The actual initial-cell signed residual. -/
def InitialReferenceCell.residual {j : ℤ} {L U : ℝ} {k : ℕ} {q : ℝ → ℝ}
    (cell : InitialReferenceCell j L U k q) : SignedMeasure ℝ :=
  cellResidualMeasure j L cell.right q cell.node

/-- The actual positive variation measure is concentrated on the closed cell. -/
theorem InitialReferenceCell.ae_mem_cell
    {j : ℤ} {L U : ℝ} {k : ℕ} {q : ℝ → ℝ}
    (cell : InitialReferenceCell j L U k q) :
    ∀ᵐ E ∂cell.residual.variation, E ∈ Icc L cell.right :=
  ae_iff.mpr cell.residual_support

/-- An initial cell above its physical spin edge stays in the physical cone
and below the prescribed terminal window. -/
theorem InitialReferenceCell.physical_support
    {j : ℤ} {L U : ℝ} {k : ℕ} {q : ℝ → ℝ}
    (cell : InitialReferenceCell j L U k q) (hL : |(j : ℝ)| ≤ L) :
    ∀ᵐ E ∂cell.residual.variation, |(j : ℝ)| ≤ E ∧ E ≤ U + 1 := by
  filter_upwards [cell.ae_mem_cell] with E hE
  exact ⟨hL.trans hE.1, hE.2.trans cell.right_mem.2⟩

/-- Every coordinate polynomial is genuinely integrable against both the
signed residual and the ordinary continuum density. -/
theorem InitialReferenceCell.coordinate_polynomial_integrable
    {j : ℤ} {L U : ℝ} {k : ℕ} {q : ℝ → ℝ}
    (cell : InitialReferenceCell j L U k q) (p : Polynomial ℝ) :
    cell.residual.Integrable (fun E => p.eval (rootCoord |(j : ℝ)| E)) ∧
      IntegrableOn (fun E => q E * p.eval (rootCoord |(j : ℝ)| E))
        (Ioo L cell.right) (referenceMeasure j) := by
  obtain ⟨hsigned, hord, _⟩ := cellResidualMeasure_integral_coordinatePolynomial
    j L cell.right cell.node cell.density_integrable p
  exact ⟨hsigned, hord⟩

/-- Complex coordinate monomials vanish through the prescribed degree and
are integrable against the actual positive variation measure. -/
theorem InitialReferenceCell.complex_moment
    {j : ℤ} {L U : ℝ} {k : ℕ} {q : ℝ → ℝ}
    (cell : InitialReferenceCell j L U k q) (m : ℕ) (hm : m ≤ k) :
    cell.residual.Integrable (fun E => (rootCoord |(j : ℝ)| E : ℂ) ^ m) ∧
      (∫ᵛ E, (rootCoord |(j : ℝ)| E : ℂ) ^ m ∂<•cell.residual) = 0 := by
  obtain ⟨hi, hz⟩ := cell.moment (Polynomial.X ^ m) (by simpa using hm)
  have hir : cell.residual.Integrable (fun E => rootCoord |(j : ℝ)| E ^ m) := by
    simpa only [InitialReferenceCell.residual, Polynomial.eval_pow, Polynomial.eval_X] using hi
  have hzr : (∫ᵛ E, rootCoord |(j : ℝ)| E ^ m ∂<•cell.residual) = 0 := by
    simpa only [InitialReferenceCell.residual, Polynomial.eval_pow, Polynomial.eval_X] using hz
  constructor
  · change Integrable (fun E => (rootCoord |(j : ℝ)| E : ℂ) ^ m) cell.residual.variation
    exact hir.ofReal.congr (Filter.Eventually.of_forall (fun E =>
      Complex.ofReal_pow (rootCoord |(j : ℝ)| E) m))
  · have h := signedIntegral_complex_ofReal hir
    rw [hzr, Complex.ofReal_zero] at h
    simpa only [Complex.ofReal_pow] using h

/-- Matching the signed integer mass bounds residual variation by twice
the absolute ordinary continuum mass. -/
theorem InitialReferenceCell.variation_le_twice_abs_mass
    {j : ℤ} {L U : ℝ} {k : ℕ} {q : ℝ → ℝ}
    (cell : InitialReferenceCell j L U k q) :
    cell.residual.variation.real univ ≤
      2 * ∫ E in Ioo L cell.right, |q E| ∂referenceMeasure j :=
  cellResidualMeasure_variation_le_twice_abs_mass j L cell.right cell.node
    cell.density_integrable cell.mass_eq

/-- The unit-node count is controlled by absolute continuum mass, without
requiring nonnegativity of the continuum being replaced. -/
theorem InitialReferenceCell.count_le_abs_mass
    {j : ℤ} {L U : ℝ} {k : ℕ} {q : ℝ → ℝ}
    (cell : InitialReferenceCell j L U k q) :
    (cell.count : ℝ) ≤ ∫ E in Ioo L cell.right, |q E| ∂referenceMeasure j := by
  rw [← cell.mass_eq]
  exact integral_mono cell.density_integrable cell.density_integrable.abs (fun E => le_abs_self _)

/-- The physical signed initial-cell endpoint theorem supplies an actual
finite residual with all support and moment facts proved. -/
theorem nonempty_initialReferenceCell_of_reserve
    (j : ℤ) {L U A Nminus : ℝ} {k : ℕ}
    (hL : |(j : ℝ)| ≤ L) (hLU : L < U) (hA : 0 ≤ A)
    (q : ℝ → ℝ) (hq : IntegrableOn q (Ioo L (U + 1)) (referenceMeasure j))
    (hnegative : (∫ E in Ioo L (U + 1), max (-q E) 0 ∂referenceMeasure j) ≤ Nminus)
    (hupper : ∀ x ∈ Icc ((rootCoord |(j : ℝ)| L + rootCoord |(j : ℝ)| U) / 2)
        (rootCoord |(j : ℝ)| (U + 1)), A ≤ cellCoordinateDensity j q x)
    (hincrement : 1 < ∫ E in Ioo U (U + 1), q E ∂referenceMeasure j)
    (hreserve : 1 / 2 < initialCellVariationReserve (rootCoord |(j : ℝ)| L)
      (rootCoord |(j : ℝ)| U) A Nminus k) :
    Nonempty (InitialReferenceCell j L U k q) := by
  obtain ⟨V, hV, N, hN, hmass, node, hnode, hmoment⟩ :=
    exists_physical_initialCell_integer_endpoint_unit_nodes j hL hLU (by linarith) hA
      q hq hnegative hupper hincrement hreserve
  have hqV : IntegrableOn q (Ioo L V) (referenceMeasure j) :=
    hq.mono_set (Ioo_subset_Ioo le_rfl hV.2)
  refine ⟨{
    right := V
    right_mem := hV
    count := N
    count_pos := hN
    node := node
    node_mem := fun i => Ioo_subset_Icc_self (hnode i)
    node_strict := hnode
    density_integrable := hqV
    mass_eq := hmass
    residual_mass := ?_
    residual_support := cellResidualMeasure_variation_compl_Icc j L V node hqV
      (fun i => Ioo_subset_Icc_self (hnode i))
    moment := ?_ }⟩
  · rw [cellResidualMeasure_univ j L V node hqV, hmass, sub_self]
  · intro p hp
    obtain ⟨hi, _, hz⟩ := cellResidualMeasure_coordinatePolynomial_eq_zero
      j L V node hqV p ((hmoment p).2 hp)
    exact ⟨hi, hz⟩

end GapFamily.Construction
