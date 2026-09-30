import GapFamily.Analytic.Foundation.SignedMomentIntegral
import GapFamily.Analytic.Foundation.ReferenceMeasure
import GapFamily.Construction.CellCoordinateGeometry
import GapFamily.Construction.CellCoordinateSignedDensity
import Mathlib.MeasureTheory.VectorMeasure.WithDensity

/-!
# The signed residual measure of a physical cell

The atomic part consists of exactly the prescribed finite list of unit atoms.
The continuous part is the actual signed density against the restricted
physical reference measure. Integrability is proved before using its integral.
-/

noncomputable section

open MeasureTheory Set
open scoped BigOperators Classical
open GapFamily.Analytic

namespace GapFamily.Construction

/-- A finite list of unit atoms, retaining multiplicity when nodes coincide. -/
def unitAtomSignedMeasure {N : ℕ} (node : Fin N → ℝ) : SignedMeasure ℝ :=
  ∑ i, (Measure.dirac (node i)).toSignedMeasure

/-- The physical signed residual: prescribed unit atoms minus the ordinary
signed numerator on the open energy cell. -/
def cellResidualMeasure {N : ℕ} (j : ℤ) (L V : ℝ) (q : ℝ → ℝ)
    (node : Fin N → ℝ) : SignedMeasure ℝ :=
  unitAtomSignedMeasure node -
    ((referenceMeasure j).restrict (Ioo L V)).withDensityᵥ q

theorem unitAtomSignedMeasure_integrable {N : ℕ} (node : Fin N → ℝ)
    (f : ℝ → ℝ) : (unitAtomSignedMeasure node).Integrable f := by
  apply VectorMeasure.Integrable.finsetSum_vectorMeasure
  intro i hi
  simpa only [VectorMeasure.Integrable, Measure.variation_toSignedMeasure] using
    (integrable_dirac (by finiteness) : Integrable f (Measure.dirac (node i)))

/-- Integration against the atomic part is the literal finite unit-weight sum. -/
theorem integral_unitAtomSignedMeasure {N : ℕ} (node : Fin N → ℝ)
    (f : ℝ → ℝ) :
    (∫ᵛ E, f E ∂<•unitAtomSignedMeasure node) = ∑ i, f (node i) := by
  unfold unitAtomSignedMeasure
  rw [VectorMeasure.integral_finsetSum_vectorMeasure]
  · simp only [VectorMeasure.integral_toSignedMeasure, integral_dirac]
  · intro i hi
    simpa only [VectorMeasure.Integrable, Measure.variation_toSignedMeasure] using
      (integrable_dirac (by finiteness) : Integrable f (Measure.dirac (node i)))

theorem unitAtomSignedMeasure_apply {N : ℕ} (node : Fin N → ℝ)
    {s : Set ℝ} (hs : MeasurableSet s) :
    unitAtomSignedMeasure node s = ∑ i, if node i ∈ s then (1 : ℝ) else 0 := by
  simp [unitAtomSignedMeasure, Measure.toSignedMeasure_apply_measurable hs,
    Set.indicator_apply]

/-- The residual is the literal atom count minus the signed physical mass
on every measurable set. -/
theorem cellResidualMeasure_apply {N : ℕ} (j : ℤ) (L V : ℝ)
    {q : ℝ → ℝ} (node : Fin N → ℝ)
    (hq : Integrable q ((referenceMeasure j).restrict (Ioo L V)))
    {s : Set ℝ} (hs : MeasurableSet s) :
    cellResidualMeasure j L V q node s =
      (∑ i, if node i ∈ s then (1 : ℝ) else 0) -
        ∫ E in s, q E ∂(referenceMeasure j).restrict (Ioo L V) := by
  change unitAtomSignedMeasure node s -
    ((referenceMeasure j).restrict (Ioo L V)).withDensityᵥ q s = _
  rw [unitAtomSignedMeasure_apply node hs, withDensityᵥ_apply hq hs]

/-- The physical cell measure is concentrated on the closed cell, including
when the reference measure of the cell is infinite. -/
theorem referenceMeasure_cell_ae_mem_Icc (j : ℤ) (L V : ℝ) :
    ∀ᵐ E ∂(referenceMeasure j).restrict (Ioo L V), E ∈ Icc L V := by
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with E hE
  exact ⟨hE.1.le, hE.2.le⟩

/-- Compactness supplies the genuine bound for every continuous test function
on the physical cell. -/
theorem referenceMeasure_cell_continuous_bounded (j : ℤ) (L V : ℝ)
    {f : ℝ → ℝ} (hf : Continuous f) :
    ∃ C : ℝ, ∀ᵐ E ∂(referenceMeasure j).restrict (Ioo L V), ‖f E‖ ≤ C := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hf.continuousOn
  exact ⟨C, (referenceMeasure_cell_ae_mem_Icc j L V).mono (fun E hE => hC E hE)⟩

/-- No part of the signed residual, even in total variation, lies outside the
closed cell when its actual atoms lie in that cell. -/
theorem cellResidualMeasure_variation_compl_Icc {N : ℕ} (j : ℤ) (L V : ℝ)
    {q : ℝ → ℝ} (node : Fin N → ℝ)
    (hq : Integrable q ((referenceMeasure j).restrict (Ioo L V)))
    (hnode : ∀ i, node i ∈ Icc L V) :
    (cellResidualMeasure j L V q node).variation (Icc L V)ᶜ = 0 := by
  apply (VectorMeasure.variation_apply_eq_zero measurableSet_Icc.compl).mpr
  intro s hs hsm
  rw [cellResidualMeasure_apply j L V node hq hsm]
  have hn : ∀ i, node i ∉ s := fun i hi => hs hi (hnode i)
  have hnull : (referenceMeasure j).restrict (Ioo L V) s = 0 := by
    rw [Measure.restrict_apply hsm]
    have he : s ∩ Ioo L V = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro E hE
      exact hs hE.1 ⟨hE.2.1.le, hE.2.2.le⟩
    rw [he, measure_empty]
  have hi : (∫ E in s, q E ∂(referenceMeasure j).restrict (Ioo L V)) = 0 := by
    rw [Measure.restrict_zero_set hnull, integral_zero_measure]
  simp [hn, hi]

/-- Every continuous test is genuinely integrable against the cell residual,
and its signed integral is the finite atomic sum minus the ordinary density
integral. No integrability of the unweighted reference measure is assumed. -/
theorem cellResidualMeasure_integral_continuous {N : ℕ} (j : ℤ) (L V : ℝ)
    {q f : ℝ → ℝ} (node : Fin N → ℝ)
    (hq : Integrable q ((referenceMeasure j).restrict (Ioo L V)))
    (hf : Continuous f) :
    (cellResidualMeasure j L V q node).Integrable f ∧
    Integrable (fun E => q E * f E) ((referenceMeasure j).restrict (Ioo L V)) ∧
    (∫ᵛ E, f E ∂<•cellResidualMeasure j L V q node) =
      (∑ i, f (node i)) - ∫ E in Ioo L V, q E * f E ∂referenceMeasure j := by
  obtain ⟨C, hC⟩ := referenceMeasure_cell_continuous_bounded j L V hf
  obtain ⟨hν, hprod, hint⟩ := signedDensity_integral_of_norm_bdd hq
    hf.aestronglyMeasurable hC
  refine ⟨(unitAtomSignedMeasure_integrable node f).sub_vectorMeasure hν, hprod, ?_⟩
  unfold cellResidualMeasure
  rw [VectorMeasure.integral_sub_vectorMeasure (unitAtomSignedMeasure_integrable node f) hν,
    integral_unitAtomSignedMeasure, hint]

/-- The mass balance is the prescribed integer atom count minus the actual
signed physical mass of the cell. -/
theorem cellResidualMeasure_univ {N : ℕ} (j : ℤ) (L V : ℝ)
    {q : ℝ → ℝ} (node : Fin N → ℝ)
    (hq : Integrable q ((referenceMeasure j).restrict (Ioo L V))) :
    cellResidualMeasure j L V q node univ =
      (N : ℝ) - ∫ E in Ioo L V, q E ∂referenceMeasure j := by
  rw [cellResidualMeasure_apply j L V node hq MeasurableSet.univ]
  simp

/-- A polynomial in the literal square-root coordinate is a continuous
physical-energy test. -/
theorem continuous_cellCoordinate_polynomial (j : ℤ) (p : Polynomial ℝ) :
    Continuous (fun E => p.eval (rootCoord |(j : ℝ)| E)) := by
  apply p.continuous.comp
  exact Real.continuous_sqrt.comp (continuous_id.sub continuous_const)

/-- The actual signed polynomial moment of the physical cell residual equals
the difference between its unit-node sum and its ordinary physical integral. -/
theorem cellResidualMeasure_integral_coordinatePolynomial {N : ℕ} (j : ℤ) (L V : ℝ)
    {q : ℝ → ℝ} (node : Fin N → ℝ)
    (hq : Integrable q ((referenceMeasure j).restrict (Ioo L V)))
    (p : Polynomial ℝ) :
    (cellResidualMeasure j L V q node).Integrable
        (fun E => p.eval (rootCoord |(j : ℝ)| E)) ∧
    Integrable (fun E => q E * p.eval (rootCoord |(j : ℝ)| E))
        ((referenceMeasure j).restrict (Ioo L V)) ∧
    (∫ᵛ E, p.eval (rootCoord |(j : ℝ)| E) ∂<•cellResidualMeasure j L V q node) =
      (∑ i, p.eval (rootCoord |(j : ℝ)| (node i))) -
        ∫ E in Ioo L V, q E * p.eval (rootCoord |(j : ℝ)| E) ∂referenceMeasure j :=
  cellResidualMeasure_integral_continuous j L V node hq
    (continuous_cellCoordinate_polynomial j p)

/-- An exact unit-node quadrature identity cancels the corresponding actual
signed coordinate moment. Both signed and ordinary integrability are proved. -/
theorem cellResidualMeasure_coordinatePolynomial_eq_zero {N : ℕ} (j : ℤ) (L V : ℝ)
    {q : ℝ → ℝ} (node : Fin N → ℝ)
    (hq : Integrable q ((referenceMeasure j).restrict (Ioo L V)))
    (p : Polynomial ℝ)
    (hm : (∑ i, p.eval (rootCoord |(j : ℝ)| (node i))) =
      ∫ E in Ioo L V, q E * p.eval (rootCoord |(j : ℝ)| E) ∂referenceMeasure j) :
    (cellResidualMeasure j L V q node).Integrable
        (fun E => p.eval (rootCoord |(j : ℝ)| E)) ∧
    Integrable (fun E => q E * p.eval (rootCoord |(j : ℝ)| E))
        ((referenceMeasure j).restrict (Ioo L V)) ∧
    (∫ᵛ E, p.eval (rootCoord |(j : ℝ)| E) ∂<•cellResidualMeasure j L V q node) = 0 := by
  obtain ⟨hi, hp, he⟩ := cellResidualMeasure_integral_coordinatePolynomial j L V node hq p
  exact ⟨hi, hp, by rw [he, hm, sub_self]⟩

/-- The real coordinate moment identity also cancels the corresponding complex
moment, with actual variation integrability in both scalar fields. -/
theorem cellResidualMeasure_coordinate_moment_eq_zero {N : ℕ} (j : ℤ) (L V : ℝ)
    {q : ℝ → ℝ} (node : Fin N → ℝ)
    (hq : Integrable q ((referenceMeasure j).restrict (Ioo L V))) (n : ℕ)
    (hm : (∑ i, rootCoord |(j : ℝ)| (node i) ^ n) =
      ∫ E in Ioo L V, q E * rootCoord |(j : ℝ)| E ^ n ∂referenceMeasure j) :
    (cellResidualMeasure j L V q node).Integrable
        (fun E => rootCoord |(j : ℝ)| E ^ n) ∧
    (cellResidualMeasure j L V q node).Integrable
        (fun E => (rootCoord |(j : ℝ)| E : ℂ) ^ n) ∧
    (∫ᵛ E, (rootCoord |(j : ℝ)| E : ℂ) ^ n ∂<•cellResidualMeasure j L V q node) = 0 := by
  have hc : Continuous (fun E => rootCoord |(j : ℝ)| E ^ n) :=
    (Real.continuous_sqrt.comp (continuous_id.sub continuous_const)).pow n
  obtain ⟨hi, _, he⟩ := cellResidualMeasure_integral_continuous j L V node hq hc
  have hz : (∫ᵛ E, rootCoord |(j : ℝ)| E ^ n
      ∂<•cellResidualMeasure j L V q node) = 0 := by
    rw [he, hm, sub_self]
  refine ⟨hi, ?_, ?_⟩
  · change Integrable (fun E => (rootCoord |(j : ℝ)| E : ℂ) ^ n)
      (cellResidualMeasure j L V q node).variation
    exact hi.ofReal.congr (Filter.Eventually.of_forall (fun E =>
      Complex.ofReal_pow (rootCoord |(j : ℝ)| E) n))
  · have h := signedIntegral_complex_ofReal hi
    rw [hz, Complex.ofReal_zero] at h
    simpa only [Complex.ofReal_pow] using h

end GapFamily.Construction
