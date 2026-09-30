import GapFamily.Construction.CellCoordinate
import GapFamily.Construction.CellCoordinateMeasure

/-!
# The actual moment-canceling signed residual of a constructed physical cell

This connects coordinate quadrature to the ordinary finite signed measure
used for local repair. The remaining lower-bound and numerical inputs are explicit.
-/

noncomputable section

open Set MeasureTheory Real
open GapFamily.Analytic
open scoped BigOperators

namespace GapFamily.Construction

/-- The complete coordinate-cell endpoint: actual prescribed unit atoms, zero
signed mass, compact variation support, and convergent vanishing coordinate
moments through the requested degree. -/
theorem exists_physical_cell_canceling_residual
    (j : ℤ) {L U W c P H : ℝ} {k : ℕ}
    (hLpos : 0 < L) (hL : |(j : ℝ)| ≤ L) (hLU : L < U) (hUW : U ≤ W)
    (hc : 0 ≤ c) (hP : 0 ≤ P) (hH : 0 ≤ H)
    (q : ℝ → ℝ) (hq : IntegrableOn q (Ioo L W) (referenceMeasure j))
    (hbound : ∀ E ∈ Icc L W, c*(E^2-(j : ℝ)^2)*P-H ≤ q E)
    (hterminal : 1 < ((2*c*P*sqrt L)*(U-|(j : ℝ)|)-2*H/sqrt L)*
      (rootCoord |(j : ℝ)| W-rootCoord |(j : ℝ)| U))
    (hreserve : 1/2 <
      ((2*c*P*sqrt L)*(cellCoordinateLength |(j : ℝ)| L U)^2/
          (8192*((k : ℝ)+1)^6)-2*H/sqrt L)*
        cellCoordinateLength |(j : ℝ)| L U/(64*((k : ℝ)+1)^6)) :
    ∃ V ∈ Icc U W, ∃ N : ℕ, 0 < N ∧ ∃ node : Fin N → ℝ,
      (∀ i, node i ∈ Icc L V) ∧
      (∫ E in Ioo L V, q E ∂referenceMeasure j) = (N : ℝ) ∧
      cellResidualMeasure j L V q node univ = 0 ∧
      (cellResidualMeasure j L V q node).variation (Icc L V)ᶜ = 0 ∧
      ∀ p : Polynomial ℝ, p.natDegree ≤ k →
        (cellResidualMeasure j L V q node).Integrable
          (fun E => p.eval (rootCoord |(j : ℝ)| E)) ∧
        (∫ᵛ E, p.eval (rootCoord |(j : ℝ)| E)
          ∂<•cellResidualMeasure j L V q node) = 0 := by
  obtain ⟨V, hV, N, hN, hmass, node, hnode, hmoment⟩ :=
    exists_physical_cell_unit_nodes_of_numerator_lower_bound j hLpos hL hLU hUW
      hc hP hH q hq hbound hterminal hreserve
  have hqV : Integrable q ((referenceMeasure j).restrict (Ioo L V)) :=
    hq.mono_set (Ioo_subset_Ioo le_rfl hV.2)
  refine ⟨V, hV, N, hN, node, hnode, hmass, ?_,
    cellResidualMeasure_variation_compl_Icc j L V node hqV hnode, ?_⟩
  · rw [cellResidualMeasure_univ j L V node hqV, hmass, sub_self]
  · intro p hp
    obtain ⟨hi, _, hz⟩ := cellResidualMeasure_coordinatePolynomial_eq_zero j L V node hqV p
      ((hmoment p).2 hp)
    exact ⟨hi, hz⟩

end GapFamily.Construction
