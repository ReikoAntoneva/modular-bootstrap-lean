import GapFamily.Construction.CellCoordinateIntegral
import GapFamily.Construction.CellCoordinateNodes
import GapFamily.Construction.CellCoordinateBound
import GapFamily.Construction.CellCoordinateWindow

/-!
# Actual physical cells from square-root-coordinate quadrature

The input density is an ordinary signed numerator against the physical
reference measure. The constructed atoms remain indexed by exactly `Fin N`.
The lower bound and the two explicit numerical reserves remain hypotheses.
-/

noncomputable section

open Set MeasureTheory Real
open GapFamily.Analytic
open scoped BigOperators

namespace GapFamily.Construction

/-- Integer mass and exact unit nodes for an actual physical signed cell.
Both the mass and all polynomial moments are ordinary convergent integrals
against the physical reference measure. -/
theorem exists_physical_cell_unit_nodes
    (j : ℤ) {L U W A B : ℝ} {k : ℕ}
    (hL : |(j : ℝ)| ≤ L) (hLU : L < U) (hUW : U ≤ W) (hA : 0 ≤ A)
    (q : ℝ → ℝ) (hq : IntegrableOn q (Ioo L W) (referenceMeasure j))
    (hbound : ∀ x ∈ Icc (rootCoord |(j : ℝ)| L) (rootCoord |(j : ℝ)| W),
      A*x^2-B ≤ cellCoordinateDensity j q x)
    (hterminal : 1 < (A*(U-|(j : ℝ)|)-B)*
      (rootCoord |(j : ℝ)| W-rootCoord |(j : ℝ)| U))
    (hreserve : 1/2 <
      (A*(cellCoordinateLength |(j : ℝ)| L U)^2/(8192*((k : ℝ)+1)^6)-B)*
        cellCoordinateLength |(j : ℝ)| L U/(64*((k : ℝ)+1)^6)) :
    ∃ V ∈ Icc U W, ∃ N : ℕ, 0 < N ∧
      (∫ E in Ioo L V, q E ∂referenceMeasure j) = (N : ℝ) ∧
      ∃ node : Fin N → ℝ, (∀ i, node i ∈ Icc L V) ∧
        ∀ p : Polynomial ℝ,
          IntegrableOn (fun E => q E * p.eval (rootCoord |(j : ℝ)| E))
            (Ioo L V) (referenceMeasure j) ∧
          (p.natDegree ≤ k → ∑ i, p.eval (rootCoord |(j : ℝ)| (node i)) =
            ∫ E in Ioo L V, q E * p.eval (rootCoord |(j : ℝ)| E) ∂referenceMeasure j) := by
  have hU := hL.trans hLU.le
  have hW := hU.trans hUW
  have hcoordLU := rootCoord_lt_rootCoord |(j : ℝ)| hL hLU
  have hcoordUW : rootCoord |(j : ℝ)| U ≤ rootCoord |(j : ℝ)| W :=
    sqrt_le_sqrt (sub_le_sub_right hUW _)
  have hf := (cellCoordinateDensity_intervalIntegrable_iff j hL (hLU.le.trans hUW) q).2 hq
  have hterminal' : 1 < (A*(rootCoord |(j : ℝ)| U)^2-B)*
      (rootCoord |(j : ℝ)| W-rootCoord |(j : ℝ)| U) := by
    simpa only [rootCoord, sq_sqrt (sub_nonneg.mpr hU)] using hterminal
  obtain ⟨v, hv, N, hN, hmass, node, hnode, hmoment⟩ :=
    exists_signed_cell_of_quadratic_variable_window (rootCoord_nonneg _ _)
      hcoordLU hcoordUW hA (cellCoordinateDensity j q) hf hbound hterminal' hreserve
  have hv0 := (rootCoord_nonneg |(j : ℝ)| U).trans hv.1
  have hV := energyCoord_mem_Icc |(j : ℝ)| hU hW hv
  have hLV : L ≤ energyCoord |(j : ℝ)| v := hLU.le.trans hV.1
  have hrootV := rootCoord_energyCoord |(j : ℝ)| hv0
  have hnode' : ∀ i, node i ∈ Icc (rootCoord |(j : ℝ)| L)
      (rootCoord |(j : ℝ)| (energyCoord |(j : ℝ)| v)) := by
    simpa only [hrootV] using hnode
  have hfV := (cellCoordinateDensity_intervalIntegrable_iff j hL hLV q).2
    (hq.mono_set (Ioo_subset_Ioo le_rfl hV.2))
  refine ⟨energyCoord |(j : ℝ)| v, hV, N, hN, ?_,
    physicalCellNode |(j : ℝ)| node,
    physicalCellNode_mem hL (hL.trans hLV) node hnode', ?_⟩
  · have ht := intervalIntegral_cellCoordinateDensity j hL hLV q
    rw [hrootV] at ht
    exact ht.symm.trans hmass
  · intro p
    constructor
    · apply (cellCoordinateDensity_mul_intervalIntegrable_iff j hL hLV q p.eval).1
      simpa only [mul_comm] using hfV.continuousOn_mul p.continuous.continuousOn
    · intro hp
      rw [physicalCellNode_test_sum node hnode' p.eval, hmoment p hp]
      have ht := intervalIntegral_cellCoordinateDensity_mul j hL hLV q p.eval
      rw [hrootV] at ht
      simpa only [mul_comm] using ht

/-- A lower bound on the physical numerator supplies the transformed C3
hypothesis, retaining the vanishing edge factor and the reference denominator. -/
theorem cellCoordinateDensity_lower_bound_of_numerator
    (j : ℤ) {L W c P H : ℝ} (hLpos : 0 < L) (hL : |(j : ℝ)| ≤ L)
    (hLW : L ≤ W) (hc : 0 ≤ c) (hP : 0 ≤ P) (hH : 0 ≤ H)
    (q : ℝ → ℝ)
    (hbound : ∀ E ∈ Icc L W, c*(E^2-(j : ℝ)^2)*P-H ≤ q E) :
    ∀ x ∈ Icc (rootCoord |(j : ℝ)| L) (rootCoord |(j : ℝ)| W),
      (2*c*P*sqrt L)*x^2-2*H/sqrt L ≤ cellCoordinateDensity j q x := by
  intro x hx
  have hE := energyCoord_mem_Icc |(j : ℝ)| hL (hL.trans hLW) hx
  have hnum : c*((|(j : ℝ)|+x^2)^2-|(j : ℝ)|^2)*P-H ≤
      q (|(j : ℝ)|+x^2) := by
    simpa only [energyCoord, sq_abs] using hbound _ hE
  exact coordinate_density_quadratic_lower_bound (abs_nonneg _) hLpos hE.1 hc hP hH q hnum

/-- The physical numerator lower bound, together with two explicit scalar
inequalities, produces a positive integer mass endpoint and exactly that many
unit nodes in physical energy. No transformed-density hypothesis is left. -/
theorem exists_physical_cell_unit_nodes_of_numerator_lower_bound
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
    ∃ V ∈ Icc U W, ∃ N : ℕ, 0 < N ∧
      (∫ E in Ioo L V, q E ∂referenceMeasure j) = (N : ℝ) ∧
      ∃ node : Fin N → ℝ, (∀ i, node i ∈ Icc L V) ∧
        ∀ p : Polynomial ℝ,
          IntegrableOn (fun E => q E * p.eval (rootCoord |(j : ℝ)| E))
            (Ioo L V) (referenceMeasure j) ∧
          (p.natDegree ≤ k → ∑ i, p.eval (rootCoord |(j : ℝ)| (node i)) =
            ∫ E in Ioo L V, q E * p.eval (rootCoord |(j : ℝ)| E) ∂referenceMeasure j) := by
  apply exists_physical_cell_unit_nodes j hL hLU hUW (by positivity) q hq
    (cellCoordinateDensity_lower_bound_of_numerator j hLpos hL (hLU.le.trans hUW)
      hc hP hH q hbound) hterminal hreserve

end GapFamily.Construction
