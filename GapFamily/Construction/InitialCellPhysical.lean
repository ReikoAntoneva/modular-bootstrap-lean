import GapFamily.Construction.InitialCellEndpoint
import GapFamily.Construction.CellCoordinateIntegral
import GapFamily.Construction.CellCoordinateNodes

/-!
# Physical initial cells from the signed upper-half reserve

The negative mass is measured against the actual physical reference measure.
The square-root substitution preserves that mass exactly. Prescribed unit
nodes in the coordinate interval return to the same number of physical atoms.
-/

noncomputable section

open Set MeasureTheory Real
open GapFamily.Analytic
open scoped BigOperators

namespace GapFamily.Construction

theorem cellCoordinateDensity_negativePart (j : ℤ) (q : ℝ → ℝ) (x : ℝ) :
    cellCoordinateDensity j (fun E => max (-q E) 0) x =
      max (-cellCoordinateDensity j q x) 0 := by
  unfold cellCoordinateDensity
  have hc : 0 ≤ 2 / sqrt (x ^ 2 + 2 * |(j : ℝ)|) := by positivity
  calc
    _ = (2 / sqrt (x ^ 2 + 2 * |(j : ℝ)|)) * max (-q (energyCoord |(j : ℝ)| x)) 0 := by ring
    _ = max ((2 / sqrt (x ^ 2 + 2 * |(j : ℝ)|)) * (-q (energyCoord |(j : ℝ)| x))) 0 := by
      rw [mul_max_of_nonneg _ _ hc, mul_zero]
    _ = _ := by congr 1; ring

/-- Total negative mass is invariant under the actual coordinate transport. -/
theorem initialCellNegativeMass_coordinate_eq (j : ℤ) {L V : ℝ}
    (hL : |(j : ℝ)| ≤ L) (hLV : L ≤ V) (q : ℝ → ℝ) :
    initialCellNegativeMass (rootCoord |(j : ℝ)| L) (rootCoord |(j : ℝ)| V)
      (cellCoordinateDensity j q) =
      ∫ E in Ioo L V, max (-q E) 0 ∂referenceMeasure j := by
  unfold initialCellNegativeMass
  simp_rw [← cellCoordinateDensity_negativePart]
  exact intervalIntegral_cellCoordinateDensity j hL hLV _

/-- A physical signed initial cell with integer mass has exactly that many
unit atoms when its upper-half coordinate density has the explicit reserve. -/
theorem exists_physical_initialCell_unit_nodes
    (j : ℤ) {L V A Nminus : ℝ} {k N : ℕ}
    (hL : |(j : ℝ)| ≤ L) (hLV : L < V) (hA : 0 ≤ A)
    (q : ℝ → ℝ) (hq : IntegrableOn q (Ioo L V) (referenceMeasure j))
    (hnegative : (∫ E in Ioo L V, max (-q E) 0 ∂referenceMeasure j) ≤ Nminus)
    (hupper : ∀ x ∈ Icc ((rootCoord |(j : ℝ)| L + rootCoord |(j : ℝ)| V) / 2)
        (rootCoord |(j : ℝ)| V), A ≤ cellCoordinateDensity j q x)
    (hN : 0 < N) (hmass : (∫ E in Ioo L V, q E ∂referenceMeasure j) = (N : ℝ))
    (hreserve : 1 / 2 < initialCellVariationReserve (rootCoord |(j : ℝ)| L)
      (rootCoord |(j : ℝ)| V) A Nminus k) :
    ∃ node : Fin N → ℝ, (∀ i, node i ∈ Ioo L V) ∧
      ∀ p : Polynomial ℝ,
        IntegrableOn (fun E => q E * p.eval (rootCoord |(j : ℝ)| E))
          (Ioo L V) (referenceMeasure j) ∧
        (p.natDegree ≤ k → ∑ i, p.eval (rootCoord |(j : ℝ)| (node i)) =
          ∫ E in Ioo L V, q E * p.eval (rootCoord |(j : ℝ)| E) ∂referenceMeasure j) := by
  have hcoord := rootCoord_lt_rootCoord |(j : ℝ)| hL hLV
  have hf := (cellCoordinateDensity_intervalIntegrable_iff j hL hLV.le q).2 hq
  have hnegative' : initialCellNegativeMass (rootCoord |(j : ℝ)| L) (rootCoord |(j : ℝ)| V)
      (cellCoordinateDensity j q) ≤ Nminus := by
    rwa [initialCellNegativeMass_coordinate_eq j hL hLV.le]
  have hmass' : (∫ x in rootCoord |(j : ℝ)| L..rootCoord |(j : ℝ)| V,
      cellCoordinateDensity j q x) = (N : ℝ) :=
    (intervalIntegral_cellCoordinateDensity j hL hLV.le q).trans hmass
  obtain ⟨node, hnode, hmoment⟩ := exists_initialCell_unit_nodes hcoord hA
    (cellCoordinateDensity j q) hf hnegative' hupper hN hmass' hreserve
  refine ⟨physicalCellNode |(j : ℝ)| node,
    physicalCellNode_mem_Ioo hL (hL.trans hLV.le) node hnode, ?_⟩
  intro p
  constructor
  · apply (cellCoordinateDensity_mul_intervalIntegrable_iff j hL hLV.le q p.eval).1
    simpa only [mul_comm] using hf.continuousOn_mul p.continuous.continuousOn
  · intro hp
    rw [physicalCellNode_test_sum node (fun i => Ioo_subset_Icc_self (hnode i)) p.eval,
      hmoment p hp]
    simpa only [mul_comm] using intervalIntegral_cellCoordinateDensity_mul j hL hLV.le q p.eval

/-- A terminal physical mass increment and the shortest initial-cell reserve
select an integer endpoint and exactly its mass of physical unit atoms. -/
theorem exists_physical_initialCell_integer_endpoint_unit_nodes
    (j : ℤ) {L U W A Nminus : ℝ} {k : ℕ}
    (hL : |(j : ℝ)| ≤ L) (hLU : L < U) (hUW : U ≤ W) (hA : 0 ≤ A)
    (q : ℝ → ℝ) (hq : IntegrableOn q (Ioo L W) (referenceMeasure j))
    (hnegative : (∫ E in Ioo L W, max (-q E) 0 ∂referenceMeasure j) ≤ Nminus)
    (hupper : ∀ x ∈ Icc ((rootCoord |(j : ℝ)| L + rootCoord |(j : ℝ)| U) / 2)
        (rootCoord |(j : ℝ)| W), A ≤ cellCoordinateDensity j q x)
    (hincrement : 1 < ∫ E in Ioo U W, q E ∂referenceMeasure j)
    (hreserve : 1 / 2 < initialCellVariationReserve (rootCoord |(j : ℝ)| L)
      (rootCoord |(j : ℝ)| U) A Nminus k) :
    ∃ V ∈ Icc U W, ∃ N : ℕ, 0 < N ∧
      (∫ E in Ioo L V, q E ∂referenceMeasure j) = (N : ℝ) ∧
      ∃ node : Fin N → ℝ, (∀ i, node i ∈ Ioo L V) ∧
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
  have hnegative' : initialCellNegativeMass (rootCoord |(j : ℝ)| L) (rootCoord |(j : ℝ)| W)
      (cellCoordinateDensity j q) ≤ Nminus := by
    rwa [initialCellNegativeMass_coordinate_eq j hL (hLU.le.trans hUW)]
  have hincrement' : 1 < ∫ x in rootCoord |(j : ℝ)| U..rootCoord |(j : ℝ)| W,
      cellCoordinateDensity j q x := by
    rwa [intervalIntegral_cellCoordinateDensity j hU hUW q]
  obtain ⟨v, hv, N, hN, hmass, node, hnode, hmoment⟩ :=
    exists_initialCell_integer_endpoint_unit_nodes hcoordLU hcoordUW hA
      (cellCoordinateDensity j q) hf hnegative' hupper hincrement' hreserve
  have hv0 := (rootCoord_nonneg |(j : ℝ)| U).trans hv.1
  have hV := energyCoord_mem_Icc |(j : ℝ)| hU hW hv
  have hLV : L ≤ energyCoord |(j : ℝ)| v := hLU.le.trans hV.1
  have hrootV := rootCoord_energyCoord |(j : ℝ)| hv0
  have hnode' : ∀ i, node i ∈ Ioo (rootCoord |(j : ℝ)| L)
      (rootCoord |(j : ℝ)| (energyCoord |(j : ℝ)| v)) := by
    simpa only [hrootV] using hnode
  have hfV := (cellCoordinateDensity_intervalIntegrable_iff j hL hLV q).2
    (hq.mono_set (Ioo_subset_Ioo le_rfl hV.2))
  refine ⟨energyCoord |(j : ℝ)| v, hV, N, hN, ?_,
    physicalCellNode |(j : ℝ)| node,
    physicalCellNode_mem_Ioo hL (hL.trans hLV) node hnode', ?_⟩
  · have ht := intervalIntegral_cellCoordinateDensity j hL hLV q
    rw [hrootV] at ht
    exact ht.symm.trans hmass
  · intro p
    constructor
    · apply (cellCoordinateDensity_mul_intervalIntegrable_iff j hL hLV q p.eval).1
      simpa only [mul_comm] using hfV.continuousOn_mul p.continuous.continuousOn
    · intro hp
      rw [physicalCellNode_test_sum node (fun i => Ioo_subset_Icc_self (hnode' i)) p.eval,
        hmoment p hp]
      have ht := intervalIntegral_cellCoordinateDensity_mul j hL hLV q p.eval
      rw [hrootV] at ht
      simpa only [mul_comm] using ht

end GapFamily.Construction
