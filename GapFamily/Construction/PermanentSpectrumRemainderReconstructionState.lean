import GapFamily.Construction.PermanentSpectrumRemainderReconstruction
import GapFamily.Construction.FiniteRepairState

/-! The concrete finite repair state's actual Dirac measures have precisely
the row masses used in the verified unit-seed Fourier reconstruction. -/

noncomputable section
namespace GapFamily.Construction

open Set MeasureTheory

theorem unitNodeRowThermalMeasure_univ_eq_listPointSeedThermalRow (nodes : List (ℝ × ℤ)) (j : ℤ) (t : ℝ) :
    unitNodeRowThermalMeasure nodes j t univ = listPointSeedThermalRow nodes j t := by
  induction nodes with
  | nil => simp [listPointSeedThermalRow]
  | cons p nodes ih =>
    change ((if p.2 = j then VectorMeasure.dirac p.1 (Real.exp (-t * p.1)) else 0) +
      unitNodeRowThermalMeasure nodes j t) univ =
        (if j = p.2 then Real.exp (-t * p.1) else 0) + listPointSeedThermalRow nodes j t
    rw [_root_.add_apply, ih]
    by_cases hj : p.2 = j
    · simp [hj]
    · simp [hj, Ne.symm hj]

/-- Prepending the marker agrees at the actual signed-measure level. -/
theorem unitMarker_add_unitNodeRowThermalMeasure
    (b : ℝ) (nodes : List (ℝ × ℤ)) (j : ℤ) (t : ℝ) :
    unitMarkerThermalMeasure b j t + unitNodeRowThermalMeasure nodes j t =
      unitNodeRowThermalMeasure ((b, 0) :: nodes) j t := by
  simp [unitMarkerThermalMeasure, unitNodeRowThermalMeasure, eq_comm]

theorem unitMarker_add_unitNodeRowThermalMeasure_univ
    (b : ℝ) (nodes : List (ℝ × ℤ)) (j : ℤ) (t : ℝ) :
    (unitMarkerThermalMeasure b j t + unitNodeRowThermalMeasure nodes j t) univ =
      listPointSeedThermalRow ((b, 0) :: nodes) j t := by
  rw [unitMarker_add_unitNodeRowThermalMeasure, unitNodeRowThermalMeasure_univ_eq_listPointSeedThermalRow]

theorem FiniteRepairState.atomicThermalOutput_univ_eq_listPointSeedThermalRow
    (s : FiniteRepairState) (b : ℝ) (j : ℤ) (t : ℝ) :
    s.atomicThermalOutput b j t univ = listPointSeedThermalRow ((b, 0) :: s.nodes) j t :=
  unitMarker_add_unitNodeRowThermalMeasure_univ b s.nodes j t

end GapFamily.Construction
