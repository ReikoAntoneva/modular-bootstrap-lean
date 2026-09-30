import GapFamily.Construction.CanonicalRepairDatum

/-! The data of an actual finite repair stage. The modular function and its
output are computed from the concrete canonical repair history. The ordinary
continuum numerator is kept separate from the persistent unit-atom list. -/

noncomputable section
namespace GapFamily.Construction
open Set MeasureTheory Analytic
open scoped BigOperators

/-- A finite state stores actual local repair inputs, row fronts, unit atom
occurrences other than the fixed marker, and the ordinary continuum numerator. -/
structure FiniteRepairState where
  front : ℤ → ℝ
  nodes : List (ℝ × ℤ)
  numerator : ℤ → ℝ → ℝ
  history : List CanonicalRepairDatum

/-- The literal thermal signed measure of the unit atoms on one output row. -/
def unitNodeRowThermalMeasure (nodes : List (ℝ × ℤ)) (j : ℤ) (t : ℝ) : SignedMeasure ℝ :=
  (nodes.map (fun p => if p.2 = j then
    VectorMeasure.dirac p.1 (Real.exp (-t * p.1)) else 0)).sum

@[simp] theorem unitNodeRowThermalMeasure_nil (j : ℤ) (t : ℝ) :
    unitNodeRowThermalMeasure [] j t = 0 := rfl

theorem unitNodeRowThermalMeasure_append (left right : List (ℝ × ℤ)) (j : ℤ) (t : ℝ) :
    unitNodeRowThermalMeasure (left ++ right) j t =
      unitNodeRowThermalMeasure left j t + unitNodeRowThermalMeasure right j t := by
  simp [unitNodeRowThermalMeasure]

/-- A cell's literal list and its finite Dirac sum retain exactly the same
unit multiplicities, including repeated nodes. -/
theorem unitNodeRowThermalMeasure_ofFn {N : ℕ} (node : Fin N → ℝ)
    (J j : ℤ) (t : ℝ) :
    unitNodeRowThermalMeasure (List.ofFn (fun i => (node i, J))) j t =
      if j = J then ∑ i, VectorMeasure.dirac (node i) (Real.exp (-t * node i)) else 0 := by
  by_cases hj : j = J
  · subst j
    simp [unitNodeRowThermalMeasure, Function.comp_def, List.sum_ofFn]
  · simp [unitNodeRowThermalMeasure, Function.comp_def, hj, Ne.symm hj]

/-- The fixed scalar marker is never included in a subtracted continuum. -/
def unitMarkerThermalMeasure (b : ℝ) (j : ℤ) (t : ℝ) : SignedMeasure ℝ :=
  if j = 0 then VectorMeasure.dirac b (Real.exp (-t * b)) else 0

namespace FiniteRepairState

/-- The complete retained atom measure: fixed marker and actual unit-node list. -/
def atomicThermalOutput (s : FiniteRepairState) (b : ℝ) (j : ℤ) (t : ℝ) : SignedMeasure ℝ :=
  unitMarkerThermalMeasure b j t + unitNodeRowThermalMeasure s.nodes j t

/-- Ordinary continuum output of the stored numerator, with no threshold atom. -/
def continuumThermalOutput (s : FiniteRepairState) (j : ℤ) (t : ℝ) : SignedMeasure ℝ :=
  (referenceMeasure j).withDensityᵥ (fun E => Real.exp (-t * E) * s.numerator j E)

/-- Genuine thermal integrability is required on every row and every positive
thermal parameter; totalized density measures are not used as a substitute. -/
def ThermalIntegrable (s : FiniteRepairState) : Prop :=
  ∀ (j : ℤ) (t : ℝ), 0 < t →
    Integrable (fun E => Real.exp (-t * E) * s.numerator j E) (referenceMeasure j)

/-- Only the physical cleared region has zero continuum. -/
def Cleared (s : FiniteRepairState) : Prop :=
  ∀ (j : ℤ) (E : ℝ), |(j : ℝ)| ≤ E → E < s.front j → s.numerator j E = 0

/-- The actual density with a moving unprocessed cutoff agrees almost
everywhere with the stored continuum whenever the cleared invariant holds. -/
theorem numerator_eq_unprocessed_ae (s : FiniteRepairState) (hc : s.Cleared) (j : ℤ) :
    s.numerator j =ᵐ[referenceMeasure j]
      (Ici (s.front j)).indicator (s.numerator j) := by
  filter_upwards [referenceMeasure_ae_above_edge j] with E hE
  by_cases hfront : s.front j ≤ E
  · simp [hfront]
  · have hzero := hc j E hE.le (lt_of_not_ge hfront)
    simp [hfront, hzero]

end FiniteRepairState
end GapFamily.Construction
