import GapFamily.Construction.RealInitialStateGeometry
import GapFamily.Construction.RealInitialStateOutput
import GapFamily.Construction.RealInitialStateBudget
import GapFamily.Construction.RealInitialRow
import GapFamily.Construction.RealConstructionEndpoint

/-!
# Full spectra from actual initial cells

The same literal initial cell history supplies all finite-state predicates
needed by the recursive tail endpoint. The marker can lie anywhere below
the initial cutoff, including zero; its position does not affect the
selection of the tail layer or the physical clearing front.
-/

noncomputable section

open Set Filter MeasureTheory Real
open GapFamily.Analytic
open scoped BigOperators

namespace GapFamily.Construction

/-- Actual finite cells, a reference output, and the two numerical error
budgets yield a fully admissible spectrum with exactly one scalar first
primary. All infinite recursion and convergence predicates are discharged. -/
theorem exists_spectrum_of_real_initial_cells
    {c δ b U A : ℝ} {T k : ℕ} {degree : ℕ → ℕ}
    (d : RealTailLocalData (shift c) U T degree)
    (ref : ReferenceOutput (shift c)) (q : ℤ → ℝ → ℝ)
    (cells : ∀ J : realInitialRows A,
      InitialReferenceCell J (max b |(J : ℝ)|) U k (q J))
    (hδ : 0 ≤ δ) (hδb : δ ≤ b) (hδT : δ < (T : ℝ))
    (ha : 100 ≤ shift c) (hT : 1 ≤ T)
    (hU : 0 ≤ U) (hA : 0 ≤ A) (hAU : A ≤ U) (hTA : (T : ℝ) ≤ A)
    (hqthermal : ∀ (j : ℤ) (t : ℝ), 0 < t →
      Integrable (fun e => exp (-t * e) * q j e) (referenceMeasure j))
    (hqzero : ∀ j : ℤ, ∀ᵐ e ∂referenceMeasure j, e < max b |(j : ℝ)| → q j e = 0)
    (href : ∀ (j : ℤ) (t : ℝ), 0 < t → ref.thermalOutput j t = unitMarkerThermalMeasure δ j t +
      (referenceMeasure j).withDensityᵥ (fun e => exp (-t * e) * q j e))
    (herr : ∀ (j : ℤ) (e : ℝ), max A |(j : ℝ)| ≤ e →
      |q j e - vacuumLeading (shift c) e j| ≤ exp (7 * sqrt (shift c * e)) / 2)
    (hrepair : ∀ (j : ℤ) (e : ℝ), |(j : ℝ)| ≤ e →
      (∑ J, |if 2 * U + 4 < e then
        (cells J).exteriorNumerator (2 * U + 4) (by linarith) j e else 0|) ≤
        exp (7 * sqrt (shift c * e)) / 8) :
    ∃ spectrum : Spectrum, PureAdmissible c spectrum ∧
      HasUnitScalarGap spectrum (shift c + δ) := by
  let S := realInitialRows A
  let B0 : ℝ := 2 * U + 4
  have hB0 : 1 ≤ B0 := by dsimp [B0]; linarith
  have hcut : ∀ J, (cells J).right < B0 :=
    realInitialRepairCell_right_lt_band S b U k q cells hU
  let initial := realInitialRepairState S b U k q cells B0 hB0 hcut
  have hcover : ∀ j : ℤ, |(j : ℝ)| ≤ A → j ∈ S :=
    fun j hj => (mem_realInitialRows hA j).mpr hj
  have hS : S.Nonempty := ⟨0, hcover 0 (by simpa using hA)⟩
  have hnodes : ∀ p ∈ initial.nodes, δ ≤ p.1 ∧ |(p.2 : ℝ)| ≤ p.1 := by
    intro p hp
    have h := (realInitialRepairState_node_position S b U k q cells B0 hB0 hcut p hp).2.1
    exact ⟨(hδb.trans (le_max_left _ _)).trans h, (le_max_right _ _).trans h⟩
  have hstrict : ∀ p ∈ initial.nodes, δ < p.1 :=
    realInitialRepairState_node_strict S b U k q cells B0 hB0 hcut hδb
  have ho : initial.HasReferenceOutput ref δ :=
    realInitialRepairState_hasReferenceOutput S b U k q cells B0 hB0 hcut
      hqthermal hqzero (shift c) δ ref href
  have hi : initial.ThermalIntegrable :=
    realInitialRepairState_thermalIntegrable S b U k q cells B0 hB0 hcut hqthermal
  have hc : initial.Cleared := realInitialRepairState_cleared S b U k q cells B0 hB0 hcut
  have hf : FrontInvariant T FiniteRepairState.front initial := by
    intro j
    exact (max_le_max hTA le_rfl).trans
      (max_le_realInitialRepairFront_of_cover S b U k q cells A hAU hcover j)
  have hupper : ∀ j : ℤ, initial.front j ≤
      max (U + 1) (max ((T : ℝ) + 1) |(j : ℝ)|) :=
    realInitialRepairState_front_le_layer_start S b U k q cells B0 hB0 hcut hS T
  have herror : ∀ (j : ℤ) (E : ℝ), |(j : ℝ)| ≤ E → initial.front j ≤ E →
      |initial.numerator j E - vacuumLeading (shift c) E j| ≤
        (5 / 8 : ℝ) * exp (7 * sqrt (shift c * E)) := by
    intro j E _ hE
    have h := realInitialRepairState_error_le_five_eighths S b U k q cells B0 hB0 hcut
      (shift c) A hAU hcover herr hrepair j E hE
    convert h using 1 <;> ring
  exact ⟨_, d.permanentSpectrumData_pureAdmissible_and_hasUnitScalarGap ref initial
    hδ hδT hnodes hstrict ha (by exact_mod_cast hT) ho hi hc hf hupper herror⟩

end GapFamily.Construction
