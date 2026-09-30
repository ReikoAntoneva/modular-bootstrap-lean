import GapFamily.Construction.RealPermanentSpectrumThermal
import GapFamily.Construction.RealTailReferenceOutput
import GapFamily.Construction.RealTailRecurrenceEnvelope
import GapFamily.Construction.PermanentSpectrumReferenceEndpoint
import GapFamily.Construction.FiniteRepairStateEnvelope

/-!
# Complete tail construction from a finite initial state

Only the finite initialization and local cell construction enter as premises.
The literal recursion, convergence of its emitted nodes, escaping continuum,
full character admissibility and unique unit marker are derived here. The
marker can be zero and is independent of the initial clearing cutoff.
-/

noncomputable section

open Set Filter MeasureTheory Real
open GapFamily.Analytic

namespace GapFamily.Construction.RealTailLocalData

variable {c U δ : ℝ} {T : ℕ} {degree : ℕ → ℕ}

/-- The same initial state and actual local repair choice produce the full
admissible spectrum. No infinite thermal or modular limit is assumed. -/
theorem permanentSpectrumData_pureAdmissible_and_hasUnitScalarGap
    (d : RealTailLocalData (shift c) U T degree)
    (ref : ReferenceOutput (shift c)) (initial : FiniteRepairState)
    (hδ : 0 ≤ δ) (hδT : δ < (T : ℝ))
    (hnodes : ∀ p ∈ initial.nodes, δ ≤ p.1 ∧ |(p.2 : ℝ)| ≤ p.1)
    (hstrict : ∀ p ∈ initial.nodes, δ < p.1)
    (ha : 100 ≤ shift c) (hT : (1 : ℝ) ≤ T)
    (ho : initial.HasReferenceOutput ref δ)
    (hi : initial.ThermalIntegrable) (hc : initial.Cleared)
    (hf : FrontInvariant T FiniteRepairState.front initial)
    (hupper : ∀ j : ℤ, initial.front j ≤
      max (U + 1) (max ((T : ℝ) + 1) |(j : ℝ)|))
    (herr : ∀ (j : ℤ) (E : ℝ), |(j : ℝ)| ≤ E → initial.front j ≤ E →
      |initial.numerator j E - vacuumLeading (shift c) E j| ≤
        (5 / 8 : ℝ) * exp (7 * sqrt (shift c * E))) :
    PureAdmissible c
        ((d.permanentSpectrumData δ hδ hδT.le initial hnodes).spectrum c) ∧
      HasUnitScalarGap
        ((d.permanentSpectrumData δ hδ hδT.le initial hnodes).spectrum c) (shift c + δ) := by
  let D := d.permanentSpectrumData δ hδ hδT.le initial hnodes
  have hout (k : ℕ) := d.state_hasReferenceOutput ref δ initial ho hi hc hupper k
  have hfront (k : ℕ) := d.state_frontInvariant initial hi herr hf k
  have hN : Tendsto (fun k => T + k) atTop atTop := by
    simpa only [Nat.add_comm] using tendsto_add_atTop_nat T
  have hcut : Tendsto (fun k => ((T + k : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hN
  have hthermal (t : ℝ) (ht : 0 < t) : Summable (D.layerThermal t) :=
    d.summable_permanentSpectrumData_layerThermal δ hδ hδT.le initial hnodes ha hT ht
  refine ⟨?_, d.permanentSpectrumData_hasUnitScalarGap δ hδ hδT.le initial hnodes
    hstrict hδT c⟩
  apply (D.pureAdmissible_and_hasGap_of_referenceState c (T : ℝ) 1 ref
    (d.state initial) (fun k => T + k) (fun k => ((T + k : ℕ) : ℝ))
    ha hT hN hcut hthermal
    (fun k => (hout k).1) (fun k => (hout k).2.1)
    (fun k => (hout k).2.2.1)
    (fun k => d.permanentSpectrumData_permanentAtomList δ hδ hδT.le initial hnodes k)
    (fun k j => ?_) (fun k j => ?_) (fun k j => ?_)).1
  · exact (show (T : ℝ) ≤ ((T + k : ℕ) : ℝ) by
      exact_mod_cast Nat.le_add_right T k).trans ((le_max_left _ _).trans (hfront k j))
  · exact (le_max_left _ _).trans (hfront k j)
  · exact (d.state initial k).ae_abs_numerator_le_tailEnvelope (by linarith)
      (hout k).2.2.1 (fun j E hp hE => d.state_error_le initial hi herr k j E hp hE) T j

end GapFamily.Construction.RealTailLocalData
