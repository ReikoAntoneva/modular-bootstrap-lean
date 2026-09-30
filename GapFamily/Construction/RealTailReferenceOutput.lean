import GapFamily.Construction.RealTailRecurrenceOutput
import GapFamily.Construction.RealTailRecurrenceEnvelope
import GapFamily.Construction.TailCellReferenceOutput

/-! Reference-independent finite output for the actual real-parameter recursion,
including a marker of shifted energy zero. -/

noncomputable section
namespace GapFamily.Construction
open Set Real Analytic
namespace RealTailLocalData
variable {a U : ℝ} {T : ℕ} {degree : ℕ → ℕ}
variable (d : RealTailLocalData a U T degree)

/-- Every complete finite state has the ordinary Fourier output of the same
reference and the same actual finite list of repairs. -/
theorem state_hasReferenceOutput (ref : ReferenceOutput a) (δ : ℝ)
    (initial : FiniteRepairState) (ho : initial.HasReferenceOutput ref δ)
    (hi : initial.ThermalIntegrable) (hc : initial.Cleared)
    (hf : ∀ j : ℤ, initial.front j ≤ max (U + 1) (max ((T : ℝ) + 1) |(j : ℝ)|))
    (k : ℕ) :
    (d.state initial k).HasReferenceOutput ref δ ∧ (d.state initial k).ThermalIntegrable ∧
      (d.state initial k).Cleared ∧ ∀ j : ℤ, (d.state initial k).front j ≤
        max (U + 1) (max (((T + k : ℕ) : ℝ) + 1) |(j : ℝ)|) := by
  apply d.state_output_invariant (fun st => st.HasReferenceOutput ref δ) ?_
    initial ho hi hc hf k
  intro st m J h hst
  exact st.addTailCell_hasReferenceOutput _ _ _ _ _ ref δ hst h.thermal

/-- The identical output and geometric invariants hold between any two slots. -/
theorem partialState_hasReferenceOutput (ref : ReferenceOutput a) (δ : ℝ)
    (initial : FiniteRepairState) (ho : initial.HasReferenceOutput ref δ)
    (hi : initial.ThermalIntegrable) (hc : initial.Cleared)
    (hf : ∀ j : ℤ, initial.front j ≤ max (U + 1) (max ((T : ℝ) + 1) |(j : ℝ)|))
    (k r : ℕ) :
    (d.partialState initial k r).HasReferenceOutput ref δ ∧
      (d.partialState initial k r).ThermalIntegrable ∧
      (d.partialState initial k r).Cleared ∧ ∀ j : ℤ, (d.partialState initial k r).front j ≤
        max (U + 1) (max (((T + k : ℕ) : ℝ) + 2) |(j : ℝ)|) := by
  apply d.partialState_output_invariant (fun st => st.HasReferenceOutput ref δ) ?_
    initial ho hi hc hf k r
  intro st m J h hst
  exact st.addTailCell_hasReferenceOutput _ _ _ _ _ ref δ hst h.thermal


/-- The concrete finite recurrence supplies its output, clearance, escaping
front and unprocessed continuum estimate together, for every marker location. -/
theorem state_spec (ref : ReferenceOutput a) (δ : ℝ)
    (initial : FiniteRepairState) (ho : initial.HasReferenceOutput ref δ)
    (hi : initial.ThermalIntegrable) (hc : initial.Cleared)
    (hupper : ∀ j : ℤ, initial.front j ≤ max (U + 1) (max ((T : ℝ) + 1) |(j : ℝ)|))
    (hfront : FrontInvariant T FiniteRepairState.front initial)
    (herr : ∀ (j : ℤ) (E : ℝ), |(j : ℝ)| ≤ E → initial.front j ≤ E →
      |initial.numerator j E - vacuumLeading a E j| ≤
        (5 / 8 : ℝ) * exp (7 * sqrt (a * E))) (k : ℕ) :
    (d.state initial k).HasReferenceOutput ref δ ∧ (d.state initial k).ThermalIntegrable ∧
      (d.state initial k).Cleared ∧
      FrontInvariant (T + k) FiniteRepairState.front (d.state initial k) ∧
      ∀ (j : ℤ) (E : ℝ), (d.state initial k).front j ≤ E →
        |(d.state initial k).numerator j E - vacuumLeading a E j| ≤
          exp (7 * sqrt (a * E)) := by
  obtain ⟨hok, hik, hck, _⟩ := d.state_hasReferenceOutput ref δ initial ho hi hc hupper k
  have hfk := d.state_frontInvariant initial hi herr hfront k
  refine ⟨hok, hik, hck, hfk, ?_⟩
  intro j E hE
  exact d.state_error_le initial hi herr k j E
    ((le_max_right _ _).trans ((hfk j).trans hE)) hE

end RealTailLocalData
end GapFamily.Construction
