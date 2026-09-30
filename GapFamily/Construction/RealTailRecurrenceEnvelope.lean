import GapFamily.Construction.RealTailRecurrence
import GapFamily.Construction.FiniteRepairStateEnvelope

/-! The finite accumulated exterior error proves all local cell hypotheses and
forces every row front to escape. The charge is an arbitrary real number. -/

noncomputable section
namespace GapFamily.Construction
open Set Real Analytic
namespace RealTailLocalData
variable {a U : ℝ} {T : ℕ} {degree : ℕ → ℕ}
variable (d : RealTailLocalData a U T degree)

/-- Actual partial states preserve the reference envelope with explicit
coefficient `5/8 + 1/256`. This does not assume slot validity. -/
theorem partialState_error (initial : FiniteRepairState)
    (hi : initial.ThermalIntegrable)
    (hinitial : ∀ (j : ℤ) (E : ℝ), |(j : ℝ)| ≤ E → initial.front j ≤ E →
      |initial.numerator j E - vacuumLeading a E j| ≤
        (5 / 8 : ℝ) * exp (7 * sqrt (a * E)))
    (k r : ℕ) (j : ℤ) (E : ℝ) (hphysical : |(j : ℝ)| ≤ E)
    (hpost : (d.partialState initial k r).front j ≤ E) :
    |(d.partialState initial k r).numerator j E - vacuumLeading a E j| ≤
      (161 / 256 : ℝ) * exp (7 * sqrt (a * E)) := by
  let slots := scheduledPartialSlotPrefix T k r
  let step : (ℕ × ℤ) → FiniteRepairState → FiniteRepairState := fun p st =>
    executeSlot p.1 FiniteRepairState.front (d.step p.1) p.2 st
  let active : FiniteRepairState → ℝ × ℤ → Prop := fun st x =>
    |(x.2 : ℝ)| ≤ x.1 ∧ st.front x.2 ≤ x.1
  let H : ℝ × ℤ → ℝ := fun x => exp (7 * sqrt (a * x.1))
  have hvalid : ∀ p ∈ slots, ∀ st, st.ThermalIntegrable → (step p st).ThermalIntegrable := by
    intro p _ st hst
    exact d.executeSlot_thermalIntegrable p.1 p.2 st hst
  have hactive : ∀ p ∈ slots, ∀ st, st.ThermalIntegrable →
      ∀ x, active (step p st) x → active st x := by
    intro p _ st _ x hx
    refine ⟨hx.1, ?_⟩
    exact (executeSlot_front_mono_of_update p.1 FiniteRepairState.front
      (d.step p.1) (d.step_front_mono p.1) p.2 st x.2).trans hx.2
  have herror : ∀ p ∈ slots, ∀ st, st.ThermalIntegrable →
      ∀ x, active (step p st) x →
        ‖(step p st).numerator x.2 x.1 - st.numerator x.2 x.1‖ ≤
          Layer.slotBudget p.1 * H x := by
    intro p _ st _ x hx
    by_cases hclear : (p.1 : ℝ) + 1 ≤ st.front p.2
    · simp only [step, executeSlot_of_cleared _ _ _ _ _ hclear, sub_self, norm_zero]
      exact mul_nonneg (by unfold Layer.slotBudget; positivity) (exp_pos _).le
    · have hunclear := lt_of_not_ge hclear
      change active (executeSlot p.1 FiniteRepairState.front (d.step p.1) p.2 st) x at hx
      rw [executeSlot_of_uncleared _ _ _ _ _ hunclear] at hx
      change ‖(executeSlot p.1 FiniteRepairState.front (d.step p.1) p.2 st).numerator x.2 x.1 - _‖ ≤ _
      rw [executeSlot_of_uncleared _ _ _ _ _ hunclear]
      simpa only [Real.norm_eq_abs, H] using d.step_error p.1 p.2 st x.2 x.1 hx.1 hx.2
  have hstart : ∀ x, active initial x →
      ‖initial.numerator x.2 x.1 - vacuumLeading a x.1 x.2‖ ≤ (5 / 8 : ℝ) * H x := by
    intro x hx
    simpa only [Real.norm_eq_abs, H] using hinitial x.2 x.1 hx.1 hx.2
  have hfold : d.partialState initial k r =
      slots.foldl (fun st p => step p st) initial := d.partialState_eq_fold initial k r
  have hx : active (slots.foldl (fun st p => step p st) initial) (E, j) := by
    rw [← hfold]
    exact ⟨hphysical, hpost⟩
  have hbound := norm_foldl_sub_reference_le slots step FiniteRepairState.ThermalIntegrable
    active (fun st x => st.numerator x.2 x.1) (fun p => Layer.slotBudget p.1) H
    hvalid hactive herror initial hi (fun x => vacuumLeading a x.1 x.2)
    (5 / 8) hstart (E, j) hx
  have hcost : (5 / 8 : ℝ) + (slots.map (fun p => Layer.slotBudget p.1)).sum ≤ 161 / 256 := by
    have hc := sum_scheduledPartialSlotPrefix_slotBudget_le T k r
    change (slots.map (fun p => Layer.slotBudget p.1)).sum ≤ (1 / 256 : ℝ) at hc
    linarith
  have hfinal := hbound.trans (mul_le_mul_of_nonneg_right hcost (exp_pos _).le)
  rw [← hfold] at hfinal
  simpa only [Real.norm_eq_abs, H] using hfinal

variable (initial : FiniteRepairState) (hi : initial.ThermalIntegrable)
    (herr : ∀ (j : ℤ) (E : ℝ), |(j : ℝ)| ≤ E → initial.front j ≤ E →
      |initial.numerator j E - vacuumLeading a E j| ≤
        (5 / 8 : ℝ) * exp (7 * sqrt (a * E)))

include hi herr in
theorem partialState_error_le (k r : ℕ) (j : ℤ) (E : ℝ)
    (hphysical : |(j : ℝ)| ≤ E) (hpost : (d.partialState initial k r).front j ≤ E) :
    |(d.partialState initial k r).numerator j E - vacuumLeading a E j| ≤
      exp (7 * sqrt (a * E)) := by
  have h := d.partialState_error initial hi herr k r j E hphysical hpost
  have hH := exp_pos (7 * sqrt (a * E))
  nlinarith

include hi herr in
theorem state_error (k : ℕ) (j : ℤ) (E : ℝ)
    (hphysical : |(j : ℝ)| ≤ E) (hpost : (d.state initial k).front j ≤ E) :
    |(d.state initial k).numerator j E - vacuumLeading a E j| ≤
      (161 / 256 : ℝ) * exp (7 * sqrt (a * E)) := by
  simpa only [partialState_zero] using d.partialState_error initial hi herr k 0 j E hphysical hpost

include hi herr in
theorem state_error_le (k : ℕ) (j : ℤ) (E : ℝ)
    (hphysical : |(j : ℝ)| ≤ E) (hpost : (d.state initial k).front j ≤ E) :
    |(d.state initial k).numerator j E - vacuumLeading a E j| ≤
      exp (7 * sqrt (a * E)) := by
  simpa only [partialState_zero] using d.partialState_error_le initial hi herr k 0 j E hphysical hpost

include hi herr in
/-- The established finite error budget activates every reached live slot. -/
theorem partialState_valid (k r : ℕ) (J : ℤ)
    (hJ : |(J : ℝ)| ≤ ((T + k : ℕ) : ℝ))
    (hL : ((T + k : ℕ) : ℝ) ≤ (d.partialState initial k r).front J)
    (hLt : (d.partialState initial k r).front J < ((T + k : ℕ) : ℝ) + 1) :
    RealTailStepValid a T (d.partialState initial k r) (T + k) J where
  layer := Nat.le_add_right _ _
  front_lower := hL
  front_upper := hLt
  physical := hJ.trans hL
  thermal := d.partialState_thermalIntegrable initial hi k r
  envelope := fun E hE => d.partialState_error_le initial hi herr k r J E
    ((hJ.trans hL).trans hE.1) hE.1

theorem partialState_eq_before (k : ℕ) (before after : List ℤ) (J : ℤ)
    (hslots : layerSlots (T + k) = before ++ J :: after) :
    d.partialState initial k before.length =
      before.foldl (fun st j => executeSlot (T + k) FiniteRepairState.front
        (d.step (T + k)) j st) (d.state initial k) := by
  unfold partialState
  rw [hslots, List.take_left]

include hi herr in
/-- All row fronts advance through the complete sequence of integer layers. -/
theorem state_frontInvariant (hf : FrontInvariant T FiniteRepairState.front initial)
    (k : ℕ) : FrontInvariant (T + k) FiniteRepairState.front (d.state initial k) := by
  apply scheduledLayerState_frontInvariant_of_prefix_advance T FiniteRepairState.front d.step
    initial d.step_front_mono hf _ k
  intro k before after J hslots
  dsimp only
  intro hL hLt
  have hJmem : J ∈ layerSlots (T + k) := by rw [hslots]; simp
  have hJ : |(J : ℝ)| ≤ ((T + k : ℕ) : ℝ) := by
    exact_mod_cast (mem_layerSlots _ _).mp hJmem
  have hstate := d.partialState_eq_before initial k before after J hslots
  have hv := d.partialState_valid initial hi herr k before.length J hJ
  rw [hstate] at hv
  exact d.step_front_advance (hv hL hLt)

include hi herr in
theorem partialState_frontInvariant (hf : FrontInvariant T FiniteRepairState.front initial)
    (k r : ℕ) : FrontInvariant (T + k) FiniteRepairState.front (d.partialState initial k r) := by
  intro j
  apply (d.state_frontInvariant initial hi herr hf k j).trans
  exact front_le_foldl FiniteRepairState.front _
    (fun st J i => executeSlot_front_mono_of_update _ _ _ (d.step_front_mono _) J st i) _ _ j

include hi herr in
theorem partialState_valid_of_uncleared (hf : FrontInvariant T FiniteRepairState.front initial)
    (k r : ℕ) (J : ℤ) (hJ : |(J : ℝ)| ≤ ((T + k : ℕ) : ℝ))
    (hLt : (d.partialState initial k r).front J < ((T + k : ℕ) : ℝ) + 1) :
    RealTailStepValid a T (d.partialState initial k r) (T + k) J :=
  d.partialState_valid initial hi herr k r J hJ
    ((le_max_left _ _).trans (d.partialState_frontInvariant initial hi herr hf k r J)) hLt

include hi herr in
theorem state_front_ge (hf : FrontInvariant T FiniteRepairState.front initial)
    (k : ℕ) (j : ℤ) : ((T + k : ℕ) : ℝ) ≤ (d.state initial k).front j :=
  (le_max_left _ _).trans (d.state_frontInvariant initial hi herr hf k j)



include hi herr in
/-- Every fixed physical cutoff is uniformly behind all row fronts eventually. -/
theorem state_front_eventually_above (hf : FrontInvariant T FiniteRepairState.front initial)
    (R : ℝ) : ∃ n : ℕ, ∀ k, n ≤ k → ∀ j : ℤ, R ≤ (d.state initial k).front j := by
  obtain ⟨n, hn⟩ := exists_nat_ge R
  refine ⟨n, fun k hnk j => ?_⟩
  have hnk' : (n : ℝ) ≤ ((T + k : ℕ) : ℝ) :=
    Nat.cast_le.mpr (hnk.trans (Nat.le_add_left _ _))
  exact hn.trans (hnk'.trans (d.state_front_ge initial hi herr hf k j))

include hi herr in
/-- Clearance and the proved finite error give the global physical envelope. -/
theorem state_abs_numerator_le_tailEnvelope (ha : 2 ≤ a) (k : ℕ)
    (hc : (d.state initial k).Cleared) (j : ℤ) (E : ℝ)
    (hphysical : |(j : ℝ)| ≤ E) :
    |(d.state initial k).numerator j E| ≤ tailEnvelopeNumerator a E j :=
  (d.state initial k).abs_numerator_le_tailEnvelope ha hc
    (d.state_error_le initial hi herr k) j E hphysical

include hi herr in
/-- The actual stored continuum satisfies the measure envelope used by the
permanent-spectrum endpoint. -/
theorem state_ae_numerator_le_tailEnvelope (ha : 2 ≤ a) (k : ℕ)
    (hc : (d.state initial k).Cleared) (B : ℝ) (j : ℤ) :
    ∀ᵐ E ∂(referenceMeasure j).restrict (Ici (max B |(j : ℝ)|)),
      |(d.state initial k).numerator j E| ≤ (1 : ℝ) * tailEnvelopeNumerator a E j :=
  (d.state initial k).ae_abs_numerator_le_tailEnvelope ha hc
    (d.state_error_le initial hi herr k) B j

end RealTailLocalData
end GapFamily.Construction
