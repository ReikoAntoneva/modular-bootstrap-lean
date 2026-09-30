import GapFamily.Construction.LayerScheduleEnvelope
import GapFamily.Analytic.Foundation.ReferenceMeasure

/-! Literal continuum replacement in one physical cell. The half-open cleared
interval retains the new frontier value in the unprocessed continuum. Ordinary
reference measures have no endpoint atoms, so this uses the same cell measure
as the open-interval residual. -/

noncomputable section
namespace GapFamily.Construction
open Set MeasureTheory

/-- Advancing exactly the selected row to its chosen right endpoint. -/
def cellFrontUpdate (front : ℤ → ℝ) (J : ℤ) (V : ℝ) : ℤ → ℝ :=
  Function.update front J V

@[simp] theorem cellFrontUpdate_same (front : ℤ → ℝ) (J : ℤ) (V : ℝ) :
    cellFrontUpdate front J V J = V := by simp [cellFrontUpdate]

theorem cellFrontUpdate_other (front : ℤ → ℝ) (J : ℤ) (V : ℝ)
    {j : ℤ} (hj : j ≠ J) : cellFrontUpdate front J V j = front j :=
  Function.update_of_ne hj _ _

theorem cellFrontUpdate_mono (front : ℤ → ℝ) (J : ℤ) (V : ℝ)
    (hV : front J ≤ V) (j : ℤ) : front j ≤ cellFrontUpdate front J V j := by
  by_cases hj : j = J
  · subst j
    simpa using hV
  · rw [cellFrontUpdate_other front J V hj]

/-- Remove just the current continuum of the selected cell; existing atom
occurrences are stored separately and are never subtracted. -/
def clearCellNumerator (q : ℤ → ℝ → ℝ) (J : ℤ) (L V : ℝ) (j : ℤ) (e : ℝ) : ℝ :=
  if j = J ∧ e ∈ Ico L V then 0 else q j e

/-- The actual update formula once the complete exterior numerator is supplied. -/
def cellNumeratorUpdate (q exterior : ℤ → ℝ → ℝ) (J : ℤ) (L V B : ℝ)
    (j : ℤ) (e : ℝ) : ℝ :=
  clearCellNumerator q J L V j e + if B < e then exterior j e else 0

theorem clearCellNumerator_unprocessed (q : ℤ → ℝ → ℝ) (front : ℤ → ℝ)
    (J : ℤ) (L V : ℝ) (j : ℤ) (e : ℝ)
    (he : cellFrontUpdate front J V j ≤ e) :
    clearCellNumerator q J L V j e = q j e := by
  unfold clearCellNumerator
  apply ite_eq_right
  rintro ⟨rfl, hcell⟩
  rw [cellFrontUpdate_same] at he
  exact (not_lt_of_ge he) hcell.2

/-- Remaining continuum points see only the complete exterior correction. -/
theorem cellNumeratorUpdate_unprocessed (q exterior : ℤ → ℝ → ℝ)
    (front : ℤ → ℝ) (J : ℤ) (L V B : ℝ) (j : ℤ) (e : ℝ)
    (he : cellFrontUpdate front J V j ≤ e) :
    cellNumeratorUpdate q exterior J L V B j e =
      q j e + if B < e then exterior j e else 0 := by
  rw [cellNumeratorUpdate, clearCellNumerator_unprocessed q front J L V j e he]

/-- No continuum remains behind the new frontier, provided the prior cleared
region is below the common repair cutoff and was already empty. -/
theorem cellNumeratorUpdate_cleared (q exterior : ℤ → ℝ → ℝ)
    (front : ℤ → ℝ) (J : ℤ) (L V B : ℝ) (hL : front J = L) (hVB : V ≤ B)
    (hfront : ∀ j : ℤ, front j ≤ max B |(j : ℝ)|)
    (hclear : ∀ (j : ℤ) (e : ℝ), |(j : ℝ)| ≤ e → e < front j → q j e = 0)
    (j : ℤ) (e : ℝ) (hphysical : |(j : ℝ)| ≤ e)
    (he : e < cellFrontUpdate front J V j) :
    cellNumeratorUpdate q exterior J L V B j e = 0 := by
  have heB : e ≤ B := by
    by_cases hj : j = J
    · subst j
      rw [cellFrontUpdate_same] at he
      exact he.le.trans hVB
    · rw [cellFrontUpdate_other front J V hj] at he
      rcases lt_max_iff.mp (he.trans_le (hfront j)) with h | h
      · exact h.le
      · exact False.elim ((not_lt_of_ge hphysical) h)
  rw [cellNumeratorUpdate, ite_eq_right (not_lt_of_ge heB), add_zero]
  unfold clearCellNumerator
  split_ifs with hcell
  · rfl
  · apply hclear j e hphysical
    by_cases hj : j = J
    · subst j
      rw [hL]
      rw [cellFrontUpdate_same] at he
      have hn : ¬ L ≤ e := by
        intro hLe
        exact hcell ⟨rfl, hLe, he⟩
      exact lt_of_not_ge hn
    · simpa only [cellFrontUpdate_other front J V hj] using he

/-- The exterior error bound is exactly the error seen at every remaining
unprocessed point; below the cutoff the error is identically zero. -/
theorem cellNumeratorUpdate_error (q exterior : ℤ → ℝ → ℝ)
    (front : ℤ → ℝ) (J : ℤ) (L V B ε : ℝ) (H : ℝ → ℝ)
    (hε : 0 ≤ ε) (hH : ∀ e, 0 ≤ H e)
    (herror : ∀ (j : ℤ) (e : ℝ), |(j : ℝ)| ≤ e → B < e →
      |exterior j e| ≤ ε * H e)
    (j : ℤ) (e : ℝ) (hphysical : |(j : ℝ)| ≤ e)
    (he : cellFrontUpdate front J V j ≤ e) :
    |cellNumeratorUpdate q exterior J L V B j e - q j e| ≤ ε * H e := by
  rw [cellNumeratorUpdate_unprocessed q exterior front J L V B j e he]
  by_cases hBe : B < e
  · rw [ite_eq_left hBe, add_sub_cancel_left]
    exact herror j e hphysical hBe
  · rw [ite_eq_right hBe, add_zero, sub_self, abs_zero]
    exact mul_nonneg hε (hH e)

theorem clearCellNumerator_eq_sub_indicator (q : ℤ → ℝ → ℝ)
    (J : ℤ) (L V : ℝ) (j : ℤ) :
    clearCellNumerator q J L V j =
      fun e => q j e - (if j = J then (Ico L V).indicator (q j) e else 0) := by
  funext e
  by_cases hj : j = J <;> by_cases he : e ∈ Ico L V <;>
    simp [clearCellNumerator, hj, he]

/-- Clearing the cell preserves ordinary local absolute integrability. -/
theorem integrable_clearCellNumerator (q : ℤ → ℝ → ℝ)
    (J : ℤ) (L V : ℝ) (j : ℤ) (μ : Measure ℝ) (hq : Integrable (q j) μ) :
    Integrable (clearCellNumerator q J L V j) μ := by
  rw [clearCellNumerator_eq_sub_indicator]
  by_cases hj : j = J
  · subst j
    simp only [ite_true]
    exact hq.sub (hq.indicator measurableSet_Ico)
  · simpa only [hj, ite_false, sub_zero] using hq

/-- The density update is ordinary on every measure for which the old density
and its actual exterior correction are integrable. -/
theorem integrable_cellNumeratorUpdate (q exterior : ℤ → ℝ → ℝ)
    (J : ℤ) (L V B : ℝ) (j : ℤ) (μ : Measure ℝ) (hq : Integrable (q j) μ)
    (hext : IntegrableOn (exterior j) (Ioi B) μ) :
    Integrable (cellNumeratorUpdate q exterior J L V B j) μ := by
  have hE : Integrable (fun e => if B < e then exterior j e else 0) μ :=
    (integrable_indicator_iff measurableSet_Ioi).mpr hext
  exact (integrable_clearCellNumerator q J L V j μ hq).add hE

end GapFamily.Construction
