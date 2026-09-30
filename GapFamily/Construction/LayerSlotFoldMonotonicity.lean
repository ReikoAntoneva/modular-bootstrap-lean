import GapFamily.Construction.LayerScheduleConstruction

/-! Front monotonicity for every intermediate state in a finite slot fold.
Only the pointwise monotonicity of the actual step is needed. -/

namespace GapFamily.Construction

variable {S A I R : Type*} [Preorder R]

/-- Every finite fold advances each front from its starting state. -/
theorem front_le_foldl (front : S → I → R) (step : S → A → S)
    (hstep : ∀ s a i, front s i ≤ front (step s a) i)
    (initial : S) (L : List A) (i : I) :
    front initial i ≤ front (L.foldl step initial) i := by
  induction L generalizing initial with
  | nil => exact le_rfl
  | cons a L ih => exact (hstep initial a i).trans (ih (step initial a))

/-- An in-range prefix successor is the literal next step of the list. -/
theorem foldl_take_succ_eq_step (step : S → A → S) (initial : S)
    (L : List A) (k : ℕ) (hk : k < L.length) :
    (L.take (k + 1)).foldl step initial =
      step ((L.take k).foldl step initial) (L.get ⟨k, hk⟩) := by
  rw [List.take_succ_eq_append_getElem hk, List.foldl_append]
  rfl

/-- Fronts are monotone along all prefixes, including indices after the end. -/
theorem front_foldl_take_monotone (front : S → I → R) (step : S → A → S)
    (hstep : ∀ s a i, front s i ≤ front (step s a) i)
    (initial : S) (L : List A) (i : I) :
    Monotone (fun k : ℕ => front ((L.take k).foldl step initial) i) := by
  apply monotone_nat_of_le_succ
  intro k
  rw [List.take_add_one, List.foldl_append]
  exact front_le_foldl front step hstep _ _ i

/-- Every partial fold is bounded by the completed finite fold. -/
theorem front_foldl_take_le (front : S → I → R) (step : S → A → S)
    (hstep : ∀ s a i, front s i ≤ front (step s a) i)
    (initial : S) (L : List A) (k : ℕ) (i : I) :
    front ((L.take k).foldl step initial) i ≤ front (L.foldl step initial) i := by
  have h := front_le_foldl front step hstep ((L.take k).foldl step initial) (L.drop k) i
  simpa only [← List.foldl_append, List.take_append_drop] using h

end GapFamily.Construction
