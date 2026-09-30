import Mathlib.Basic.Real.Basic

/-! The initial row front combines the chosen endpoint on active rows with
the physical spin threshold on every inactive row. -/

noncomputable section
namespace GapFamily.Construction

/-- Initial endpoints are used exactly on the rows active at threshold `T`. -/
def initialFront (T : ℝ) (endpoint : ℤ → ℝ) (j : ℤ) : ℝ :=
  if |(j : ℝ)| ≤ T then endpoint j else |(j : ℝ)|

@[simp] theorem initialFront_of_active (T : ℝ) (endpoint : ℤ → ℝ) (j : ℤ)
    (hj : |(j : ℝ)| ≤ T) : initialFront T endpoint j = endpoint j :=
  ite_eq_left hj

@[simp] theorem initialFront_of_inactive (T : ℝ) (endpoint : ℤ → ℝ) (j : ℤ)
    (hj : T < |(j : ℝ)|) : initialFront T endpoint j = |(j : ℝ)| :=
  ite_eq_right (not_le.mpr hj)

/-- A chosen endpoint above both thresholds makes every initial row front
at least the larger of the common threshold and its physical spin threshold. -/
theorem max_le_initialFront (T : ℝ) (endpoint : ℤ → ℝ)
    (hT : ∀ j : ℤ, |(j : ℝ)| ≤ T → T ≤ endpoint j)
    (hspin : ∀ j : ℤ, |(j : ℝ)| ≤ T → |(j : ℝ)| ≤ endpoint j) (j : ℤ) :
    max T |(j : ℝ)| ≤ initialFront T endpoint j := by
  by_cases hj : |(j : ℝ)| ≤ T
  · rw [initialFront_of_active T endpoint j hj]
    exact max_le (hT j hj) (hspin j hj)
  · rw [initialFront_of_inactive T endpoint j (lt_of_not_ge hj)]
    exact max_le (lt_of_not_ge hj).le le_rfl

theorem threshold_le_initialFront (T : ℝ) (endpoint : ℤ → ℝ)
    (hT : ∀ j : ℤ, |(j : ℝ)| ≤ T → T ≤ endpoint j) (j : ℤ) :
    T ≤ initialFront T endpoint j := by
  by_cases hj : |(j : ℝ)| ≤ T
  · rw [initialFront_of_active T endpoint j hj]
    exact hT j hj
  · rw [initialFront_of_inactive T endpoint j (lt_of_not_ge hj)]
    exact (lt_of_not_ge hj).le

theorem abs_spin_le_initialFront (T : ℝ) (endpoint : ℤ → ℝ)
    (hspin : ∀ j : ℤ, |(j : ℝ)| ≤ T → |(j : ℝ)| ≤ endpoint j) (j : ℤ) :
    |(j : ℝ)| ≤ initialFront T endpoint j := by
  by_cases hj : |(j : ℝ)| ≤ T
  · rw [initialFront_of_active T endpoint j hj]
    exact hspin j hj
  · rw [initialFront_of_inactive T endpoint j (lt_of_not_ge hj)]

theorem initialFront_nonneg (T : ℝ) (endpoint : ℤ → ℝ)
    (hspin : ∀ j : ℤ, |(j : ℝ)| ≤ T → |(j : ℝ)| ≤ endpoint j) (j : ℤ) :
    0 ≤ initialFront T endpoint j :=
  (abs_nonneg (j : ℝ)).trans (abs_spin_le_initialFront T endpoint hspin j)

/-- Increasing the chosen active endpoints increases the entire initial front. -/
theorem initialFront_mono (T : ℝ) {endpoint₁ endpoint₂ : ℤ → ℝ}
    (hle : ∀ j : ℤ, |(j : ℝ)| ≤ T → endpoint₁ j ≤ endpoint₂ j) :
    initialFront T endpoint₁ ≤ initialFront T endpoint₂ := by
  intro j
  by_cases hj : |(j : ℝ)| ≤ T
  · rw [initialFront_of_active T endpoint₁ j hj, initialFront_of_active T endpoint₂ j hj]
    exact hle j hj
  · rw [initialFront_of_inactive T endpoint₁ j (lt_of_not_ge hj),
      initialFront_of_inactive T endpoint₂ j (lt_of_not_ge hj)]

end GapFamily.Construction
