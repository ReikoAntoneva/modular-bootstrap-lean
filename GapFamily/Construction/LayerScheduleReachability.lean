import GapFamily.Construction.LayerSlotChronology

/-! Frontier advancement from local estimates at the literal reached slot
states. This formulation allows ordinary error estimates to establish cell
validity on each finite prefix before the advancing-front induction is used. -/

noncomputable section
namespace GapFamily.Construction

variable {S : Type*}

/-- A local half-step proof at each actual slot prefix suffices to advance the
whole deterministic layer. No invariant for arbitrary off-trace states is needed. -/
theorem executeLayer_invariant_of_prefix_advance
    (m : ℕ) (front : S → ℤ → ℝ) (update : ℤ → S → S) (initial : S)
    (hmono : ∀ (j : ℤ) (s : S) (i : ℤ), front s i ≤ front (update j s) i)
    (hf : FrontInvariant m front initial)
    (hadvance : ∀ (before after : List ℤ) (j : ℤ),
      layerSlots m = before ++ j :: after →
      let s := before.foldl (fun s i => executeSlot m front update i s) initial
      (m : ℝ) ≤ front s j → front s j < (m : ℝ) + 1 →
        front s j + 1 / 2 ≤ front (update j s) j) :
    FrontInvariant (m + 1) front (executeLayer m front update initial) := by
  let step : S → ℤ → S := fun s j => executeSlot m front update j s
  have hstep : ∀ (s : S) (j i : ℤ), front s i ≤ front (step s j) i :=
    fun s j i => executeSlot_front_mono_of_update m front update hmono j s i
  have hfinalmono (i : ℤ) : front initial i ≤ front (executeLayer m front update initial) i :=
    executeLayer_front_mono_of_update m front update hmono initial i
  have hrow (j : ℤ) (hj : |j| ≤ (m : ℤ)) :
      (m : ℝ) + 1 ≤ front (executeLayer m front update initial) j := by
    obtain ⟨left, right, hrows⟩ := List.mem_iff_append.mp (mem_layerRows.mpr hj)
    let pre := left.flatMap (fun i => [i, i])
    let post := right.flatMap (fun i => [i, i])
    have hslots : layerSlots m = pre ++ j :: j :: post := by
      simp only [layerSlots, hrows, List.flatMap_append, List.flatMap_cons,
        List.cons_append, List.nil_append, pre, post]
    let u := pre.foldl step initial
    let v := step u j
    let w := step v j
    have hu : (m : ℝ) ≤ front u j :=
      ((le_max_left _ _).trans (hf j)).trans (front_le_foldl front step hstep initial pre j)
    have huv : front u j ≤ front v j := hstep u j j
    have hv : (m : ℝ) ≤ front v j := hu.trans huv
    have hfirst : front u j < (m : ℝ) + 1 →
        front u j + 1 / 2 ≤ front v j := by
      intro h
      have hraw := hadvance pre (j :: post) j hslots hu h
      simpa only [v, step, executeSlot_of_uncleared _ _ _ _ _ h] using hraw
    have hsecond : front v j < (m : ℝ) + 1 →
        front v j + 1 / 2 ≤ front w j := by
      intro h
      have hsplit : layerSlots m = (pre ++ [j]) ++ j :: post := by
        simpa only [List.append_assoc, List.cons_append, List.nil_append] using hslots
      have hpref : (pre ++ [j]).foldl
          (fun s i => executeSlot m front update i s) initial = v := by
        simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
        rfl
      have hraw := hadvance (pre ++ [j]) post j hsplit
      rw [hpref] at hraw
      have hh := hraw hv h
      simpa only [w, step, executeSlot_of_uncleared _ _ _ _ _ h] using hh
    have hw : (m : ℝ) + 1 ≤ front w j := by
      by_cases huc : (m : ℝ) + 1 ≤ front u j
      · exact huc.trans (huv.trans (hstep v j j))
      by_cases hvc : (m : ℝ) + 1 ≤ front v j
      · exact hvc.trans (hstep v j j)
      have h1 := hfirst (lt_of_not_ge huc)
      have h2 := hsecond (lt_of_not_ge hvc)
      linarith
    have hout : executeLayer m front update initial = post.foldl step w := by
      rw [executeLayer_eq_slot_fold, hslots, List.foldl_append,
        List.foldl_cons, List.foldl_cons]
    rw [hout]
    exact hw.trans (front_le_foldl front step hstep w post j)
  intro j
  apply max_le
  · have hh : (m : ℝ) + 1 ≤ front (executeLayer m front update initial) j := by
      by_cases hj : |j| ≤ (m : ℤ)
      · exact hrow j hj
      · have hint : (m : ℤ) + 1 ≤ |j| := by omega
        have hreal : (m : ℝ) + 1 ≤ |(j : ℝ)| := by exact_mod_cast hint
        exact hreal.trans (((le_max_right _ _).trans (hf j)).trans (hfinalmono j))
    simpa only [Nat.cast_add, Nat.cast_one] using hh
  · exact ((le_max_right _ _).trans (hf j)).trans (hfinalmono j)

/-- Actual-prefix cell validity and local advancement propagate the frontier
through the already defined natural recursion. -/
theorem scheduledLayerState_frontInvariant_of_prefix_advance
    (T : ℕ) (front : S → ℤ → ℝ) (update : ℕ → ℤ → S → S) (initial : S)
    (hmono : ∀ (m : ℕ) (j : ℤ) (s : S) (i : ℤ), front s i ≤ front (update m j s) i)
    (hf : FrontInvariant T front initial)
    (hadvance : ∀ (n : ℕ) (before after : List ℤ) (j : ℤ),
      layerSlots (T + n) = before ++ j :: after →
      let s := before.foldl (fun s i => executeSlot (T + n) front (update (T + n)) i s)
        (scheduledLayerState T front update initial n)
      ((T + n : ℕ) : ℝ) ≤ front s j → front s j < ((T + n : ℕ) : ℝ) + 1 →
        front s j + 1 / 2 ≤ front (update (T + n) j s) j) :
    ∀ n, FrontInvariant (T + n) front (scheduledLayerState T front update initial n) := by
  intro n
  induction n with
  | zero => simpa using hf
  | succ n ih =>
    have h := executeLayer_invariant_of_prefix_advance (T + n) front (update (T + n))
      (scheduledLayerState T front update initial n) (hmono (T + n)) ih (hadvance n)
    simpa only [scheduledLayerState_succ, Nat.add_assoc] using h

end GapFamily.Construction
