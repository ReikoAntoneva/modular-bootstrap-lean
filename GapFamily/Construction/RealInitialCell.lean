import GapFamily.Construction.InitialReferenceCellGrowth

/-!
# Initial reference cells with real construction parameters

The vacuum shift and the cutoff are arbitrary real numbers. A natural
moment degree is controlled by inequalities, without an integer identity
between the physical scales. This interface supports both proportional
cutoffs and fixed cutoffs once their numerical estimates are supplied.
-/

noncomputable section

open Set MeasureTheory Real
open GapFamily.Analytic

namespace GapFamily.Construction

/-- Physical mass estimates supply arbitrarily large variation reserve
whenever the natural degree lies between the negative and positive
exponential scales. The constants are selected before any physical scale. -/
theorem exists_realInitialCell_variation_threshold {c B D : ℝ}
    (hc : 0 < c) (hB : 0 ≤ B) (hD : 0 ≤ D) (p : ℕ) (β : ℝ) :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k → ∀ a b U C_N x₀ x₁ A N : ℝ,
      0 ≤ a → 1 + a ≤ D * ((k : ℝ) + 1) →
      C_N * sqrt (a * b) ≤ (k : ℝ) → (k : ℝ) ≤ sqrt (a * U) →
      c * exp (4 * sqrt (a * U)) ≤ A * (x₁ - x₀) →
      N ≤ B * (1 + a) ^ p * exp (C_N * sqrt (a * b)) →
      0 < initialCellMomentMargin x₀ x₁ A N k ∧
        β < initialCellVariationReserve x₀ x₁ A N k := by
  obtain ⟨k₀, hk₀⟩ := exists_initialCell_variation_threshold hc
    (show 0 ≤ B * D ^ p by positivity) p β
  refine ⟨k₀, ?_⟩
  intro k hk a b U C_N x₀ x₁ A N ha hpoly hnegativeExponent hpositiveExponent
    hpositive hnegative
  apply hk₀ k hk x₀ x₁ A N
  · exact (mul_le_mul_of_nonneg_left
      (exp_le_exp.mpr (by linarith)) hc.le).trans hpositive
  · refine hnegative.trans ?_
    calc
      B * (1 + a) ^ p * exp (C_N * sqrt (a * b)) ≤
          B * (D * ((k : ℝ) + 1)) ^ p * exp (k : ℝ) := by
        gcongr
      _ = (B * D ^ p) * ((k : ℝ) + 1) ^ p * exp (k : ℝ) := by
        rw [mul_pow]
        ring

/-- An actual initial reference cell exists at arbitrary real vacuum and
cutoff scales. Its atom count is the selected positive integer continuum
mass, and its natural moment degree is unrestricted except for the stated
growth inequalities. No integer restriction is imposed on `a` or `b`. -/
theorem exists_realInitialReferenceCell_threshold_of_bounds {c B D : ℝ}
    (hc : 0 < c) (hB : 0 ≤ B) (hD : 0 ≤ D) (p : ℕ) :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k → ∀ a b U C_N : ℝ,
      0 ≤ a → 1 ≤ U → 2 / c < U → b ≤ U / 16 →
      1 + a ≤ D * ((k : ℝ) + 1) →
      C_N * sqrt (a * b) ≤ (k : ℝ) → (k : ℝ) ≤ sqrt (a * U) →
      ∀ j : ℤ, |(j : ℝ)| ≤ U / 16 → ∀ q : ℝ → ℝ,
      IntegrableOn q (Ioo (max b |(j : ℝ)|) (U + 1)) (referenceMeasure j) →
      (∫ E in Ioo (max b |(j : ℝ)|) (U + 1),
        max (-q E) 0 ∂referenceMeasure j) ≤
          B * (1 + a) ^ p * exp (C_N * sqrt (a * b)) →
      (∀ E ∈ Icc (U / 4) (U + 1),
        c * (E ^ 2 - (j : ℝ) ^ 2) * exp (8 * sqrt (a * E)) ≤ q E) →
      Nonempty (InitialReferenceCell j (max b |(j : ℝ)|) U k q) := by
  obtain ⟨k₀, hk₀⟩ := exists_realInitialCell_variation_threshold
    (show 0 < c / 32 by positivity) hB hD p (1 / 2)
  refine ⟨k₀, ?_⟩
  intro k hk a b U C_N ha hU hlarge hbU hpoly hnegativeExponent hpositiveExponent
    j hjU q hq hnegative hbound
  have hUpos : 0 < U := by linarith
  have hLU : max b |(j : ℝ)| < U :=
    (max_le hbU hjU).trans_lt (by linarith)
  let A : ℝ := c * U * sqrt U / 8 * exp (4 * sqrt (a * U))
  let Nminus : ℝ := B * (1 + a) ^ p * exp (C_N * sqrt (a * b))
  have hreserve : 1 / 2 < initialCellVariationReserve
      (rootCoord |(j : ℝ)| (max b |(j : ℝ)|))
      (rootCoord |(j : ℝ)| U) A Nminus k := by
    exact (hk₀ k hk a b U C_N _ _ A Nminus ha hpoly
      hnegativeExponent hpositiveExponent
      (initialCell_density_length_lower (abs_nonneg _) hU hjU hbU hc.le) le_rfl).2
  have hupper := initialCell_coordinate_density_lower_of_edge_exponential j ha hUpos
    hjU hbU (show U ≤ U + 1 by linarith) hc.le q hbound
  have hterminal : 1 < ∫ E in Ioo U (U + 1), q E ∂referenceMeasure j := by
    apply initialReferenceCell_terminal_mass_gt_one j ha hU hjU hc hlarge q
      (hq.mono_set (Ioo_subset_Ioo hLU.le le_rfl))
    intro E hE
    exact hbound E ⟨(by linarith [hE.1]), hE.2⟩
  exact nonempty_initialReferenceCell_of_reserve j (A := A) (Nminus := Nminus)
    (le_max_right _ _) hLU (by dsimp [A]; positivity) q hq hnegative hupper hterminal hreserve

end GapFamily.Construction
