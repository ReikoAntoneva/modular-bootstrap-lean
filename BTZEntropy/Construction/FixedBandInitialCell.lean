import BTZEntropy.Construction.FixedBandDegree
import GapFamily.Construction.FixedCutoffReferenceDensityMass

/-! Fixed-band initial cells. A quadratic polynomial in the moment degree
absorbs charge growth while the processing endpoint stays fixed. -/

noncomputable section

open Set MeasureTheory Real
open GapFamily.Analytic GapFamily.Construction

namespace BTZEntropy.Construction

/-- Physical mass estimates supply arbitrarily large variation reserve
whenever the natural degree lies between the negative and positive
exponential scales. The constants are selected before any physical scale. -/
theorem exists_fixedBandCell_variation_threshold {c B D : ℝ}
    (hc : 0 < c) (hB : 0 ≤ B) (hD : 0 ≤ D) (p : ℕ) (β : ℝ) :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k → ∀ a b U C_N x₀ x₁ A N : ℝ,
      0 ≤ a → 1 + a ≤ D * ((k : ℝ) + 1) ^ 2 →
      C_N * sqrt (a * b) ≤ (k : ℝ) → (k : ℝ) ≤ sqrt (a * U) →
      c * exp (4 * sqrt (a * U)) ≤ A * (x₁ - x₀) →
      N ≤ B * (1 + a) ^ p * exp (C_N * sqrt (a * b)) →
      0 < initialCellMomentMargin x₀ x₁ A N k ∧
        β < initialCellVariationReserve x₀ x₁ A N k := by
  obtain ⟨k₀, hk₀⟩ := exists_initialCell_variation_threshold hc
    (show 0 ≤ B * D ^ p by positivity) (2 * p) β
  refine ⟨k₀, ?_⟩
  intro k hk a b U C_N x₀ x₁ A N ha hpoly hnegativeExponent hpositiveExponent
    hpositive hnegative
  apply hk₀ k hk x₀ x₁ A N
  · exact (mul_le_mul_of_nonneg_left
      (exp_le_exp.mpr (by linarith)) hc.le).trans hpositive
  · refine hnegative.trans ?_
    calc
      B * (1 + a) ^ p * exp (C_N * sqrt (a * b)) ≤
          B * (D * ((k : ℝ) + 1) ^ 2) ^ p * exp (k : ℝ) := by
        gcongr
      _ = (B * D ^ p) * ((k : ℝ) + 1) ^ (2 * p) * exp (k : ℝ) := by
        rw [mul_pow, ← pow_mul]
        ring

/-- An actual initial reference cell exists at arbitrary real vacuum and
cutoff scales. Its atom count is the selected positive integer continuum
mass, and its natural moment degree is unrestricted except for the stated
growth inequalities. No integer restriction is imposed on `a` or `b`. -/
theorem exists_fixedBandInitialReferenceCell_threshold_of_bounds {c B D : ℝ}
    (hc : 0 < c) (hB : 0 ≤ B) (hD : 0 ≤ D) (p : ℕ) :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k → ∀ a b U C_N : ℝ,
      0 ≤ a → 1 ≤ U → 2 / c < U → b ≤ U / 16 →
      1 + a ≤ D * ((k : ℝ) + 1) ^ 2 →
      C_N * sqrt (a * b) ≤ (k : ℝ) → (k : ℝ) ≤ sqrt (a * U) →
      ∀ j : ℤ, |(j : ℝ)| ≤ U / 16 → ∀ q : ℝ → ℝ,
      IntegrableOn q (Ioo (max b |(j : ℝ)|) (U + 1)) (referenceMeasure j) →
      (∫ E in Ioo (max b |(j : ℝ)|) (U + 1),
        max (-q E) 0 ∂referenceMeasure j) ≤
          B * (1 + a) ^ p * exp (C_N * sqrt (a * b)) →
      (∀ E ∈ Icc (U / 4) (U + 1),
        c * (E ^ 2 - (j : ℝ) ^ 2) * exp (8 * sqrt (a * E)) ≤ q E) →
      Nonempty (InitialReferenceCell j (max b |(j : ℝ)|) U k q) := by
  obtain ⟨k₀, hk₀⟩ := exists_fixedBandCell_variation_threshold
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


/-- The canonical reference supplies genuine integer-mass cells for real
`a` and cutoff `b`, uniformly in the marker `δ ∈ [0,b]`. Its numerical degree threshold is independent of these scales.
All analytic density and endpoint-existence premises are discharged. -/
theorem exists_fixedBandInitialCell_threshold {D : ℝ} (hD : 0 ≤ D) :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k → ∀ a b δ U : ℝ,
      ∀ (ha : 2 ≤ a) (hb : 1 ≤ b),
      0 ≤ δ → δ ≤ b →
      (fixedCutoffReferenceBandThreshold : ℝ) ≤ b → b ≤ a →
      16 ≤ U → 2 / (π ^ 4 / 625) < U →
      (fixedCutoffReferenceRadius : ℝ) * b ≤ U / 16 →
      1 + a ≤ D * ((k : ℝ) + 1) ^ 2 →
      fixedCutoffReferenceNegativeExponent * sqrt (a * b) ≤ (k : ℝ) →
      (k : ℝ) ≤ sqrt (a * U) →
      ∀ j : ℤ, |(j : ℝ)| ≤ (fixedCutoffReferenceRadius : ℝ) * b →
      Nonempty (InitialReferenceCell j (max b |(j : ℝ)|) U k
        (fixedCutoffReferenceDensity a b δ ha hb j)) := by
  obtain ⟨k₀, hk₀⟩ := exists_fixedBandInitialReferenceCell_threshold_of_bounds
    (show 0 < π ^ 4 / 625 by positivity) fixedCutoffReferenceNegativeCoefficient_pos.le hD 9
  refine ⟨k₀, ?_⟩
  intro k hk a b δ U ha hb hδ hδb hnb hba hU hlarge hTU hpoly hnegative hpositive j hj
  have hR : (1 : ℝ) ≤ fixedCutoffReferenceRadius := by
    exact_mod_cast (show 1 ≤ fixedCutoffReferenceRadius by have := fixedCutoffReferenceRadius_gt_six; omega)
  have hbT : b ≤ (fixedCutoffReferenceRadius : ℝ) * b :=
    le_mul_of_one_le_left (by linarith) hR
  apply hk₀ k hk a b U fixedCutoffReferenceNegativeExponent (by linarith) (by linarith)
    hlarge (hbT.trans hTU) hpoly hnegative hpositive j (hj.trans hTU)
    (fixedCutoffReferenceDensity a b δ ha hb j)
  · exact IntegrableOn.mono_set
      (fixedCutoffReferenceDensity_integrable a b δ ha hb hδ hδb (U + 1) j)
      (Ioo_subset_Ioo (le_max_right _ _) le_rfl)
  · exact (setIntegral_le_integral
      (fixedCutoffReferenceDensity_negativePart_integrable a b δ ha hb hδ hδb j hnb hba hj)
      (Filter.Eventually.of_forall fun E => le_max_right _ _)).trans
      (fixedCutoffReferenceDensity_negativeMass_le a b δ ha hb hδ hδb j hnb hba hj)
  · intro E hE
    apply fixedCutoffReferenceDensity_lower a b δ ha hb hδ hδb E j hnb hba
    · linarith [hE.1]
    · linarith [hE.1]

/-- Fixing the clearing band and processing endpoint leaves only a charge
threshold, uniform in every marker location in the band. -/
theorem eventually_fixedBandInitialCell {b U : ℝ} (hb : 1 ≤ b)
    (hnb : (fixedCutoffReferenceBandThreshold : ℝ) ≤ b)
    (hU : 16 ≤ U) (hlarge : 2 / (π ^ 4 / 625) < U)
    (hTU : (fixedCutoffReferenceRadius : ℝ) * b ≤ U / 16)
    (hnegative : 4 * fixedCutoffReferenceNegativeExponent ^ 2 * b ≤ U) :
    ∀ᶠ a : ℝ in Filter.atTop, ∃ ha : 2 ≤ a, b ≤ a ∧
      ∀ δ : ℝ, 0 ≤ δ → δ ≤ b → ∀ j : ℤ,
        |(j : ℝ)| ≤ (fixedCutoffReferenceRadius : ℝ) * b →
        Nonempty (InitialReferenceCell j (max b |(j : ℝ)|) U (fixedBandDegree a U)
          (fixedCutoffReferenceDensity a b δ ha hb j)) := by
  have hUpos : 0 < U := by linarith
  obtain ⟨k₀, hk₀⟩ := exists_fixedBandInitialCell_threshold
    (show 0 ≤ 1 + 1 / U by positivity)
  filter_upwards [eventually_fixedBandDegree_large hUpos k₀,
    Filter.eventually_ge_atTop (max 2 b)] with a hk ha
  have ha2 : 2 ≤ a := (le_max_left _ _).trans ha
  have hba : b ≤ a := (le_max_right _ _).trans ha
  refine ⟨ha2, hba, ?_⟩
  intro δ hδ hδb j hj
  exact hk₀ (fixedBandDegree a U) hk.1 a b δ U ha2 hb hδ hδb hnb hba hU hlarge hTU
    (fixedBandDegree_polynomial_base (by linarith) hUpos)
    (fixedBandDegree_negative_exponent (by linarith) (by linarith)
      fixedCutoffReferenceNegativeExponent_pos.le hnegative hk.2)
    (fixedBandDegree_le_sqrt a U) j hj

end BTZEntropy.Construction
