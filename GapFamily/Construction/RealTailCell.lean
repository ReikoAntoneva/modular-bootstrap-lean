import GapFamily.Construction.TailCellExistence
import GapFamily.Construction.RealTailMomentSchedule

/-! Tail cells at arbitrary real charge. Rounding is confined to the number of
moments; the vacuum, continuum and repair envelopes retain the actual charge. -/

noncomputable section
open Set MeasureTheory Real Filter
open GapFamily.Analytic

namespace GapFamily.Construction

/-- A single real-charge threshold supplies every layer cell above a positive
charge ray, with integer moment count and actual signed variation bounds. -/
theorem eventually_realTailCell {t : ℝ} (ht : 0 < t) {K : ℕ} (hK : 0 < K) :
    ∀ᶠ a : ℝ in atTop, ∀ m : ℕ, ∀ L : ℝ, t * a ≤ L →
      (m : ℝ) ≤ L → L < (m : ℝ) + 1 →
      ∀ j : ℤ, |(j : ℝ)| ≤ L →
      ∀ q : ℝ → ℝ, IntegrableOn q (Ioo L (L + 1)) (referenceMeasure j) →
      (∀ E ∈ Icc L (L + 1),
        |q E - vacuumLeading a E j| ≤ exp (7 * sqrt (a * E))) →
      1 ≤ realTailMomentDegree K a m ∧
      ∃ cell : TailCell j L (realTailMomentDegree K a m) q,
        cell.residual.variation.real univ ≤ 12 * exp (4 * π * (a + L)) ∧
        log (2 + cell.residual.variation.real univ) ≤ (4 * π + 14) * (a + L) := by
  filter_upwards [eventually_exists_tailCell ht
    (show 0 < 3 * ((K : ℝ) + 1) by positivity), eventually_ge_atTop (1 : ℝ)]
      with a hcell ha
  intro m L htL hmL _ j hj q hq herror
  exact ⟨realTailMomentDegree_pos hK a,
    hcell L htL j hj _ (realTailMomentDegree_add_one_le ha hmL) q hq herror⟩

/-- Deterministic natural threshold for a fixed real ray and moment multiplier. -/
def realTailCellThreshold {t : ℝ} (ht : 0 < t) {K : ℕ} (hK : 0 < K) : ℕ :=
  ⌈Classical.choose (eventually_atTop.mp (eventually_realTailCell ht hK))⌉₊

theorem realTailCellThreshold_spec {t : ℝ} (ht : 0 < t) {K : ℕ} (hK : 0 < K)
    {a : ℝ} (ha : (realTailCellThreshold ht hK : ℝ) ≤ a)
    (m : ℕ) (L : ℝ) (htL : t * a ≤ L) (hmL : (m : ℝ) ≤ L)
    (hLm : L < (m : ℝ) + 1) (j : ℤ) (hj : |(j : ℝ)| ≤ L)
    (q : ℝ → ℝ) (hq : IntegrableOn q (Ioo L (L + 1)) (referenceMeasure j))
    (herror : ∀ E ∈ Icc L (L + 1),
      |q E - vacuumLeading a E j| ≤ exp (7 * sqrt (a * E))) :
    1 ≤ realTailMomentDegree K a m ∧
    ∃ cell : TailCell j L (realTailMomentDegree K a m) q,
      cell.residual.variation.real univ ≤ 12 * exp (4 * π * (a + L)) ∧
      log (2 + cell.residual.variation.real univ) ≤ (4 * π + 14) * (a + L) := by
  have h := Classical.choose_spec
    (eventually_atTop.mp (eventually_realTailCell ht hK))
  exact h a ((Nat.le_ceil _).trans ha) m L htL hmL hLm j hj q hq herror

/-- The same choice serves every physical density obeying the invariant. -/
def selectedRealTailCell {t : ℝ} (ht : 0 < t) {K : ℕ} (hK : 0 < K)
    {a : ℝ} (ha : (realTailCellThreshold ht hK : ℝ) ≤ a)
    {m : ℕ} {L : ℝ} (htL : t * a ≤ L) (hmL : (m : ℝ) ≤ L)
    (hLm : L < (m : ℝ) + 1) {j : ℤ} (hj : |(j : ℝ)| ≤ L)
    {q : ℝ → ℝ} (hq : IntegrableOn q (Ioo L (L + 1)) (referenceMeasure j))
    (herror : ∀ E ∈ Icc L (L + 1),
      |q E - vacuumLeading a E j| ≤ exp (7 * sqrt (a * E))) :
    TailCell j L (realTailMomentDegree K a m) q :=
  Classical.choose (realTailCellThreshold_spec ht hK ha m L htL hmL hLm j hj q hq herror).2

/-- The deterministic cell retains both ordinary variation estimates. -/
theorem selectedRealTailCell_spec {t : ℝ} (ht : 0 < t) {K : ℕ} (hK : 0 < K)
    {a : ℝ} (ha : (realTailCellThreshold ht hK : ℝ) ≤ a)
    {m : ℕ} {L : ℝ} (htL : t * a ≤ L) (hmL : (m : ℝ) ≤ L)
    (hLm : L < (m : ℝ) + 1) {j : ℤ} (hj : |(j : ℝ)| ≤ L)
    {q : ℝ → ℝ} (hq : IntegrableOn q (Ioo L (L + 1)) (referenceMeasure j))
    (herror : ∀ E ∈ Icc L (L + 1),
      |q E - vacuumLeading a E j| ≤ exp (7 * sqrt (a * E))) :
    (selectedRealTailCell ht hK ha htL hmL hLm hj hq herror).residual.variation.real univ ≤
        12 * exp (4 * π * (a + L)) ∧
      log (2 + (selectedRealTailCell ht hK ha htL hmL hLm hj hq herror).residual.variation.real
        univ) ≤ (4 * π + 14) * (a + L) :=
  Classical.choose_spec
    (realTailCellThreshold_spec ht hK ha m L htL hmL hLm j hj q hq herror).2

end GapFamily.Construction
