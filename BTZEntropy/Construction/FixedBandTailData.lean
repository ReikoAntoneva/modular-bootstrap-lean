import BTZEntropy.Construction.FixedBandTailCell
import GapFamily.Construction.RealTailData

/-! Fixed-threshold local data for the actual canonical tail recursion.
The starting layer and cutoff stay fixed as the real charge tends to infinity. -/

noncomputable section
open Set MeasureTheory Real Filter
open GapFamily.Analytic GapFamily.Construction

namespace BTZEntropy.Construction

/-- A charge threshold for every physical signed cell above a fixed energy. -/
def fixedBandTailCellThreshold {T : ℝ} (hT : 10 ≤ T) {K : ℕ} (hK : 0 < K) : ℕ :=
  ⌈Classical.choose (eventually_atTop.mp (eventually_fixedTail_realTailCell hT hK))⌉₊

theorem fixedBandTailCellThreshold_spec {T : ℝ} (hT : 10 ≤ T) {K : ℕ} (hK : 0 < K)
    {a : ℝ} (ha : (fixedBandTailCellThreshold hT hK : ℝ) ≤ a)
    (m : ℕ) (L : ℝ) (hTL : T ≤ L) (hmL : (m : ℝ) ≤ L)
    (hLm : L < (m : ℝ) + 1) (j : ℤ) (hj : |(j : ℝ)| ≤ L)
    (q : ℝ → ℝ) (hq : IntegrableOn q (Ioo L (L + 1)) (referenceMeasure j))
    (herror : ∀ E ∈ Icc L (L + 1),
      |q E - vacuumLeading a E j| ≤ exp (7 * sqrt (a * E))) :
    1 ≤ realTailMomentDegree K a m ∧
    ∃ cell : TailCell j L (realTailMomentDegree K a m) q,
      cell.residual.variation.real univ ≤ 12 * exp (4 * π * (a + L)) ∧
      log (2 + cell.residual.variation.real univ) ≤ (4 * π + 14) * (a + L) := by
  have h := Classical.choose_spec
    (eventually_atTop.mp (eventually_fixedTail_realTailCell hT hK))
  exact h a ((Nat.le_ceil _).trans ha) m L hTL hmL hLm j hj q hq herror

/-- Deterministically selected actual cell at a fixed starting energy. -/
def selectedFixedBandTailCell {T : ℝ} (hT : 10 ≤ T) {K : ℕ} (hK : 0 < K)
    {a : ℝ} (ha : (fixedBandTailCellThreshold hT hK : ℝ) ≤ a)
    {m : ℕ} {L : ℝ} (hTL : T ≤ L) (hmL : (m : ℝ) ≤ L)
    (hLm : L < (m : ℝ) + 1) {j : ℤ} (hj : |(j : ℝ)| ≤ L)
    {q : ℝ → ℝ} (hq : IntegrableOn q (Ioo L (L + 1)) (referenceMeasure j))
    (herror : ∀ E ∈ Icc L (L + 1),
      |q E - vacuumLeading a E j| ≤ exp (7 * sqrt (a * E))) :
    TailCell j L (realTailMomentDegree K a m) q :=
  Classical.choose
    (fixedBandTailCellThreshold_spec hT hK ha m L hTL hmL hLm j hj q hq herror).2

theorem selectedFixedBandTailCell_spec {T : ℝ} (hT : 10 ≤ T) {K : ℕ} (hK : 0 < K)
    {a : ℝ} (ha : (fixedBandTailCellThreshold hT hK : ℝ) ≤ a)
    {m : ℕ} {L : ℝ} (hTL : T ≤ L) (hmL : (m : ℝ) ≤ L)
    (hLm : L < (m : ℝ) + 1) {j : ℤ} (hj : |(j : ℝ)| ≤ L)
    {q : ℝ → ℝ} (hq : IntegrableOn q (Ioo L (L + 1)) (referenceMeasure j))
    (herror : ∀ E ∈ Icc L (L + 1),
      |q E - vacuumLeading a E j| ≤ exp (7 * sqrt (a * E))) :
    (selectedFixedBandTailCell hT hK ha hTL hmL hLm hj hq herror).residual.variation.real
      univ ≤ 12 * exp (4 * π * (a + L)) ∧
    log (2 + (selectedFixedBandTailCell hT hK ha hTL hmL hLm hj hq herror).residual.variation.real
      univ) ≤ (4 * π + 14) * (a + L) :=
  Classical.choose_spec
    (fixedBandTailCellThreshold_spec hT hK ha m L hTL hmL hLm j hj q hq herror).2

/-- The canonical multiplier is fixed independently of the initial band and
the charge, while the threshold accommodates the fixed starting layer. -/
def fixedBandCanonicalTailThreshold {T : ℕ} (hT : 10 ≤ T) : ℕ :=
  max 100 (fixedBandTailCellThreshold (show (10 : ℝ) ≤ T by exact_mod_cast hT)
    canonicalTailMomentMultiplier_pos)

theorem fixedBandCanonicalTailThreshold_spec {T : ℕ} (hT : 10 ≤ T) {a : ℝ}
    (ha : (fixedBandCanonicalTailThreshold hT : ℝ) ≤ a) :
    100 ≤ a ∧
      (fixedBandTailCellThreshold (show (10 : ℝ) ≤ T by exact_mod_cast hT)
        canonicalTailMomentMultiplier_pos : ℝ) ≤ a := by
  have h100 : (100 : ℝ) ≤ (fixedBandCanonicalTailThreshold hT : ℝ) := by
    exact_mod_cast (le_max_left 100
      (fixedBandTailCellThreshold (show (10 : ℝ) ≤ T by exact_mod_cast hT)
        canonicalTailMomentMultiplier_pos))
  have hcell :
      (fixedBandTailCellThreshold (show (10 : ℝ) ≤ T by exact_mod_cast hT)
        canonicalTailMomentMultiplier_pos : ℝ) ≤ (fixedBandCanonicalTailThreshold hT : ℝ) := by
    exact_mod_cast (le_max_right 100
      (fixedBandTailCellThreshold (show (10 : ℝ) ≤ T by exact_mod_cast hT)
        canonicalTailMomentMultiplier_pos))
  exact ⟨h100.trans ha, hcell.trans ha⟩

/-- Actual recursion data at a fixed starting layer: every valid signed slot
gets a unit-node cell and its full canonical exterior repair estimate. -/
def fixedBandTailLocalData {a U : ℝ} {T : ℕ} (hT : 10 ≤ T)
    (ha : (fixedBandCanonicalTailThreshold hT : ℝ) ≤ a)
    (hU₀ : 0 ≤ U) (hUa : U ≤ a) :
    RealTailLocalData a U T (realTailMomentDegree canonicalTailMomentMultiplier a) where
  cutoff_nonneg := hU₀
  cell state m J h :=
    selectedFixedBandTailCell (show (10 : ℝ) ≤ T by exact_mod_cast hT)
      canonicalTailMomentMultiplier_pos
      (fixedBandCanonicalTailThreshold_spec hT ha).2
      ((by exact_mod_cast h.layer : (T : ℝ) ≤ m).trans h.front_lower)
      h.front_lower h.front_upper h.physical
      (state.integrableOn_numerator h.thermal J (state.front J) (state.front J + 1))
      h.envelope
  error state m J h j E hj hE := by
    apply TailCell.real_exteriorNumerator_le_slotBudget _
      (fixedBandCanonicalTailThreshold_spec hT ha).1
      ((by exact_mod_cast (show 1 ≤ m from (by omega : 1 ≤ T).trans h.layer) :
        (1 : ℝ) ≤ m).trans h.front_lower)
      h.front_upper h.physical hU₀ hUa h.envelope j E hj hE.le
      (canonicalTailChargeThreshold_real_spec a (fixedBandCanonicalTailThreshold_spec hT ha).1)
      canonicalTailMomentMultiplier_budget

/-- A fixed starting layer supports actual tail recursion data for every
cutoff below the charge, at one common charge threshold. -/
theorem eventually_fixedBandTailLocalData {T : ℕ} (hT : 10 ≤ T) :
    ∀ᶠ a : ℝ in atTop, ∀ U : ℝ, 0 ≤ U → U ≤ a →
      Nonempty (RealTailLocalData a U T
        (realTailMomentDegree canonicalTailMomentMultiplier a)) := by
  filter_upwards [eventually_ge_atTop (fixedBandCanonicalTailThreshold hT : ℝ)] with a ha
  intro U hU₀ hUa
  exact ⟨fixedBandTailLocalData hT ha hU₀ hUa⟩

/-- In particular, both the initial layer and the repair cutoff may stay
fixed while the charge tends to infinity. -/
theorem eventually_fixedBandTailLocalData_fixedCutoff {T : ℕ} (hT : 10 ≤ T)
    {U : ℝ} (hU : 0 ≤ U) :
    ∀ᶠ a : ℝ in atTop, Nonempty (RealTailLocalData a U T
      (realTailMomentDegree canonicalTailMomentMultiplier a)) := by
  filter_upwards [eventually_fixedBandTailLocalData hT, eventually_ge_atTop U] with a h ha
  exact h U hU ha

end BTZEntropy.Construction
