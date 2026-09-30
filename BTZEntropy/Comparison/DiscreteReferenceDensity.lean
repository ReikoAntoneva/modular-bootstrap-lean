import BTZEntropy.Comparison.DensityErrorUniform
import BTZEntropy.Comparison.DensityErrorCell
import BTZEntropy.Comparison.DiscreteReferenceScale
import GapFamily.Construction.RealTailCellThermal

/-! Density comparison for the literal cells in a fixed-cutoff construction.
Each integral uses the numerator from its own preceding repair state. -/

noncomputable section

open Set Filter MeasureTheory Real
open GapFamily GapFamily.Analytic GapFamily.Construction
open scoped BigOperators

namespace BTZEntropy.Comparison
namespace FixedFamilyDatum

variable {B : ℝ} {g : BTZEntropy.Construction.FixedFamilyGeometry B}
  {a : ℝ} {δ : ℝ} (d : BTZEntropy.Construction.FixedFamilyDatum g a δ)

/-- The literal signed density difference at the state immediately before
an active cell is constructed. -/
def activeCellDensityError (p : d.tail.ActiveSlot d.initialState) (e : ℝ) : ℝ :=
  finiteStateDensityError (shift (gapFamilyCharge a))
    (d.tail.slotPreState d.initialState p.val) p.val.row e

/-- The finite sum of density errors uses the same descendant packet in
every actual cell and retains the complete finite repair history. -/
def activeCellDensityErrorPacket (φ : SmoothKernel) (E : ℝ)
    (F : Finset (ℕ × ℕ)) (I : Finset (d.tail.ActiveSlot d.initialState)) : ℝ :=
  ∑ p ∈ I, ∫ e in
    Ioo ((d.tail.slotPreState d.initialState p.val).front p.val.row)
      (d.tail.activeCell d.initialState p).right,
    FixedFamilyDatum.activeCellDensityError d p e * primaryDescendantTest φ E F e
      ∂referenceMeasure p.val.row

/-- Actual active cells begin above energy one and the physical spin edge. -/
theorem activeCell_front_one (p : d.tail.ActiveSlot d.initialState) :
    1 ≤ (d.tail.slotPreState d.initialState p.val).front p.val.row :=
  (show (1 : ℝ) ≤ (g.start : ℝ) by exact_mod_cast g.start_pos).trans
    (d.tail.activeCell_front_lower d.initialState p)

/-- The scheduler's local invariant bounds the numerator used in this
particular cell, throughout its full closed interval. -/
theorem activeCell_densityError_bound (p : d.tail.ActiveSlot d.initialState)
    {e : ℝ} (he : e ∈ Icc
      ((d.tail.slotPreState d.initialState p.val).front p.val.row)
      (d.tail.activeCell d.initialState p).right) :
    |FixedFamilyDatum.activeCellDensityError d p e| ≤
      exp (7 * sqrt (shift (gapFamilyCharge a) * e)) :=
  p.property.envelope e ⟨he.1,
    he.2.trans (d.tail.activeCell d.initialState p).right_mem.2⟩

/-- The density-error integral on every actual cell is an ordinary
integrable function, with no additional analytic premise on the datum. -/
theorem activeCell_densityError_integrable (φ : SmoothKernel)
    (E : ℝ) (F : Finset (ℕ × ℕ)) (p : d.tail.ActiveSlot d.initialState) :
    IntegrableOn (fun e => FixedFamilyDatum.activeCellDensityError d p e *
      primaryDescendantTest φ E F e)
      (Ioo ((d.tail.slotPreState d.initialState p.val).front p.val.row)
        (d.tail.activeCell d.initialState p).right) (referenceMeasure p.val.row) := by
  obtain ⟨R, H, hR0, hH, hR, hφ⟩ := exists_kernel_upper_bound φ
  have htest (e : ℝ) (he : 0 ≤ e) : primaryDescendantTest φ E F e ≤
      H * exp ((E + R + 1 / 12 + 4) * sqrt 1) := by
    simpa only [mul_one] using primaryDescendantTest_le_sqrt φ F he
      (show (1 : ℝ) ≤ 1 by rfl) (le_refl E) hR0 hH hR hφ
  apply densityErrorRow_integrable φ E R (shift (gapFamilyCharge a))
    (H * exp ((E + R + 1 / 12 + 4) * sqrt 1)) F
    (finiteStateDensityError (shift (gapFamilyCharge a))
      (d.tail.slotPreState d.initialState p.val))
    (d.tail.slotPreState d.initialState p.val).front
    (d.tail.activeCell d.initialState p).right p.val.row
    (by linarith [d.charge_large]) (by positivity)
    (FixedFamilyDatum.activeCell_front_one d p) p.property.physical hR
    htest
    (finiteStateDensityError_aestronglyMeasurable _ _ p.property.thermal p.val.row)
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with e he
  exact FixedFamilyDatum.activeCell_densityError_bound d p ⟨he.1.le, he.2.le⟩

/-- The local density error is exactly the difference of the actual old
continuum test and the leading vacuum test on the same cell. -/
theorem activeCell_densityError_integral_eq (φ : SmoothKernel) (E : ℝ)
    (F : Finset (ℕ × ℕ)) (p : d.tail.ActiveSlot d.initialState) :
    (∫ e in Ioo ((d.tail.slotPreState d.initialState p.val).front p.val.row)
        (d.tail.activeCell d.initialState p).right,
      activeCellDensityError d p e * primaryDescendantTest φ E F e
        ∂referenceMeasure p.val.row) =
      (∫ e in Ioo ((d.tail.slotPreState d.initialState p.val).front p.val.row)
          (d.tail.activeCell d.initialState p).right,
        (d.tail.slotPreState d.initialState p.val).numerator p.val.row e *
          primaryDescendantTest φ E F e ∂referenceMeasure p.val.row) -
      (∫ e in Ioo ((d.tail.slotPreState d.initialState p.val).front p.val.row)
          (d.tail.activeCell d.initialState p).right,
        vacuumLeading (shift (gapFamilyCharge a)) e p.val.row *
          primaryDescendantTest φ E F e ∂referenceMeasure p.val.row) := by
  have hn := (cellResidualMeasure_integral_continuous p.val.row
    ((d.tail.slotPreState d.initialState p.val).front p.val.row)
    (d.tail.activeCell d.initialState p).right (d.tail.activeCell d.initialState p).node
    (d.tail.activeCell d.initialState p).density_integrable
    (continuous_primaryDescendantTest φ E F)).2.1
  have he := activeCell_densityError_integrable d φ E F p
  have href := (hn.sub he).congr (Filter.Eventually.of_forall (fun e =>
    show (d.tail.slotPreState d.initialState p.val).numerator p.val.row e *
        primaryDescendantTest φ E F e -
        activeCellDensityError d p e * primaryDescendantTest φ E F e =
      vacuumLeading (shift (gapFamilyCharge a)) e p.val.row *
        primaryDescendantTest φ E F e by
      simp only [activeCellDensityError, finiteStateDensityError]
      ring))
  simp only [activeCellDensityError, finiteStateDensityError, sub_mul]
  exact integral_sub hn href

/-- Summing the local identity keeps exactly the active cells selected for
the discrete-reference comparison. -/
theorem activeCell_densityErrorPacket_eq_sub (φ : SmoothKernel) (E : ℝ)
    (F : Finset (ℕ × ℕ)) (I : Finset (d.tail.ActiveSlot d.initialState)) :
    activeCellDensityErrorPacket d φ E F I =
      (∑ p ∈ I, ∫ e in
        Ioo ((d.tail.slotPreState d.initialState p.val).front p.val.row)
          (d.tail.activeCell d.initialState p).right,
        (d.tail.slotPreState d.initialState p.val).numerator p.val.row e *
          primaryDescendantTest φ E F e ∂referenceMeasure p.val.row) -
      (∑ p ∈ I, ∫ e in
        Ioo ((d.tail.slotPreState d.initialState p.val).front p.val.row)
          (d.tail.activeCell d.initialState p).right,
        vacuumLeading (shift (gapFamilyCharge a)) e p.val.row *
          primaryDescendantTest φ E F e ∂referenceMeasure p.val.row) := by
  simp only [activeCellDensityErrorPacket, activeCell_densityError_integral_eq,
    Finset.sum_sub_distrib]

/-- Patch the literal finite family by zero outside its actual cells. -/
def activeCellDensityErrorPatch (I : Finset (d.tail.ActiveSlot d.initialState)) :
    ℤ → ℝ → ℝ :=
  patchedDensityError I (fun p => p.val.row)
    (fun p => (d.tail.slotPreState d.initialState p.val).front p.val.row)
    (fun p => (d.tail.activeCell d.initialState p).right) (activeCellDensityError d)

/-- Same-row disjointness prevents any loss proportional to the number of
cells in the patched density envelope. -/
theorem activeCell_densityErrorPatch_bound
    (I : Finset (d.tail.ActiveSlot d.initialState)) (j : ℤ) (e : ℝ) :
    |FixedFamilyDatum.activeCellDensityErrorPatch d I j e| ≤
      exp (7 * sqrt (shift (gapFamilyCharge a) * e)) := by
  apply patchedDensityError_abs_le_exp I _ _ _ _ _
  · intro p hp q hq hpq hrow
    exact d.tail.activeCell_pairwise_disjoint d.initialState hpq hrow
  · intro p hp e he
    exact FixedFamilyDatum.activeCell_densityError_bound d p ⟨he.1.le, he.2.le⟩

/-- The patched full-spin test is exactly the sum of the original local
integrals, with ordinary integrability proved from the actual cells. -/
theorem activeCell_densityErrorPacket_eq (φ : SmoothKernel) (E : ℝ)
    (F : Finset (ℕ × ℕ)) (I : Finset (d.tail.ActiveSlot d.initialState)) :
    FixedFamilyDatum.activeCellDensityErrorPacket d φ E F I =
      densityErrorFullPacket φ E F (FixedFamilyDatum.activeCellDensityErrorPatch d I)
        (fun j => max 1 |(j : ℝ)|) := by
  symm
  apply densityErrorFullPacket_patchedDensityError
  · intro p hp
    exact max_le (FixedFamilyDatum.activeCell_front_one d p) p.property.physical
  · intro p hp
    exact FixedFamilyDatum.activeCell_densityError_integrable d φ E F p

end FixedFamilyDatum

/-- All literal preceding-state density errors, over an arbitrary finite
family of active cells and descendant levels, have a common inverse-power
threshold at every sufficiently large real charge. -/
theorem activeCell_densityError_eventually_inverse_pow (φ : SmoothKernel)
    {L U R H : ℝ} (hL : 0 < L) (hLU : L ≤ U) (hR0 : 0 ≤ R) (hH : 0 ≤ H)
    (hR : ∀ u, φ u ≠ 0 → u ≤ R) (hφ : ∀ u, φ u ≤ H) (P : ℕ) :
    ∀ᶠ a : ℝ in atTop, ∀ {B : ℝ} {g : BTZEntropy.Construction.FixedFamilyGeometry B}
      {δ : ℝ} (d : BTZEntropy.Construction.FixedFamilyDatum g a δ)
      (F : Finset (ℕ × ℕ)) (I : Finset (d.tail.ActiveSlot d.initialState))
      (x : ℝ), x ∈ Icc L U →
      |FixedFamilyDatum.activeCellDensityErrorPacket d φ (x * gapFamilyCharge a) F I| /
        exp (2 * π * gapFamilyCharge a * sqrt (x / 3)) ≤
          1 / gapFamilyCharge a ^ P := by
  have hr := tendsto_gapFamilyCharge_atTop.eventually
    (densityErrorFullPacket_eventually_inverse_pow φ hL hLU hR0 hH hR hφ P)
  filter_upwards [hr] with a ha
  intro B g δ d F I x hx
  rw [FixedFamilyDatum.activeCell_densityErrorPacket_eq d]
  exact ha x hx F _ _ (fun j => le_max_left _ _) (fun j => le_max_right _ _)
    (fun j => Filter.Eventually.of_forall (fun e he =>
      FixedFamilyDatum.activeCell_densityErrorPatch_bound d I j e))

private theorem densityError_normalize_exp_bound {A c E : ℝ} (P : ℕ) (hc : 1 ≤ c)
    (h : A / exp E ≤ 1 / c ^ (P + 1)) :
    A / (exp E / sqrt c) ≤ 1 / c ^ P := by
  have hc0 : 0 < c := lt_of_lt_of_le zero_lt_one hc
  have hs : sqrt c ≤ c := sqrt_le_self_iff.mpr (Or.inr hc)
  calc
    A / (exp E / sqrt c) = (A / exp E) * sqrt c := by
      simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
      ring
    _ ≤ (1 / c ^ (P + 1)) * sqrt c :=
      mul_le_mul_of_nonneg_right h (sqrt_nonneg c)
    _ ≤ (1 / c ^ (P + 1)) * c :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    _ = 1 / c ^ P := by
      rw [pow_succ]
      field_simp

/-- The density error of the actual finite active-cell family is smaller
than every inverse power of the true BTZ counting scale. The common
threshold depends only on the prescribed kernel, ratio interval and order. -/
theorem activeCell_densityError_eventually_btzScale (φ : SmoothKernel)
    {L U : ℝ} (hL : 0 < L) (hLU : L ≤ U) (P : ℕ) :
    ∀ᶠ a : ℝ in atTop, ∀ {B : ℝ} {g : BTZEntropy.Construction.FixedFamilyGeometry B}
      {δ : ℝ} (d : BTZEntropy.Construction.FixedFamilyDatum g a δ)
      (F : Finset (ℕ × ℕ)) (I : Finset (d.tail.ActiveSlot d.initialState))
      (x : ℝ), x ∈ Icc L U →
      |FixedFamilyDatum.activeCellDensityErrorPacket d φ (x * gapFamilyCharge a) F I| ≤
        exp (leadingAction x (gapFamilyCharge a)) /
          (sqrt (gapFamilyCharge a) * gapFamilyCharge a ^ P) := by
  obtain ⟨R, H, hR0, hH, hR, hφ⟩ := exists_kernel_upper_bound φ
  filter_upwards [activeCell_densityError_eventually_inverse_pow φ hL hLU
    hR0 hH hR hφ (P + 1)] with a ha
  intro B g δ d F I x hx
  have hc : 1 ≤ gapFamilyCharge a := by
    have h := d.charge_large
    unfold shift at h
    linarith
  have hn := densityError_normalize_exp_bound P hc (ha d F I x hx)
  rw [← leadingAction_eq_btz] at hn
  have hp : 0 < exp (leadingAction x (gapFamilyCharge a)) /
      sqrt (gapFamilyCharge a) := div_pos (exp_pos _) (sqrt_pos.mpr (by linarith))
  have hb := (div_le_iff₀ hp).mp hn
  calc
    _ ≤ 1 / gapFamilyCharge a ^ P *
        (exp (leadingAction x (gapFamilyCharge a)) / sqrt (gapFamilyCharge a)) := hb
    _ = _ := by ring

end BTZEntropy.Comparison
