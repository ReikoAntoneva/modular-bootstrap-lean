import BTZEntropy.Comparison.CellMassTotal
import BTZEntropy.Comparison.DiscreteReferenceScale
import BTZEntropy.Construction.FixedFamilyActual

/-!
# Uniform quadrature error for the actual fixed family

The packet retains every chosen unit-node occurrence and the true numerator
of the state immediately before its cell. The admitted degree schedule,
disjoint-cell mass bound and charge normalization give every inverse power
uniformly in the marker, selector, finite cell set and descendant cutoff.
-/

noncomputable section

open Set MeasureTheory Real
open GapFamily GapFamily.Analytic GapFamily.Construction
open scoped BigOperators

namespace BTZEntropy.Comparison

namespace FixedFamilyDatum

variable {B : ℝ} {g : Construction.FixedFamilyGeometry B} {a : ℝ} {δ : ℝ}
  (d : Construction.FixedFamilyDatum g a δ)

/-- Actual emitted descendant packet minus the continuum packet used to
choose exactly those cells, with the same complete preceding state. -/
def activeCellQuadraturePacket (φ : SmoothKernel) (E : ℝ)
    (F : Finset (ℕ × ℕ)) (I : Finset (d.tail.ActiveSlot d.initialState)) : ℝ :=
  (∑ p ∈ I, scheduledCellTest d.tail d.initialState
    (fun q => primaryDescendantTest φ E F q.1) p.val) -
    ∑ p ∈ I, ∫ e in
      Ioo ((d.tail.slotPreState d.initialState p.val).front p.val.row)
        (d.tail.activeCell d.initialState p).right,
      (d.tail.slotPreState d.initialState p.val).numerator p.val.row e *
        primaryDescendantTest φ E F e ∂referenceMeasure p.val.row

end FixedFamilyDatum

/-- Compact support supplies a symmetric nonnegative radius. -/
theorem exists_kernel_support_radius (φ : SmoothKernel) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ v, φ v ≠ 0 → |v| ≤ R := by
  obtain ⟨A, hA⟩ := φ.compactSupport.bddAbove
  obtain ⟨Z, hZ⟩ := φ.compactSupport.bddBelow
  refine ⟨max |A| |Z|, (abs_nonneg A).trans (le_max_left _ _), ?_⟩
  intro v hv
  have ht := subset_tsupport φ hv
  apply abs_le.mpr
  constructor
  · have hz : -|Z| ≤ v := (neg_abs_le Z).trans (hZ ht)
    exact (neg_le_neg (le_max_right |A| |Z|)).trans hz
  · exact ((hA ht).trans (le_abs_self A)).trans (le_max_left _ _)

/-- A single kernel-dependent constant bounds every actual datum whose
retained moment degrees dominate its charge. The bound includes arbitrary
finite active-cell sets and both descendant cutoffs. -/
theorem exists_activeCell_quadrature_btzScale (φ : SmoothKernel)
    {L U : ℝ} (hL : 0 < L) (hLU : L ≤ U) (P : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {B : ℝ} {g : Construction.FixedFamilyGeometry B}
      {a : ℝ} {δ : ℝ} (d : Construction.FixedFamilyDatum g a δ),
      (∀ m, shift (gapFamilyCharge a) ≤ (d.tailDegree m : ℝ)) →
      ∀ (x : ℝ), x ∈ Icc L U → ∀ (F : Finset (ℕ × ℕ))
        (I : Finset (d.tail.ActiveSlot d.initialState)),
      |FixedFamilyDatum.activeCellQuadraturePacket d φ (x * gapFamilyCharge a) F I| ≤
        C * exp (leadingAction x (gapFamilyCharge a)) /
          (sqrt (gapFamilyCharge a) * gapFamilyCharge a ^ P) := by
  obtain ⟨R, hR0, hR⟩ := exists_kernel_support_radius φ
  let D : ℝ := R + 13 / 12
  let V : ℝ := 13 * U + D
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hU : 0 < U := hL.trans_le hLU
  have hV : 0 < V := by dsimp [V]; positivity
  obtain ⟨C₀, hC₀, hpacket⟩ := exists_uniform_relevantPacket_exp_error_le φ (P + 4) V hV
  obtain ⟨C, hC, hscale⟩ := discreteReference_gapFamilyCharge_le hL hLU hR0 hC₀ P
  refine ⟨C, hC.le, ?_⟩
  intro B g a δ d hdegree x hx F I
  have ha : 100 ≤ shift (gapFamilyCharge a) := d.charge_large
  have ha1 : 1 ≤ shift (gapFamilyCharge a) := by linarith
  have hcdef : gapFamilyCharge a = 12 * shift (gapFamilyCharge a) + 1 := by
    rw [shift_gapFamilyCharge]
    rfl
  have hc0 : 0 ≤ gapFamilyCharge a := by rw [hcdef]; positivity
  have hc13 : gapFamilyCharge a ≤ 13 * shift (gapFamilyCharge a) := by
    linarith only [hcdef, ha1]
  have hx0 : 0 < x := hL.trans_le hx.1
  have hX : 0 < x * gapFamilyCharge a + R + 13 / 12 := by positivity
  have hXV : x * gapFamilyCharge a + R + 13 / 12 ≤
      V * shift (gapFamilyCharge a) := by
    calc
      _ = x * gapFamilyCharge a + D := by dsimp [D]; ring
      _ ≤ U * (13 * shift (gapFamilyCharge a)) + D * shift (gapFamilyCharge a) :=
        add_le_add (mul_le_mul hx.2 hc13 hc0 hU.le) (le_mul_of_one_le_right hD ha1)
      _ = _ := by dsimp [V]; ring
  have hp := hpacket (shift (gapFamilyCharge a)) g.upper ha g.start d.tailDegree d.tail
    (show (1 : ℝ) ≤ g.start by exact_mod_cast g.start_pos) hdegree d.initialState I
    (x * gapFamilyCharge a) R F hR hX hXV
  have hp' : |FixedFamilyDatum.activeCellQuadraturePacket d φ (x * gapFamilyCharge a) F I| ≤
      C₀ * (1 + (x * gapFamilyCharge a + R + 13 / 12)) ^ 2 *
        exp (4 * π * sqrt (a *
          (x * gapFamilyCharge a + R + 13 / 12))) / (1 + a) ^ (P + 4) := by
    simpa only [FixedFamilyDatum.activeCellQuadraturePacket, shift_gapFamilyCharge] using hp
  exact hp'.trans (hscale a (by simpa using (show 0 ≤ shift (gapFamilyCharge a) by linarith)) x hx)

/-- Admission itself supplies the degree bound for the literal selected
datum. No local error or continuum-positivity premise is needed. -/
theorem fixedFamily_selected_tailDegree_ge_charge
    {B : ℝ} {σ : Construction.ActualFixedFamilySelector B}
    (hσ : σ ∈ Construction.fixedFamilySelectors B) {a : ℝ}
    (hK : Construction.fixedFamilyThreshold B ≤ a) {δ : ℝ}
    (hδ : δ ∈ Ico (0 : ℝ) B) (m : ℕ) :
    shift (gapFamilyCharge a) ≤ ((σ a hK δ hδ).tailDegree m : ℝ) := by
  have hschedule := (Construction.fixedFamily_selected_admission hσ hK hδ).1.tail_degree
  rw [hschedule]
  exact realTailMomentDegree_ge_charge canonicalTailMomentMultiplier_pos _ _

/-- The common quadrature bound holds for every admitted selector and
marker at every charge where that actual family is defined. -/
theorem exists_fixedFamily_selected_quadrature_btzScale (B : ℝ) (φ : SmoothKernel)
    {L U : ℝ} (hL : 0 < L) (hLU : L ≤ U) (P : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ σ ∈ Construction.fixedFamilySelectors B,
      ∀ (a : ℝ) (hK : Construction.fixedFamilyThreshold B ≤ a),
      ∀ (δ : ℝ) (hδ : δ ∈ Ico (0 : ℝ) B),
      ∀ (x : ℝ), x ∈ Icc L U → ∀ (F : Finset (ℕ × ℕ))
        (I : Finset ((σ a hK δ hδ).tail.ActiveSlot (σ a hK δ hδ).initialState)),
      |FixedFamilyDatum.activeCellQuadraturePacket (σ a hK δ hδ) φ
          (x * gapFamilyCharge a) F I| ≤
        C * exp (leadingAction x (gapFamilyCharge a)) /
          (sqrt (gapFamilyCharge a) * gapFamilyCharge a ^ P) := by
  obtain ⟨C, hC, hbound⟩ := exists_activeCell_quadrature_btzScale φ hL hLU P
  refine ⟨C, hC, ?_⟩
  intro σ hσ a hK δ hδ x hx F I
  exact hbound (σ a hK δ hδ) (fixedFamily_selected_tailDegree_ge_charge hσ hK hδ)
    x hx F I

end BTZEntropy.Comparison
