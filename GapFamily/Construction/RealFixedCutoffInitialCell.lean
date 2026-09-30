import GapFamily.Construction.RealInitialCell
import GapFamily.Construction.FixedCutoffReferenceDensityMass

/-!
# Initial cells with an independently prescribed marker

The actual transferred marker reference satisfies the signed-mass and positive-density
hypotheses. The remaining interface consists only of numerical inequalities
for the real vacuum, gap, endpoint, and natural degree.
-/

noncomputable section

open Set MeasureTheory Real
open GapFamily.Analytic

namespace GapFamily.Construction

/-- The canonical reference supplies genuine integer-mass cells for real
`a` and cutoff `b`, uniformly in the marker `δ ∈ [0,b]`. Its numerical degree threshold is independent of these scales.
All analytic density and endpoint-existence premises are discharged. -/
theorem exists_realFixedCutoffInitialCell_threshold {D : ℝ} (hD : 0 ≤ D) :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k → ∀ a b δ U : ℝ,
      ∀ (ha : 2 ≤ a) (hb : 1 ≤ b),
      0 ≤ δ → δ ≤ b →
      (fixedCutoffReferenceBandThreshold : ℝ) ≤ b → b ≤ a →
      16 ≤ U → 2 / (π ^ 4 / 625) < U →
      (fixedCutoffReferenceRadius : ℝ) * b ≤ U / 16 →
      1 + a ≤ D * ((k : ℝ) + 1) →
      fixedCutoffReferenceNegativeExponent * sqrt (a * b) ≤ (k : ℝ) →
      (k : ℝ) ≤ sqrt (a * U) →
      ∀ j : ℤ, |(j : ℝ)| ≤ (fixedCutoffReferenceRadius : ℝ) * b →
      Nonempty (InitialReferenceCell j (max b |(j : ℝ)|) U k
        (fixedCutoffReferenceDensity a b δ ha hb j)) := by
  obtain ⟨k₀, hk₀⟩ := exists_realInitialReferenceCell_threshold_of_bounds
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

end GapFamily.Construction
