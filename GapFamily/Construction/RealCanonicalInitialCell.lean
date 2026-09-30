import GapFamily.Construction.RealInitialCell
import GapFamily.Construction.MarkerReferenceDensityMass

/-!
# Canonical initial cells at arbitrary real scales

The actual marker reference satisfies the signed-mass and positive-density
hypotheses. The remaining interface consists only of numerical inequalities
for the real vacuum, gap, endpoint, and natural degree.
-/

noncomputable section

open Set MeasureTheory Real
open GapFamily.Analytic

namespace GapFamily.Construction

/-- The canonical reference supplies genuine integer-mass cells for real
`a` and `b`. Its numerical degree threshold is independent of these scales.
All analytic density and endpoint-existence premises are discharged. -/
theorem exists_realCanonicalInitialCell_threshold {D : ℝ} (hD : 0 ≤ D) :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k → ∀ a b U : ℝ,
      ∀ (ha : 2 ≤ a) (hb : 1 ≤ b),
      (markerReferenceBandThreshold : ℝ) ≤ b → b ≤ a →
      16 ≤ U → 2 / (π ^ 4 / 625) < U →
      (markerReferenceRadius : ℝ) * b ≤ U / 16 →
      1 + a ≤ D * ((k : ℝ) + 1) →
      markerReferenceNegativeExponent * sqrt (a * b) ≤ (k : ℝ) →
      (k : ℝ) ≤ sqrt (a * U) →
      ∀ j : ℤ, |(j : ℝ)| ≤ (markerReferenceRadius : ℝ) * b →
      Nonempty (InitialReferenceCell j (max b |(j : ℝ)|) U k
        (canonicalMarkerReferenceDensity a b ha hb j)) := by
  obtain ⟨k₀, hk₀⟩ := exists_realInitialReferenceCell_threshold_of_bounds
    (show 0 < π ^ 4 / 625 by positivity) markerReferenceNegativeCoefficient_pos.le hD 9
  refine ⟨k₀, ?_⟩
  intro k hk a b U ha hb hnb hba hU hlarge hTU hpoly hnegative hpositive j hj
  have hR : (1 : ℝ) ≤ markerReferenceRadius := by
    exact_mod_cast (show 1 ≤ markerReferenceRadius by have := markerReferenceRadius_gt_three; omega)
  have hbT : b ≤ (markerReferenceRadius : ℝ) * b :=
    le_mul_of_one_le_left (by linarith) hR
  apply hk₀ k hk a b U markerReferenceNegativeExponent (by linarith) (by linarith)
    hlarge (hbT.trans hTU) hpoly hnegative hpositive j (hj.trans hTU)
    (canonicalMarkerReferenceDensity a b ha hb j)
  · exact IntegrableOn.mono_set (canonicalMarkerReferenceDensity_integrable a b (U + 1) ha hb j)
      (Ioo_subset_Ioo (le_max_right _ _) le_rfl)
  · exact (setIntegral_le_integral
      (canonicalMarkerReferenceDensity_negativePart_integrable a b ha hb j hnb hba hj)
      (Filter.Eventually.of_forall fun E => le_max_right _ _)).trans
      (canonicalMarkerReferenceDensity_negativeMass_le a b ha hb j hnb hba hj)
  · intro E hE
    apply canonicalMarkerReferenceDensity_lower a b ha hb E j hnb hba
    · linarith [hE.1]
    · linarith [hE.1]

end GapFamily.Construction
