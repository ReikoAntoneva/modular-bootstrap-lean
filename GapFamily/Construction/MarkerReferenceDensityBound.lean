import GapFamily.Construction.MarkerReferenceDensity
import GapFamily.Construction.MarkerReferenceExteriorBound
import GapFamily.Construction.MarkerReferenceCompactMass
import GapFamily.Analytic.Foundation.NegativeDensityIntegral

/-! Actual ordinary reference density bounds, including finite negative mass
on the low-spin rows. The growing positive density is never treated as a
finite signed measure without thermal or compact restriction. -/

noncomputable section

open MeasureTheory Set Real
open GapFamily.Analytic

namespace GapFamily.Construction

/-- Beyond the chosen reference radius, the literal ordinary density has the
actual vacuum approximation bound. -/
theorem canonicalMarkerReferenceDensity_uniform_error
    (a b : ℝ) (ha : 2 ≤ a) (hb : 1 ≤ b) (e : ℝ) (j : ℤ)
    (hnb : (markerReferenceBandThreshold : ℝ) ≤ b) (hba : b ≤ a)
    (he : (markerReferenceRadius : ℝ) * b ≤ e) (hj : |(j : ℝ)| ≤ e) :
    |canonicalMarkerReferenceDensity a b ha hb j e - vacuumLeading a e j| ≤
      exp (7 * sqrt (a * e)) / 2 := by
  have hR : (3 : ℝ) < markerReferenceRadius := by exact_mod_cast markerReferenceRadius_gt_three
  have h3 : 3 * b < e :=
    (mul_lt_mul_of_pos_right hR (by linarith : 0 < b)).trans_le he
  rw [canonicalMarkerReferenceDensity_eq_kernelNumerator a b ha hb j h3]
  exact canonicalMarkerReferenceKernelNumerator_uniform_error a b ha hb e j hnb hba he hj

/-- The genuine ordinary reference retains its exponential edge factor. -/
theorem canonicalMarkerReferenceDensity_lower
    (a b : ℝ) (ha : 2 ≤ a) (hb : 1 ≤ b) (e : ℝ) (j : ℤ)
    (hnb : (markerReferenceBandThreshold : ℝ) ≤ b) (hba : b ≤ a)
    (he : (markerReferenceRadius : ℝ) * b ≤ e) (hedge : |(j : ℝ)| + 1 ≤ e) :
    (π ^ 4 / 625) * (e ^ 2 - (j : ℝ) ^ 2) * exp (8 * sqrt (a * e)) ≤
      canonicalMarkerReferenceDensity a b ha hb j e := by
  have ha100 : 100 ≤ a := by
    have ht : (100 : ℝ) ≤ markerReferenceBandThreshold := by
      exact_mod_cast markerReferenceBandThreshold_ge_hundred
    exact ht.trans (hnb.trans hba)
  apply referenceDensity_lower_of_vacuum_error j ha100 hedge
    (canonicalMarkerReferenceDensity a b ha hb j)
  exact (canonicalMarkerReferenceDensity_uniform_error a b ha hb e j hnb hba he
    (by linarith)).trans (by have := exp_pos (7 * sqrt (a * e)); linarith)

/-- On every low-spin row, the actual reference is positive after `T + 1`,
where `T` is the universally enlarged reference threshold. -/
theorem canonicalMarkerReferenceDensity_pos_above
    (a b : ℝ) (ha : 2 ≤ a) (hb : 1 ≤ b) (j : ℤ)
    (hnb : (markerReferenceBandThreshold : ℝ) ≤ b) (hba : b ≤ a)
    (hj : |(j : ℝ)| ≤ (markerReferenceRadius : ℝ) * b)
    {e : ℝ} (he : (markerReferenceRadius : ℝ) * b + 1 ≤ e) :
    0 < canonicalMarkerReferenceDensity a b ha hb j e := by
  have hedge : |(j : ℝ)| + 1 ≤ e := by linarith
  have hedgesq := one_le_energy_sq_sub_spin_sq j hedge
  exact lt_of_lt_of_le (by positivity)
    (canonicalMarkerReferenceDensity_lower a b ha hb e j hnb hba (by linarith) hedge)

private theorem canonicalMarkerReferenceDensity_nonneg_off_cutoff
    (a b : ℝ) (ha : 2 ≤ a) (hb : 1 ≤ b) (j : ℤ)
    (hnb : (markerReferenceBandThreshold : ℝ) ≤ b) (hba : b ≤ a)
    (hj : |(j : ℝ)| ≤ (markerReferenceRadius : ℝ) * b) :
    ∀ᵐ e ∂(referenceMeasure j).restrict
      (Ioo |(j : ℝ)| ((markerReferenceRadius : ℝ) * b + 1))ᶜ,
      0 ≤ canonicalMarkerReferenceDensity a b ha hb j e := by
  filter_upwards [ae_restrict_of_ae (referenceMeasure_ae_above_edge j),
    ae_restrict_mem measurableSet_Ioo.compl] with e hedge hout
  have he : (markerReferenceRadius : ℝ) * b + 1 ≤ e := by
    by_contra h
    exact hout ⟨hedge, lt_of_not_ge h⟩
  exact (canonicalMarkerReferenceDensity_pos_above a b ha hb j hnb hba hj he).le

/-- The actual negative density is ordinarily integrable even though the
positive reference density has unbounded exponential growth. -/
theorem canonicalMarkerReferenceDensity_negativePart_integrable
    (a b : ℝ) (ha : 2 ≤ a) (hb : 1 ≤ b) (j : ℤ)
    (hnb : (markerReferenceBandThreshold : ℝ) ≤ b) (hba : b ≤ a)
    (hj : |(j : ℝ)| ≤ (markerReferenceRadius : ℝ) * b) :
    Integrable (fun e => max (-canonicalMarkerReferenceDensity a b ha hb j e) 0)
      (referenceMeasure j) :=
  integrable_negPart_of_local measurableSet_Ioo
    (canonicalMarkerReferenceDensity_integrable a b
      ((markerReferenceRadius : ℝ) * b + 1) ha hb j)
    (canonicalMarkerReferenceDensity_nonneg_off_cutoff a b ha hb j hnb hba hj)

/-- All ordinary negative mass lies below the fixed physical cutoff `T + 1`. -/
theorem canonicalMarkerReferenceDensity_negativeMass_eq_cutoff
    (a b : ℝ) (ha : 2 ≤ a) (hb : 1 ≤ b) (j : ℤ)
    (hnb : (markerReferenceBandThreshold : ℝ) ≤ b) (hba : b ≤ a)
    (hj : |(j : ℝ)| ≤ (markerReferenceRadius : ℝ) * b) :
    (∫ e, max (-canonicalMarkerReferenceDensity a b ha hb j e) 0 ∂referenceMeasure j) =
      ∫ e in Ioo |(j : ℝ)| ((markerReferenceRadius : ℝ) * b + 1),
        max (-canonicalMarkerReferenceDensity a b ha hb j e) 0 ∂referenceMeasure j :=
  integral_negPart_eq_setIntegral measurableSet_Ioo
    (canonicalMarkerReferenceDensity_nonneg_off_cutoff a b ha hb j hnb hba hj)

end GapFamily.Construction
