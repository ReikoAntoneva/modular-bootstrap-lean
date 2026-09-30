import GapFamily.Construction.ProportionalInitialData
import GapFamily.Construction.RealInitialConstructionEndpoint
import GapFamily.Construction.RealLayerStart
import GapFamily.Construction.RealTailData
import GapFamily.GapFamilyLimit

/-!
# The complete proportional gap family

Actual initial cells and the actual recursive tail give an admissible
spectrum at every sufficiently large exact charge. The scalar marker is
the unique first primary and has multiplicity one.
-/

noncomputable section

open Set Filter MeasureTheory Real
open GapFamily.Analytic
open scoped BigOperators

namespace GapFamily.Construction

/-- The finite proportional initialization supplies every hypothesis of the
real tail construction, including the literal reference output and its
five-eighths error reserve. -/
theorem exists_spectrum_of_marker_initial_cells
    {a b U c t : ℝ} {k : ℕ} (ht : 0 < t)
    (hshift : shift c = a) (ha : 2 ≤ a) (hb : 1 ≤ b)
    (hU : 1 ≤ U) (hUa : U ≤ a)
    (hnb : (markerReferenceBandThreshold : ℝ) ≤ b) (hba : b ≤ a)
    (hTU : (markerReferenceRadius : ℝ) * b ≤ U)
    (htail : (realCanonicalTailThreshold ht : ℝ) ≤ a)
    (hray : t * a ≤ (⌊(markerReferenceRadius : ℝ) * b⌋₊ : ℝ))
    (cells : ∀ J : realInitialRows ((markerReferenceRadius : ℝ) * b),
      InitialReferenceCell J (max b |(J : ℝ)|) U k
        (canonicalMarkerReferenceDensity a b ha hb J))
    (hrepair : ∀ (j : ℤ) (e : ℝ), |(j : ℝ)| ≤ e →
      (∑ J, |if 2 * U + 4 < e then
        (cells J).exteriorNumerator (2 * U + 4) (by linarith) j e else 0|) ≤
        exp (7 * sqrt (a * e)) / 8) :
    ∃ spectrum : Spectrum, PureAdmissible c spectrum ∧
      HasUnitScalarGap spectrum (a + b) := by
  subst a
  let radius : ℝ := (markerReferenceRadius : ℝ) * b
  let T : ℕ := ⌊radius⌋₊
  have hR : (3 : ℝ) < markerReferenceRadius := by
    exact_mod_cast markerReferenceRadius_gt_three
  have hradius : 0 ≤ radius := by dsimp [radius]; positivity
  have hbT : b < (T : ℝ) := marker_lt_floor_layerStart hR hb
  have hT : 1 ≤ T := one_le_floor_layerStart hR hb
  let d := realTailLocalData ht htail hT hray (by linarith : 0 ≤ U) hUa
  apply exists_spectrum_of_real_initial_cells d
    (ReferenceOutput.canonicalMarker (shift c) b ha hb)
    (canonicalMarkerReferenceDensity (shift c) b ha hb) cells
    (by linarith) le_rfl hbT (realCanonicalTailThreshold_spec ht htail).1 hT
    (by linarith) hradius hTU (Nat.floor_le hradius)
  · exact fun j _ ht =>
      canonicalMarkerReferenceDensity_thermal_integrable (shift c) b ha hb j ht
  · exact canonicalMarkerReferenceDensity_ae_eq_zero_below_max (shift c) b ha hb
  · exact fun j _ ht =>
      canonicalMarkerReferenceThermalMeasure_eq_marker_add_density (shift c) b ha hb j ht
  · exact fun j e he => canonicalMarkerReferenceDensity_uniform_error (shift c) b ha hb e j
      hnb hba ((le_max_left _ _).trans he) ((le_max_right _ _).trans he)
  · exact hrepair

end GapFamily.Construction

namespace GapFamily

open Construction

/-- Theorem 2.2(i), including the complete real interval of ratios, the
all sufficiently large real charges, full character admissibility, unit scalar first
primary, and the strict normalized-dimension limit. -/
theorem proportionalGapFamilyExists : ProportionalGapFamilyExists := by
  apply proportionalGapFamilyExists_of_eventually_realizesGap
  obtain ⟨R, s, _, _, _, κ₀, hκ₀, hdata⟩ := exists_proportional_initial_data
  refine ⟨κ₀, hκ₀, ?_⟩
  intro κ hκ hκlt
  obtain ⟨a₀, _, ha₀⟩ := hdata κ hκ hκlt
  let t : ℝ := (markerReferenceRadius : ℝ) * κ / 2
  have hR : (3 : ℝ) < markerReferenceRadius := by
    exact_mod_cast markerReferenceRadius_gt_three
  have hRpos : (0 : ℝ) < markerReferenceRadius := by linarith
  have ht : 0 < t := by dsimp [t]; positivity
  filter_upwards [eventually_ge_atTop a₀,
    eventually_ge_atTop (realCanonicalTailThreshold ht : ℝ)] with a haThreshold htail
  obtain ⟨ha, hb, hU, hnb, hba, hTU, hUa, cells, hrepair⟩ := ha₀ a haThreshold
  have hradius : 2 ≤ (markerReferenceRadius : ℝ) * (κ * a) := by
    have h := mul_le_mul_of_nonneg_left hb (by linarith : (0 : ℝ) ≤ markerReferenceRadius)
    linarith
  exact exists_spectrum_of_marker_initial_cells ht (shift_gapFamilyCharge a) ha hb hU hUa
    hnb hba hTU htail (ray_le_floor_layerStart hradius) cells hrepair

end GapFamily
