import GapFamily.Construction.FixedCutoffInitialData
import GapFamily.Construction.FixedCutoffReferenceOutput
import GapFamily.Construction.RealInitialConstructionEndpoint
import GapFamily.Construction.RealLayerStart
import GapFamily.Construction.RealTailData
import GapFamily.GapFamilyLimit

/-!
# The complete fixed gap family

A positive clearing cutoff grows along a fixed charge ray. The actual
marker-transfer reference places its one scalar atom at any prescribed
nonnegative energy, including zero. The initial cells and real tail
recursion then remove the continuum without changing that atom.
-/

noncomputable section

open Set Filter MeasureTheory Real
open GapFamily.Analytic
open scoped BigOperators

namespace GapFamily.Construction

/-- The independently placed marker reference and actual finite cells give
the full spectrum, with no infinite-spectrum hypothesis. -/
theorem exists_spectrum_of_fixedCutoff_initial_cells
    {a b δ U c t : ℝ} {k : ℕ} (ht : 0 < t)
    (hshift : shift c = a) (ha : 2 ≤ a) (hb : 1 ≤ b)
    (hδ : 0 ≤ δ) (hδb : δ ≤ b) (hU : 1 ≤ U) (hUa : U ≤ a)
    (hnb : (fixedCutoffReferenceBandThreshold : ℝ) ≤ b) (hba : b ≤ a)
    (hTU : (fixedCutoffReferenceRadius : ℝ) * b ≤ U)
    (htail : (realCanonicalTailThreshold ht : ℝ) ≤ a)
    (hray : t * a ≤ (⌊(fixedCutoffReferenceRadius : ℝ) * b⌋₊ : ℝ))
    (cells : ∀ J : realInitialRows ((fixedCutoffReferenceRadius : ℝ) * b),
      InitialReferenceCell J (max b |(J : ℝ)|) U k
        (fixedCutoffReferenceDensity a b δ ha hb J))
    (hrepair : ∀ (j : ℤ) (e : ℝ), |(j : ℝ)| ≤ e →
      (∑ J, |if 2 * U + 4 < e then
        (cells J).exteriorNumerator (2 * U + 4) (by linarith) j e else 0|) ≤
        exp (7 * sqrt (a * e)) / 8) :
    ∃ spectrum : Spectrum, PureAdmissible c spectrum ∧
      HasUnitScalarGap spectrum (a + δ) := by
  subst a
  let A : ℝ := (fixedCutoffReferenceRadius : ℝ) * b
  let T : ℕ := ⌊A⌋₊
  have hR : (3 : ℝ) < fixedCutoffReferenceRadius := by
    exact_mod_cast (show 3 < fixedCutoffReferenceRadius by
      have := fixedCutoffReferenceRadius_gt_six; omega)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hbT : b < (T : ℝ) := marker_lt_floor_layerStart hR hb
  have hT : 1 ≤ T := one_le_floor_layerStart hR hb
  let d := realTailLocalData ht htail hT hray (by linarith : 0 ≤ U) hUa
  let ref := ReferenceOutput.fixedCutoff (shift c) b δ ha hb hδ hδb
  apply exists_spectrum_of_real_initial_cells d ref
    (fixedCutoffReferenceDensity (shift c) b δ ha hb) cells hδ hδb (hδb.trans_lt hbT)
    (realCanonicalTailThreshold_spec ht htail).1 hT (by linarith) hA hTU
    (Nat.floor_le hA)
  · exact fun j _ ht =>
      fixedCutoffReferenceDensity_thermal_integrable (shift c) b δ ha hb hδ hδb j ht
  · exact fixedCutoffReferenceDensity_ae_eq_zero_below_cutoff (shift c) b δ ha hb
  · intro j t ht
    exact fixedCutoffReferenceThermalMeasure_eq_marker_add_density
      (shift c) b δ ha hb hδ hδb j ht
  · intro j e he
    exact fixedCutoffReferenceDensity_uniform_error (shift c) b δ ha hb hδ hδb e j
      hnb hba ((le_max_left _ _).trans he) ((le_max_right _ _).trans he)
  · exact hrepair

end GapFamily.Construction

namespace GapFamily

open Construction

/-- Theorem 2.2(ii), including zero shifted gap, all sufficiently large
real shifts, complete character admissibility,
the unique unit scalar first primary, and both required limits. -/
theorem fixedGapFamilyExists : FixedGapFamilyExists := by
  apply fixedGapFamilyExists_of_eventually_realizesGap
  intro δ hδ
  obtain ⟨R, s, _, _, _, κ₀, hκ₀, hdata⟩ := exists_fixedCutoff_initial_data
  let κ : ℝ := κ₀ / 2
  have hκ : 0 < κ := by dsimp [κ]; positivity
  have hκlt : κ < κ₀ := by dsimp [κ]; linarith
  obtain ⟨a₀, _, ha₀⟩ := hdata κ hκ hκlt δ hδ
  let t : ℝ := (fixedCutoffReferenceRadius : ℝ) * κ / 2
  have hR : (6 : ℝ) < fixedCutoffReferenceRadius := by
    exact_mod_cast fixedCutoffReferenceRadius_gt_six
  have ht : 0 < t := by dsimp [t]; positivity
  filter_upwards [eventually_ge_atTop a₀,
    eventually_ge_atTop (realCanonicalTailThreshold ht : ℝ)] with a haThreshold htail
  obtain ⟨ha, hb, hU, hδb, hnb, hba, hTU, hUa, cells, hrepair⟩ := ha₀ a haThreshold
  have hradius : 2 ≤ (fixedCutoffReferenceRadius : ℝ) * (κ * a) := by
    have h := mul_le_mul_of_nonneg_left hb
      (by linarith : (0 : ℝ) ≤ fixedCutoffReferenceRadius)
    linarith
  exact exists_spectrum_of_fixedCutoff_initial_cells ht (shift_gapFamilyCharge a)
    ha hb hδ hδb hU hUa hnb hba hTU htail (ray_le_floor_layerStart hradius) cells hrepair

end GapFamily
