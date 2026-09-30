import GapFamily.Construction.PermanentSpectrumRemainder
import GapFamily.Construction.PermanentSpectrumRemainderAtomList
import GapFamily.Construction.PermanentSpectrumRemainderReconstruction

/-! Actual finite canonical repair histories give the required complete
modular functions. Their ordinary thermal output masses, persistent unit
atoms, and escaping density tail identify the permanent character limit. -/

noncomputable section
namespace GapFamily.Construction.PermanentSpectrumData
open Set Filter MeasureTheory Real
open scoped Topology UpperHalfPlane
open Analytic
variable {b : ℝ} (D : PermanentSpectrumData b)

/-- Ordinary row-mass reconstruction of the actual canonical repair history
identifies its exact residual from the same permanent atom prefix. -/
theorem repairHistory_remainder_eq_tailDensity
    (c T C : ℝ) (ha : 2 ≤ shift c) (hb : 1 ≤ b)
    (history : ℕ → List CanonicalRepairDatum) (q : ℕ → ℤ → ℝ → ℝ)
    (ha100 : 100 ≤ shift c) (hT : 1 ≤ T)
    (hm : ∀ n j, AEStronglyMeasurable (q n j)
      ((referenceMeasure j).restrict (Ici (max T |(j : ℝ)|))))
    (hq : ∀ n j, ∀ᵐ E ∂(referenceMeasure j).restrict (Ici (max T |(j : ℝ)|)),
      |q n j E| ≤ C * tailEnvelopeNumerator (shift c) E j)
    (hmass : ∀ n (j : ℤ) (t : ℝ), 0 < t →
      finiteRepairHistoryThermalMeasure (shift c) b ha hb (history n) j t univ =
        listPointSeedThermalRow (D.permanentAtomList n) j t + tailDensityThermalRow T t (q n) j)
    (n : ℕ) (τ : ℍ) :
    finiteRepairHistorySeed (shift c) b ha hb (history n) τ - D.reducedPrefix c n τ =
      tailDensityPointValue T (q n) τ := by
  have h := finiteRepairHistorySeed_eq_list_add_tail (shift c) b ha hb (history n)
    (D.permanentAtomList n) T C (q n) ha100 hT (hm n) (hq n) (hmass n) τ
  rw [vacuumDirectRow_eq_vacuumNumerator, D.vacuum_add_pointSeed_sum_permanentAtomList] at h
  rw [h, add_sub_cancel_left]

/-- The explicit canonical history functions converge to the actual reduced
character numerator when their ordinary unprocessed densities escape. -/
theorem tendsto_reducedNumerator_of_repairHistoryThermalMass
    (c T C : ℝ) (ha : 2 ≤ shift c) (hb : 1 ≤ b)
    (history : ℕ → List CanonicalRepairDatum) (q : ℕ → ℤ → ℝ → ℝ) (R : ℕ → ℝ)
    (ha100 : 100 ≤ shift c) (hT : 1 ≤ T) (hR : Tendsto R atTop atTop)
    (hthermal : ∀ t : ℝ, 0 < t → Summable (D.layerThermal t))
    (hm : ∀ n j, AEStronglyMeasurable (q n j)
      ((referenceMeasure j).restrict (Ici (max T |(j : ℝ)|))))
    (hq : ∀ n j, ∀ᵐ E ∂(referenceMeasure j).restrict (Ici (max T |(j : ℝ)|)),
      |q n j E| ≤ C * tailEnvelopeNumerator (shift c) E j)
    (hz : ∀ n j, ∀ᵐ E ∂(referenceMeasure j).restrict (Ici (max T |(j : ℝ)|)),
      E < R n → q n j E = 0)
    (hmass : ∀ n (j : ℤ) (t : ℝ), 0 < t →
      finiteRepairHistoryThermalMeasure (shift c) b ha hb (history n) j t univ =
        listPointSeedThermalRow (D.permanentAtomList n) j t + tailDensityThermalRow T t (q n) j) :
    ∀ τ, Tendsto (fun n => finiteRepairHistorySeed (shift c) b ha hb (history n) τ)
      atTop (𝓝 (reducedNumerator c (D.spectrum c) τ)) :=
  D.tendsto_reducedNumerator_of_tailDensity (shift c) T C c
    (fun n => finiteRepairHistorySeed (shift c) b ha hb (history n)) q R ha100 hT hR hthermal
    (D.repairHistory_remainder_eq_tailDensity c T C ha hb history q ha100 hT hm hq hmass) hq hz

/-- No modularity or limit premise is assumed: the functions here are the
literal complete canonical repair histories, whose modularity is already
proved. The remaining inputs are the construction's ordinary output identity,
node thermal sum, and continuum envelope and cutoff bounds. -/
theorem pureAdmissible_and_hasGap_of_repairHistoryThermalMass
    (c T C : ℝ) (ha : 2 ≤ shift c) (hb : 1 ≤ b)
    (history : ℕ → List CanonicalRepairDatum) (q : ℕ → ℤ → ℝ → ℝ) (R : ℕ → ℝ)
    (ha100 : 100 ≤ shift c) (hT : 1 ≤ T) (hR : Tendsto R atTop atTop)
    (hthermal : ∀ t : ℝ, 0 < t → Summable (D.layerThermal t))
    (hm : ∀ n j, AEStronglyMeasurable (q n j)
      ((referenceMeasure j).restrict (Ici (max T |(j : ℝ)|))))
    (hq : ∀ n j, ∀ᵐ E ∂(referenceMeasure j).restrict (Ici (max T |(j : ℝ)|)),
      |q n j E| ≤ C * tailEnvelopeNumerator (shift c) E j)
    (hz : ∀ n j, ∀ᵐ E ∂(referenceMeasure j).restrict (Ici (max T |(j : ℝ)|)),
      E < R n → q n j E = 0)
    (hmass : ∀ n (j : ℤ) (t : ℝ), 0 < t →
      finiteRepairHistoryThermalMeasure (shift c) b ha hb (history n) j t univ =
        listPointSeedThermalRow (D.permanentAtomList n) j t + tailDensityThermalRow T t (q n) j) :
    PureAdmissible c (D.spectrum c) ∧ HasGap (D.spectrum c) (shift c + b) := by
  have hc : 1 < c := by unfold shift at ha100; linarith
  apply D.pureAdmissible_and_hasGap_of_tailDensity (shift c) T C hc
    (fun n => finiteRepairHistorySeed (shift c) b ha hb (history n)) q R ha100 hT hR hthermal
  · intro n τ
    exact finiteRepairHistorySeed_smul (shift c) b ha hb (history n) τ ModularGroup.S
  · intro n τ
    exact finiteRepairHistorySeed_smul (shift c) b ha hb (history n) τ ModularGroup.T
  · exact D.repairHistory_remainder_eq_tailDensity c T C ha hb history q ha100 hT hm hq hmass
  · exact hq
  · exact hz

end GapFamily.Construction.PermanentSpectrumData
