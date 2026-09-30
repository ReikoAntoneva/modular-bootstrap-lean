import GapFamily.Construction.PermanentSpectrumRemainderHistory
import GapFamily.Construction.PermanentSpectrumRemainderState
import GapFamily.Construction.PermanentSpectrumRemainderReconstructionState
import GapFamily.Construction.FiniteRepairStateOutput

/-! The concrete finite repair state supplies the spectral remainder directly
from its actual ordinary measure invariant. A cofinal prefix index permits the
scheduled stage `n` to correspond to the absolute energy layer `T + n`. -/

noncomputable section
namespace GapFamily.Construction.PermanentSpectrumData
open Set Filter MeasureTheory Real
open scoped Topology UpperHalfPlane
open Analytic
variable {b : ℝ} (D : PermanentSpectrumData b)

/-- The concrete state invariant identifies the complete modular seed with
the exact permanent atom prefix and the actual remaining continuum. -/
theorem repairState_seed_eq_prefix_add_tail
    (c T C : ℝ) (ha : 2 ≤ shift c) (hb : 1 ≤ b)
    (s : FiniteRepairState) (n : ℕ)
    (ha100 : 100 ≤ shift c) (hT : 1 ≤ T)
    (ho : s.HasThermalOutput (shift c) b ha hb)
    (hi : s.ThermalIntegrable) (hc : s.Cleared)
    (hnodes : D.permanentAtomList n = (b, 0) :: s.nodes)
    (hfront : ∀ j, T ≤ s.front j)
    (hq : ∀ j, ∀ᵐ E ∂(referenceMeasure j).restrict (Ici (max T |(j : ℝ)|)),
      |s.numerator j E| ≤ C * tailEnvelopeNumerator (shift c) E j) (τ : ℍ) :
    s.seed (shift c) b ha hb τ = D.reducedPrefix c n τ + tailDensityPointValue T s.numerator τ := by
  have hmass : ∀ (j : ℤ) (t : ℝ), 0 < t →
      finiteRepairHistoryThermalMeasure (shift c) b ha hb s.history j t univ =
        listPointSeedThermalRow (D.permanentAtomList n) j t +
          tailDensityThermalRow T t s.numerator j := by
    intro j t ht
    have h := congrArg (fun μ : SignedMeasure ℝ => μ univ) (ho j t ht)
    change finiteRepairHistoryThermalMeasure (shift c) b ha hb s.history j t univ = _ at h
    rw [_root_.add_apply, s.atomicThermalOutput_univ_eq_listPointSeedThermalRow,
      s.continuumThermalOutput_univ_eq_tailDensityThermalRow hi hc T j (hfront j) ht,
      ← hnodes] at h
    exact h
  have h := finiteRepairHistorySeed_eq_list_add_tail (shift c) b ha hb s.history
    (D.permanentAtomList n) T C s.numerator ha100 hT
    (fun j => (s.aestronglyMeasurable_numerator hi j).restrict) hq hmass τ
  rw [vacuumDirectRow_eq_vacuumNumerator, D.vacuum_add_pointSeed_sum_permanentAtomList] at h
  exact h

/-- The actual complete modular output minus its permanent atom prefix has
the explicit ordinary all-spin thermal tail bound. -/
theorem repairState_remainder_norm_le
    (c T C R : ℝ) (ha : 2 ≤ shift c) (hb : 1 ≤ b)
    (s : FiniteRepairState) (n : ℕ)
    (ha100 : 100 ≤ shift c) (hT : 1 ≤ T)
    (ho : s.HasThermalOutput (shift c) b ha hb)
    (hi : s.ThermalIntegrable) (hc : s.Cleared)
    (hnodes : D.permanentAtomList n = (b, 0) :: s.nodes)
    (hfront : ∀ j, T ≤ s.front j) (hcutoff : ∀ j, R ≤ s.front j)
    (hq : ∀ j, ∀ᵐ E ∂(referenceMeasure j).restrict (Ici (max T |(j : ℝ)|)),
      |s.numerator j E| ≤ C * tailEnvelopeNumerator (shift c) E j) (τ : ℍ) :
    ‖s.seed (shift c) b ha hb τ - D.reducedPrefix c n τ‖ ≤
      sqrt τ.im * C * tailEnvelopeThermalTail (shift c) T (2 * π * τ.im) R := by
  rw [D.repairState_seed_eq_prefix_add_tail c T C ha hb s n ha100 hT ho hi hc
    hnodes hfront hq τ, add_sub_cancel_left]
  exact norm_tailDensityPointValue_le_cutoff (shift c) T C R s.numerator ha100 hT hq
    (fun j => s.numerator_zero_below_cutoff_ae hc T R j (hcutoff j)) τ

/-- Escaping fronts force the actual complete canonical history functions to
converge to the public character numerator of these permanent unit atoms. -/
theorem tendsto_reducedNumerator_of_repairState
    (c T C : ℝ) (ha : 2 ≤ shift c) (hb : 1 ≤ b)
    (s : ℕ → FiniteRepairState) (N : ℕ → ℕ) (R : ℕ → ℝ)
    (ha100 : 100 ≤ shift c) (hT : 1 ≤ T)
    (hN : Tendsto N atTop atTop) (hR : Tendsto R atTop atTop)
    (hthermal : ∀ t : ℝ, 0 < t → Summable (D.layerThermal t))
    (ho : ∀ n, (s n).HasThermalOutput (shift c) b ha hb)
    (hi : ∀ n, (s n).ThermalIntegrable) (hc : ∀ n, (s n).Cleared)
    (hnodes : ∀ n, D.permanentAtomList (N n) = (b, 0) :: (s n).nodes)
    (hfront : ∀ n j, T ≤ (s n).front j)
    (hcutoff : ∀ n j, R n ≤ (s n).front j)
    (hq : ∀ n j, ∀ᵐ E ∂(referenceMeasure j).restrict (Ici (max T |(j : ℝ)|)),
      |(s n).numerator j E| ≤ C * tailEnvelopeNumerator (shift c) E j) :
    ∀ τ, Tendsto (fun n => (s n).seed (shift c) b ha hb τ) atTop
      (𝓝 (reducedNumerator c (D.spectrum c) τ)) := by
  intro τ
  have hprefix := (D.tendsto_reducedPrefix c τ
    (hthermal (2 * π * τ.im) (by positivity))).comp hN
  have htail := tendsto_tailDensityPointValue_of_cutoff (shift c) T C
    (fun n => (s n).numerator) R ha100 hT hR hq
    (fun n j => (s n).numerator_zero_below_cutoff_ae (hc n) T (R n) j (hcutoff n j)) τ
  have h := hprefix.add htail
  simp only [add_zero] at h
  convert h using 1
  funext n
  exact D.repairState_seed_eq_prefix_add_tail c T C ha hb (s n) (N n) ha100 hT
    (ho n) (hi n) (hc n) (hnodes n) (hfront n) (hq n) τ

/-- The actual finite-state measure invariant and proved local estimates give
public admissibility and the exact marker gap. No modularity, inverse, or
convergence assertion is postulated here. -/
theorem pureAdmissible_and_hasGap_of_repairState
    (c T C : ℝ) (ha : 2 ≤ shift c) (hb : 1 ≤ b)
    (s : ℕ → FiniteRepairState) (N : ℕ → ℕ) (R : ℕ → ℝ)
    (ha100 : 100 ≤ shift c) (hT : 1 ≤ T)
    (hN : Tendsto N atTop atTop) (hR : Tendsto R atTop atTop)
    (hthermal : ∀ t : ℝ, 0 < t → Summable (D.layerThermal t))
    (ho : ∀ n, (s n).HasThermalOutput (shift c) b ha hb)
    (hi : ∀ n, (s n).ThermalIntegrable) (hc : ∀ n, (s n).Cleared)
    (hnodes : ∀ n, D.permanentAtomList (N n) = (b, 0) :: (s n).nodes)
    (hfront : ∀ n j, T ≤ (s n).front j)
    (hcutoff : ∀ n j, R n ≤ (s n).front j)
    (hq : ∀ n j, ∀ᵐ E ∂(referenceMeasure j).restrict (Ici (max T |(j : ℝ)|)),
      |(s n).numerator j E| ≤ C * tailEnvelopeNumerator (shift c) E j) :
    PureAdmissible c (D.spectrum c) ∧ HasGap (D.spectrum c) (shift c + b) := by
  refine ⟨?_, D.hasGap c⟩
  have hc' : 1 < c := by unfold shift at ha100; linarith
  apply nodeSpectrum_pureAdmissible_of_pointwise_limit hc' D.energy D.spin D.energy_cone
    D.energy_sublevel_finite
    (fun y hy => D.energyThermal_summable y (hthermal (2 * π * y) (by positivity)))
    (fun n => (s n).seed (shift c) b ha hb)
  · intro n τ
    exact (s n).seed_smul (shift c) b ha hb τ ModularGroup.S
  · intro n τ
    exact (s n).seed_smul (shift c) b ha hb τ ModularGroup.T
  · exact D.tendsto_reducedNumerator_of_repairState c T C ha hb s N R ha100 hT hN hR
      hthermal ho hi hc hnodes hfront hcutoff hq

end GapFamily.Construction.PermanentSpectrumData
