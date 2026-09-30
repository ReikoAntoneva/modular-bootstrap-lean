import GapFamily.Construction.PermanentSpectrumRemainderStateEndpoint
import GapFamily.Construction.PermanentSpectrumFirstPrimary
import GapFamily.Construction.ReferenceOutput

/-! The endpoint argument for an arbitrary actual modular reference.
The marker energy enters only the permanent atom data, so zero is included. -/

noncomputable section
namespace GapFamily.Construction
open Set Filter MeasureTheory Real UpperHalfPlane
open scoped Topology
open Analytic PoincareFourier

namespace FiniteRepairState

/-- Fourier uniqueness identifies the literal reference and finite repair
history with the retained atom list and the ordinary continuum tail. -/
theorem referenceSeed_eq_list_add_tail {a : ℝ} (s : FiniteRepairState)
    (ref : ReferenceOutput a) (δ T C : ℝ)
    (ha100 : 100 ≤ a) (hT : 1 ≤ T)
    (ho : s.HasReferenceOutput ref δ)
    (hi : s.ThermalIntegrable) (hc : s.Cleared)
    (hfront : ∀ j, T ≤ s.front j)
    (hq : ∀ j, ∀ᵐ E ∂(referenceMeasure j).restrict (Ici (max T |(j : ℝ)|)),
      |s.numerator j E| ≤ C * tailEnvelopeNumerator a E j) (τ : ℍ) :
    s.referenceSeed ref τ = vacuumDirectRow a τ.im τ.re +
      (((δ, 0) :: s.nodes).map (fun p => pointSeed p.1 p.2 (1 / 2) τ)).sum +
        tailDensityPointValue T s.numerator τ := by
  have ht : 0 < 2 * Real.pi * τ.im := by positivity
  have htail : HasSum (fun j : ℤ => (Real.sqrt τ.im : ℂ) *
      (tailDensityThermalRow T (2 * Real.pi * τ.im) s.numerator j : ℂ) *
        cuspFourierMode j τ.re) (tailDensityPointValue T s.numerator τ) := by
    have hd := (summable_norm_tailDensityPointValue_term a T C s.numerator
      ha100 hT hq τ).of_norm.hasSum
    simpa only [tailDensityPointValue, mul_assoc] using hd.mul_left (Real.sqrt τ.im : ℂ)
  have hactual := s.hasSum_referenceSeed_output ref τ.im τ.im_pos τ.re
  have hrow : rowPoint τ.im τ.im_pos τ.re = τ := by
    apply UpperHalfPlane.ext
    exact Complex.eta _
  rw [hrow] at hactual
  have hsplit := (hasSum_listPointSeedThermalRow ((δ, 0) :: s.nodes) τ).add htail
  have heq : s.referenceSeed ref τ - vacuumDirectRow a τ.im τ.re =
      (((δ, 0) :: s.nodes).map (fun p => pointSeed p.1 p.2 (1 / 2) τ)).sum +
        tailDensityPointValue T s.numerator τ := by
    apply hactual.unique
    convert hsplit using 1
    funext j
    rw [ho j _ ht, _root_.add_apply,
      s.atomicThermalOutput_univ_eq_listPointSeedThermalRow,
      s.continuumThermalOutput_univ_eq_tailDensityThermalRow hi hc T j (hfront j) ht,
      Complex.ofReal_add, mul_add, add_mul]
  calc
    _ = (s.referenceSeed ref τ - vacuumDirectRow a τ.im τ.re) +
        vacuumDirectRow a τ.im τ.re := by ring
    _ = _ := by rw [heq]; ring

end FiniteRepairState

namespace PermanentSpectrumData
variable {δ : ℝ} (D : PermanentSpectrumData δ)

theorem referenceState_seed_eq_prefix_add_tail (c T C : ℝ)
    (ref : ReferenceOutput (shift c)) (s : FiniteRepairState) (n : ℕ)
    (ha100 : 100 ≤ shift c) (hT : 1 ≤ T)
    (ho : s.HasReferenceOutput ref δ)
    (hi : s.ThermalIntegrable) (hc : s.Cleared)
    (hnodes : D.permanentAtomList n = (δ, 0) :: s.nodes)
    (hfront : ∀ j, T ≤ s.front j)
    (hq : ∀ j, ∀ᵐ E ∂(referenceMeasure j).restrict (Ici (max T |(j : ℝ)|)),
      |s.numerator j E| ≤ C * tailEnvelopeNumerator (shift c) E j) (τ : ℍ) :
    s.referenceSeed ref τ = D.reducedPrefix c n τ + tailDensityPointValue T s.numerator τ := by
  have h := s.referenceSeed_eq_list_add_tail ref δ T C ha100 hT ho hi hc hfront hq τ
  rw [← hnodes, vacuumDirectRow_eq_vacuumNumerator,
    D.vacuum_add_pointSeed_sum_permanentAtomList] at h
  exact h

theorem referenceState_remainder_norm_le (c T C R : ℝ)
    (ref : ReferenceOutput (shift c)) (s : FiniteRepairState) (n : ℕ)
    (ha100 : 100 ≤ shift c) (hT : 1 ≤ T)
    (ho : s.HasReferenceOutput ref δ)
    (hi : s.ThermalIntegrable) (hc : s.Cleared)
    (hnodes : D.permanentAtomList n = (δ, 0) :: s.nodes)
    (hfront : ∀ j, T ≤ s.front j) (hcutoff : ∀ j, R ≤ s.front j)
    (hq : ∀ j, ∀ᵐ E ∂(referenceMeasure j).restrict (Ici (max T |(j : ℝ)|)),
      |s.numerator j E| ≤ C * tailEnvelopeNumerator (shift c) E j) (τ : ℍ) :
    ‖s.referenceSeed ref τ - D.reducedPrefix c n τ‖ ≤
      sqrt τ.im * C * tailEnvelopeThermalTail (shift c) T (2 * π * τ.im) R := by
  rw [D.referenceState_seed_eq_prefix_add_tail c T C ref s n ha100 hT ho hi hc
    hnodes hfront hq τ, add_sub_cancel_left]
  exact norm_tailDensityPointValue_le_cutoff (shift c) T C R s.numerator ha100 hT hq
    (fun j => s.numerator_zero_below_cutoff_ae hc T R j (hcutoff j)) τ

theorem tendsto_reducedNumerator_of_referenceState (c T C : ℝ)
    (ref : ReferenceOutput (shift c))
    (s : ℕ → FiniteRepairState) (N : ℕ → ℕ) (R : ℕ → ℝ)
    (ha100 : 100 ≤ shift c) (hT : 1 ≤ T)
    (hN : Tendsto N atTop atTop) (hR : Tendsto R atTop atTop)
    (hthermal : ∀ t : ℝ, 0 < t → Summable (D.layerThermal t))
    (ho : ∀ n, (s n).HasReferenceOutput ref δ)
    (hi : ∀ n, (s n).ThermalIntegrable) (hc : ∀ n, (s n).Cleared)
    (hnodes : ∀ n, D.permanentAtomList (N n) = (δ, 0) :: (s n).nodes)
    (hfront : ∀ n j, T ≤ (s n).front j)
    (hcutoff : ∀ n j, R n ≤ (s n).front j)
    (hq : ∀ n j, ∀ᵐ E ∂(referenceMeasure j).restrict (Ici (max T |(j : ℝ)|)),
      |(s n).numerator j E| ≤ C * tailEnvelopeNumerator (shift c) E j) :
    ∀ τ, Tendsto (fun n => (s n).referenceSeed ref τ) atTop
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
  exact D.referenceState_seed_eq_prefix_add_tail c T C ref (s n) (N n) ha100 hT
    (ho n) (hi n) (hc n) (hnodes n) (hfront n) (hq n) τ

/-- Actual output, thermal bounds, and escaping cleared fronts give the
admissible permanent spectrum for every nonnegative marker represented by `D`. -/
theorem pureAdmissible_and_hasGap_of_referenceState (c T C : ℝ)
    (ref : ReferenceOutput (shift c))
    (s : ℕ → FiniteRepairState) (N : ℕ → ℕ) (R : ℕ → ℝ)
    (ha100 : 100 ≤ shift c) (hT : 1 ≤ T)
    (hN : Tendsto N atTop atTop) (hR : Tendsto R atTop atTop)
    (hthermal : ∀ t : ℝ, 0 < t → Summable (D.layerThermal t))
    (ho : ∀ n, (s n).HasReferenceOutput ref δ)
    (hi : ∀ n, (s n).ThermalIntegrable) (hc : ∀ n, (s n).Cleared)
    (hnodes : ∀ n, D.permanentAtomList (N n) = (δ, 0) :: (s n).nodes)
    (hfront : ∀ n j, T ≤ (s n).front j)
    (hcutoff : ∀ n j, R n ≤ (s n).front j)
    (hq : ∀ n j, ∀ᵐ E ∂(referenceMeasure j).restrict (Ici (max T |(j : ℝ)|)),
      |(s n).numerator j E| ≤ C * tailEnvelopeNumerator (shift c) E j) :
    PureAdmissible c (D.spectrum c) ∧ HasGap (D.spectrum c) (shift c + δ) := by
  refine ⟨?_, D.hasGap c⟩
  have hc' : 1 < c := by unfold shift at ha100; linarith
  apply nodeSpectrum_pureAdmissible_of_pointwise_limit hc' D.energy D.spin D.energy_cone
    D.energy_sublevel_finite
    (fun y hy => D.energyThermal_summable y (hthermal (2 * π * y) (by positivity)))
    (fun n => (s n).referenceSeed ref)
  · intro n τ
    exact (s n).referenceSeed_smul ref τ ModularGroup.S
  · intro n τ
    exact (s n).referenceSeed_smul ref τ ModularGroup.T
  · exact D.tendsto_reducedNumerator_of_referenceState c T C ref s N R ha100 hT hN hR
      hthermal ho hi hc hnodes hfront hcutoff hq

/-- Strict separation of nonmarker occurrences passes through the genuine
finite-fibre multiplicities to the unit scalar first-primary conclusion. -/
theorem pureAdmissible_and_hasUnitScalarGap_of_referenceState (c T C : ℝ)
    (ref : ReferenceOutput (shift c))
    (s : ℕ → FiniteRepairState) (N : ℕ → ℕ) (R : ℕ → ℝ)
    (ha100 : 100 ≤ shift c) (hT : 1 ≤ T)
    (hN : Tendsto N atTop atTop) (hR : Tendsto R atTop atTop)
    (hthermal : ∀ t : ℝ, 0 < t → Summable (D.layerThermal t))
    (ho : ∀ n, (s n).HasReferenceOutput ref δ)
    (hi : ∀ n, (s n).ThermalIntegrable) (hc : ∀ n, (s n).Cleared)
    (hnodes : ∀ n, D.permanentAtomList (N n) = (δ, 0) :: (s n).nodes)
    (hfront : ∀ n j, T ≤ (s n).front j)
    (hcutoff : ∀ n j, R n ≤ (s n).front j)
    (hq : ∀ n j, ∀ᵐ E ∂(referenceMeasure j).restrict (Ici (max T |(j : ℝ)|)),
      |(s n).numerator j E| ≤ C * tailEnvelopeNumerator (shift c) E j)
    (hinitial : ∀ i, δ < D.initialEnergy i)
    (hlayer : ∀ m i, δ < D.layerEnergy m i) :
    PureAdmissible c (D.spectrum c) ∧ HasUnitScalarGap (D.spectrum c) (shift c + δ) :=
  ⟨(D.pureAdmissible_and_hasGap_of_referenceState c T C ref s N R ha100 hT hN hR
    hthermal ho hi hc hnodes hfront hcutoff hq).1,
    D.hasUnitScalarGap c hinitial hlayer⟩

end PermanentSpectrumData
end GapFamily.Construction
