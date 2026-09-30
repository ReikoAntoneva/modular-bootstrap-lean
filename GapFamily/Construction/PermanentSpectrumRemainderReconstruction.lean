import GapFamily.Analytic.Foundation.FullVacuumDirect
import GapFamily.Analytic.Poincare.Poincare
import GapFamily.Construction.FiniteRepairHistory
import GapFamily.Construction.PermanentSpectrumRemainderDensity

noncomputable section
namespace GapFamily.Construction

open Set MeasureTheory UpperHalfPlane Analytic Analytic.PoincareFourier

/-- The literal thermal mass of unit atoms in one integer-spin row.
List repetitions retain their unit multiplicities. -/
def listPointSeedThermalRow (atoms : List (ℝ × ℤ)) (j : ℤ) (t : ℝ) : ℝ :=
  (atoms.map (fun p => if j = p.2 then Real.exp (-t * p.1) else 0)).sum

theorem sqrt_mul_thermal_cuspFourierMode_eq_pointSeed
    (E : ℝ) (J : ℤ) (τ : UpperHalfPlane) :
    (Real.sqrt τ.im : ℂ) * (Real.exp (-(2 * Real.pi * τ.im) * E) : ℂ) *
        cuspFourierMode J τ.re = pointSeed E J (1 / 2) τ := by
  unfold cuspFourierMode pointSeed
  rw [← Real.sqrt_eq_rpow, Complex.ofReal_exp, mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- Every finite unit-atom list has its exact ordinary Fourier reconstruction. -/
theorem hasSum_listPointSeedThermalRow (atoms : List (ℝ × ℤ)) (τ : UpperHalfPlane) :
    HasSum (fun j : ℤ => (Real.sqrt τ.im : ℂ) *
      (listPointSeedThermalRow atoms j (2 * Real.pi * τ.im) : ℂ) *
        cuspFourierMode j τ.re)
      ((atoms.map (fun p => pointSeed p.1 p.2 (1 / 2) τ)).sum) := by
  induction atoms with
  | nil => simp [listPointSeedThermalRow]
  | cons p atoms ih =>
    have hs : HasSum (fun j : ℤ => (Real.sqrt τ.im : ℂ) *
        ((if j = p.2 then Real.exp (-(2 * Real.pi * τ.im) * p.1) else 0) : ℝ) *
          cuspFourierMode j τ.re) (pointSeed p.1 p.2 (1 / 2) τ) := by
      convert hasSum_ite_eq p.2 (pointSeed p.1 p.2 (1 / 2) τ) using 1
      funext j
      by_cases hj : j = p.2
      · subst j
        simp only [ite_true]
        exact sqrt_mul_thermal_cuspFourierMode_eq_pointSeed p.1 p.2 τ
      · simp [hj]
    simpa only [listPointSeedThermalRow, List.map_cons, List.sum_cons,
      Complex.ofReal_add, mul_add, add_mul] using hs.add ih

/-- Exact finite-stage row masses identify the same actual modular seed
with its literal unit atoms and its ordinary physical tail density.
The density integrals and the all-spin Fourier sum have proved convergence. -/
theorem finiteRepairHistorySeed_list_tail_integrable_and_eq
    (a b : ℝ) (ha : 2 ≤ a) (hb : 1 ≤ b) (history : List CanonicalRepairDatum)
    (atoms : List (ℝ × ℤ)) (T C : ℝ) (q : ℤ → ℝ → ℝ)
    (ha100 : 100 ≤ a) (hT : 1 ≤ T)
    (hmeas : ∀ j, AEStronglyMeasurable (q j)
      ((referenceMeasure j).restrict (Ici (max T |(j : ℝ)|))))
    (hbound : ∀ j, ∀ᵐ E ∂(referenceMeasure j).restrict (Ici (max T |(j : ℝ)|)),
      |q j E| ≤ C * tailEnvelopeNumerator a E j)
    (hmass : ∀ (j : ℤ) (t : ℝ), 0 < t →
      finiteRepairHistoryThermalMeasure a b ha hb history j t univ =
        listPointSeedThermalRow atoms j t + tailDensityThermalRow T t q j)
    (τ : UpperHalfPlane) :
    (∀ j, IntegrableOn (fun E => Real.exp (-(2 * Real.pi * τ.im) * E) * q j E)
      (Ici (max T |(j : ℝ)|)) (referenceMeasure j)) ∧
    finiteRepairHistorySeed a b ha hb history τ = vacuumDirectRow a τ.im τ.re +
      (atoms.map (fun p => pointSeed p.1 p.2 (1 / 2) τ)).sum +
        tailDensityPointValue T q τ := by
  have ht : 0 < 2 * Real.pi * τ.im := by positivity
  refine ⟨fun j => integrable_tailDensityThermalRow a T C q j ha100 hT ht
    (hmeas j) (hbound j), ?_⟩
  have htail : HasSum (fun j : ℤ => (Real.sqrt τ.im : ℂ) *
      (tailDensityThermalRow T (2 * Real.pi * τ.im) q j : ℂ) * cuspFourierMode j τ.re)
      (tailDensityPointValue T q τ) := by
    have hd := (summable_norm_tailDensityPointValue_term a T C q ha100 hT hbound τ).of_norm.hasSum
    simpa only [tailDensityPointValue, mul_assoc] using hd.mul_left (Real.sqrt τ.im : ℂ)
  have hactual := hasSum_finiteRepairHistorySeed_output a b ha hb history
    τ.im τ.im_pos τ.re
  have hrow : rowPoint τ.im τ.im_pos τ.re = τ := by
    apply UpperHalfPlane.ext
    exact Complex.eta _
  rw [hrow] at hactual
  have hsplit := (hasSum_listPointSeedThermalRow atoms τ).add htail
  have heq : finiteRepairHistorySeed a b ha hb history τ - vacuumDirectRow a τ.im τ.re =
      (atoms.map (fun p => pointSeed p.1 p.2 (1 / 2) τ)).sum +
        tailDensityPointValue T q τ := by
    apply hactual.unique
    convert hsplit using 1
    funext j
    rw [hmass j _ ht, Complex.ofReal_add, mul_add, add_mul]
  calc
    _ = (finiteRepairHistorySeed a b ha hb history τ - vacuumDirectRow a τ.im τ.re) +
        vacuumDirectRow a τ.im τ.re := by ring
    _ = ((atoms.map (fun p => pointSeed p.1 p.2 (1 / 2) τ)).sum +
        tailDensityPointValue T q τ) + vacuumDirectRow a τ.im τ.re := by rw [heq]
    _ = _ := by ring

/-- Equality projection of the verified finite-stage reconstruction. -/
theorem finiteRepairHistorySeed_eq_list_add_tail
    (a b : ℝ) (ha : 2 ≤ a) (hb : 1 ≤ b) (history : List CanonicalRepairDatum)
    (atoms : List (ℝ × ℤ)) (T C : ℝ) (q : ℤ → ℝ → ℝ)
    (ha100 : 100 ≤ a) (hT : 1 ≤ T)
    (hmeas : ∀ j, AEStronglyMeasurable (q j)
      ((referenceMeasure j).restrict (Ici (max T |(j : ℝ)|))))
    (hbound : ∀ j, ∀ᵐ E ∂(referenceMeasure j).restrict (Ici (max T |(j : ℝ)|)),
      |q j E| ≤ C * tailEnvelopeNumerator a E j)
    (hmass : ∀ (j : ℤ) (t : ℝ), 0 < t →
      finiteRepairHistoryThermalMeasure a b ha hb history j t univ =
        listPointSeedThermalRow atoms j t + tailDensityThermalRow T t q j)
    (τ : UpperHalfPlane) :
    finiteRepairHistorySeed a b ha hb history τ = vacuumDirectRow a τ.im τ.re +
      (atoms.map (fun p => pointSeed p.1 p.2 (1 / 2) τ)).sum +
        tailDensityPointValue T q τ :=
  (finiteRepairHistorySeed_list_tail_integrable_and_eq a b ha hb history atoms T C q
    ha100 hT hmeas hbound hmass τ).2

/-- The C9 list may exclude the fixed scalar marker. Prepending it gives
the exact character vacuum, that marker, every unit atom, and the density tail. -/
theorem finiteRepairHistorySeed_eq_character_marker_list_add_tail
    (c b : ℝ) (ha : 2 ≤ shift c) (hb : 1 ≤ b) (history : List CanonicalRepairDatum)
    (atoms : List (ℝ × ℤ)) (T C : ℝ) (q : ℤ → ℝ → ℝ)
    (ha100 : 100 ≤ shift c) (hT : 1 ≤ T)
    (hmeas : ∀ j, AEStronglyMeasurable (q j)
      ((referenceMeasure j).restrict (Ici (max T |(j : ℝ)|))))
    (hbound : ∀ j, ∀ᵐ E ∂(referenceMeasure j).restrict (Ici (max T |(j : ℝ)|)),
      |q j E| ≤ C * tailEnvelopeNumerator (shift c) E j)
    (hmass : ∀ (j : ℤ) (t : ℝ), 0 < t →
      finiteRepairHistoryThermalMeasure (shift c) b ha hb history j t univ =
        (if j = 0 then Real.exp (-t * b) else 0) + listPointSeedThermalRow atoms j t +
          tailDensityThermalRow T t q j)
    (τ : UpperHalfPlane) :
    finiteRepairHistorySeed (shift c) b ha hb history τ =
      (Real.sqrt τ.im : ℂ) * vacuumNumerator c τ + pointSeed b 0 (1 / 2) τ +
        (atoms.map (fun p => pointSeed p.1 p.2 (1 / 2) τ)).sum +
          tailDensityPointValue T q τ := by
  have hmass' : ∀ (j : ℤ) (t : ℝ), 0 < t →
      finiteRepairHistoryThermalMeasure (shift c) b ha hb history j t univ =
        listPointSeedThermalRow ((b, 0) :: atoms) j t + tailDensityThermalRow T t q j := by
    intro j t ht
    simpa only [listPointSeedThermalRow, List.map_cons, List.sum_cons] using hmass j t ht
  simpa only [vacuumDirectRow_eq_vacuumNumerator, List.map_cons, List.sum_cons, add_assoc] using
    finiteRepairHistorySeed_eq_list_add_tail (shift c) b ha hb history ((b, 0) :: atoms)
      T C q ha100 hT hmeas hbound hmass' τ

end GapFamily.Construction
