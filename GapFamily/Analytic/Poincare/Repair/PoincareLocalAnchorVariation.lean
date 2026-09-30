import GapFamily.Analytic.Poincare.Repair.PoincareLocalInverseInput

/-!
# Ordinary total variation of the local anchor

The actual high scalar band input has exactly the scalar seed variation.
Subtracting its native low-band inverse adds at most the established inverse
variation bound, with the actual inverse operator norm retained explicitly.
-/

noncomputable section

namespace GapFamily.Analytic

open Set MeasureTheory
open scoped Classical BigOperators

/-- Total variation of a difference obeys the ordinary real-valued triangle
inequality, since both signed measures have finite variation. -/
theorem signedMeasure_variation_real_sub_le (μ ν : SignedMeasure ℝ) :
    (μ - ν).variation.real univ ≤ μ.variation.real univ + ν.variation.real univ := by
  let := signedMeasure_isFiniteMeasure_variation μ
  let := signedMeasure_isFiniteMeasure_variation ν
  have h := ENNReal.toReal_mono (measure_ne_top (μ.variation + ν.variation) univ)
    (VectorMeasure.variation_sub_le (μ := μ) (ν := ν) univ)
  simpa only [Measure.real, Measure.add_apply,
    ENNReal.toReal_add (measure_ne_top μ.variation univ)
      (measure_ne_top ν.variation univ)] using h

/-- The finite high input has exactly the variation mass of its scalar row. -/
theorem sum_totalVariation_localAnchorHighInput (S : Finset ℤ) (h0 : 0 ∈ S)
    (B : ℝ) (hB : 0 < B) (ζ : ℝ → ℝ)
    (hζ : ContinuousOn ζ (scalarAnchorBand B)) :
    (∑ j ∈ S, (localAnchorHighInput B hB ζ hζ j).variation.real univ) =
      (scalarAnchorBandMeasure B hB ζ hζ).variation.real univ := by
  have he (j : ℤ) : (localAnchorHighInput B hB ζ hζ j).variation.real univ =
      if j = 0 then (scalarAnchorBandMeasure B hB ζ hζ).variation.real univ else 0 := by
    by_cases hj : j = 0 <;> simp [localAnchorHighInput, hj]
  simp_rw [he]
  simp [h0]

/-- Native subtype indexing preserves the high input's exact ordinary mass. -/
theorem signedSeedMass_localAnchorHighInput (S : Finset ℤ) (h0 : 0 ∈ S)
    (B : ℝ) (hB : 0 < B) (ζ : ℝ → ℝ)
    (hζ : ContinuousOn ζ (scalarAnchorBand B)) :
    signedSeedMass (fun j : S => localAnchorHighInput B hB ζ hζ j) =
      (scalarAnchorBandMeasure B hB ζ hζ).variation.real univ := by
  rw [signedSeedMass]
  simpa only [← Finset.sum_coe_sort S] using
    sum_totalVariation_localAnchorHighInput S h0 B hB ζ hζ

/-- The actual integer-indexed inverse variation is precisely its native
finite subtype sum. -/
theorem sum_totalVariation_localInverseInput_eq_native
    (S : Finset ℤ) (ν : ℤ → SignedMeasure ℝ) (M B : ℝ)
    (hM : 0 ≤ M) (hB : 0 ≤ B)
    (hs : ∀ J ∈ S, ∀ᵐ E ∂(ν J).variation, |(J : ℝ)| ≤ E ∧ E ≤ M)
    (hunit : IsUnit (correctedLowBandIdentityPlus (fun j : S => (j : ℤ)) B)) :
    (∑ j ∈ S, (localInverseInput S ν M B hM hB hs hunit j).variation.real univ) =
      ∑ j : S, (correctedSignedInverseMeasure (fun J : S => ν J)
        Subtype.val Subtype.val M B hM hB (fun J => hs J J.property) hunit j).variation.real univ := by
  rw [← Finset.sum_coe_sort S]
  apply Finset.sum_congr rfl
  intro j hj
  rw [localInverseInput_apply S ν M B hM hB hs hunit j j.property]

/-- The literal high scalar input minus its actual low-band inverse has the
ordinary variation bound of the scalar seed and native inverse together. -/
theorem sum_totalVariation_localAnchorInput_le (S : Finset ℤ) (h0 : 0 ∈ S)
    (B : ℝ) (hB : 1 ≤ B) (hband : ∀ j ∈ S, |(j : ℝ)| < B)
    (ζ : ℝ → ℝ) (hζ : ContinuousOn ζ (scalarAnchorBand B))
    (hunit : IsUnit (correctedLowBandIdentityPlus (fun j : S => (j : ℤ)) B)) :
    (∑ j ∈ S, (localAnchorInput S B (zero_lt_one.trans_le hB) ζ hζ hunit j).variation.real univ) ≤
      (1 + 45 * correctedKernelBound * B ^ 3 +
        500 * correctedKernelBound ^ 2 * B ^ 6 *
          ‖Ring.inverse (correctedLowBandIdentityPlus (fun j : S => (j : ℤ)) B)‖) *
        (scalarAnchorBandMeasure B (zero_lt_one.trans_le hB) ζ hζ).variation.real univ := by
  let hBpos : 0 < B := zero_lt_one.trans_le hB
  let ν := localAnchorHighInput B hBpos ζ hζ
  let hs : ∀ J ∈ S, ∀ᵐ E ∂(ν J).variation, |(J : ℝ)| ≤ E ∧ E ≤ 3 * B :=
    fun J _ => localAnchorHighInput_ae_physical B hBpos ζ hζ J
  let μ := localInverseInput S ν (3 * B) B (by positivity) hBpos.le hs hunit
  have hν : (∑ j ∈ S, (ν j).variation.real univ) =
      (scalarAnchorBandMeasure B hBpos ζ hζ).variation.real univ :=
    sum_totalVariation_localAnchorHighInput S h0 B hBpos ζ hζ
  have hμ : (∑ j ∈ S, (μ j).variation.real univ) ≤
      (45 * correctedKernelBound * B ^ 3 +
        500 * correctedKernelBound ^ 2 * B ^ 6 *
          ‖Ring.inverse (correctedLowBandIdentityPlus (fun j : S => (j : ℤ)) B)‖) *
        (scalarAnchorBandMeasure B hBpos ζ hζ).variation.real univ := by
    change (∑ j ∈ S, (localInverseInput S ν (3 * B) B _ _ hs hunit j).variation.real univ) ≤ _
    rw [sum_totalVariation_localInverseInput_eq_native]
    have h := sum_totalVariation_correctedSignedInverseMeasure_le_physical
      (fun J : S => ν J) Subtype.val Subtype.val Subtype.val_injective B hB
      (fun J => hband J J.property) (fun J => hs J J.property) hunit
    simpa only [ν, signedSeedMass_localAnchorHighInput S h0 B hBpos ζ hζ] using h
  change (∑ j ∈ S, (ν j - μ j).variation.real univ) ≤ _
  calc
    _ ≤ ∑ j ∈ S, ((ν j).variation.real univ + (μ j).variation.real univ) :=
      Finset.sum_le_sum fun j _ => signedMeasure_variation_real_sub_le (ν j) (μ j)
    _ = (∑ j ∈ S, (ν j).variation.real univ) + ∑ j ∈ S, (μ j).variation.real univ :=
      Finset.sum_add_distrib
    _ ≤ (scalarAnchorBandMeasure B hBpos ζ hζ).variation.real univ +
        (45 * correctedKernelBound * B ^ 3 +
          500 * correctedKernelBound ^ 2 * B ^ 6 *
            ‖Ring.inverse (correctedLowBandIdentityPlus (fun j : S => (j : ℤ)) B)‖) *
          (scalarAnchorBandMeasure B hBpos ζ hζ).variation.real univ :=
      add_le_add hν.le hμ
    _ = _ := by ring

end GapFamily.Analytic
