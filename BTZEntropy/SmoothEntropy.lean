import BTZEntropy.Comparison.ReferenceLowBandActual
import BTZEntropy.Comparison.SpinComparison
import BTZEntropy.Analytic.SaddleExpansionUniform
import BTZEntropy.Analytic.SaddleRelative
import GapFamily.GapFamilyLimit

/-!
# Proposition 2.3: smooth BTZ entropy

The actual fixed-cutoff spectra, with every admitted node selector, have the
prescribed all-order entropy expansion. The proof compares their full state
counts with the actual integer reference, removes the noncentral spin images,
and applies the proved BTZ saddle and logarithmic estimates.
-/

noncomputable section

open Set Filter GapFamily
open BTZEntropy.Construction BTZEntropy.Comparison

namespace BTZEntropy

universe u

/-- The actual integer-spin comparison for every sufficiently large real charge. -/
theorem integerReference_btz_uniformRemainder {ι : Type u}
    (B : ℝ) (selectors : Set ι) (φ : SmoothKernel) (P : ℕ) :
    UniformRemainder B selectors P (fun _ a _ x =>
      (integerLeadingSmoothCount φ (shift (gapFamilyCharge a)) 0
          (x * gapFamilyCharge a) - btzCount φ x (gapFamilyCharge a)) /
        saddleCountScale φ x (gapFamilyCharge a)) := by
  intro L U hL hLU
  obtain ⟨A, hA, herror⟩ := integerLeadingSmoothCount_sub_btz_saddleScale φ hL hLU P
  refine ⟨1, zero_lt_one, A, (by linarith), ?_⟩
  intro σ hσ a ha δ hδ x hx
  have has : A ≤ shift (gapFamilyCharge a) := by
    simpa only [shift_gapFamilyCharge] using ha
  have he := herror (shift (gapFamilyCharge a)) has x hx
  have hc : 12 * shift (gapFamilyCharge a) + 1 = gapFamilyCharge a := by
    unfold shift
    ring
  simpa only [hc] using he

/-- Full-state count matching for the very same constructed spectra. -/
theorem fixedFamily_btz_uniformRelativeMatching (B : ℝ) (φ : SmoothKernel) :
    UniformRelativeMatching B (fixedFamilySelectors B) (fixedFamilySpectrum B) φ
      (fun a x => btzCount φ x (gapFamilyCharge a)) := by
  apply uniformRelativeMatching_of_saddleScale_error φ (btzCount φ)
    (uniformSaddleCountExpansion_btzCount φ)
  intro P hP
  have h := (fixedFamily_fullIntegerReference_uniformRemainder B φ P).add
    (integerReference_btz_uniformRemainder B (fixedFamilySelectors B) φ P)
  convert h using 1
  funext σ a δ x
  ring

/-- Proposition 2.3 for the explicit, inhabited class of all admitted
fixed-cutoff construction selectors. No construction or analytic premise
remains beyond the stated positive cutoff. -/
theorem smoothBTZFamily_fixedCutoff (B : ℝ) (hB : 0 < B) :
    SmoothBTZFamily B (fixedFamilySelectors B) (fixedFamilySpectrum B) := by
  refine ⟨actual_uniformFixedCutoffFamily B hB, ?_⟩
  intro φ
  exact uniformSmoothEntropyExpansion_of_saddleCountExpansion φ (btzCount φ)
    (uniformSaddleCountExpansion_btzCount φ) (fixedFamily_btz_uniformRelativeMatching B φ).2

/-- The existential formulation, with a genuinely nonempty selector class. -/
theorem smoothBTZFamily_exists (B : ℝ) (hB : 0 < B) :
    ∃ (ι : Type) (selectors : Set ι) (family : ι → ℝ → ℝ → Spectrum),
      SmoothBTZFamily B selectors family :=
  ⟨ActualFixedFamilySelector B, fixedFamilySelectors B, fixedFamilySpectrum B,
    smoothBTZFamily_fixedCutoff B hB⟩

/-- Proposition 2.3: every fixed nonnegative gap has a real-charge spectral
family with both limits of Theorem 2.2(ii) and the complete smooth BTZ entropy
expansion, all for the same family. -/
theorem smoothBTZEntropy_fixedGap : FixedGapSmoothEntropyFamilyExists := by
  intro δ hδ
  have hB : 0 < δ + 1 := by linarith
  have hδB : δ ∈ Ico (0 : ℝ) (δ + 1) := ⟨hδ, by linarith⟩
  obtain ⟨hfamily, hentropy⟩ := smoothBTZFamily_fixedCutoff (δ + 1) hB
  obtain ⟨σ, hσ⟩ := hfamily.2.1
  obtain ⟨a₀, ha₀, hgap⟩ := hfamily.2.2
  refine ⟨a₀, ha₀, fun a => fixedFamilySpectrum (δ + 1) σ a δ, ?_, ?_, ?_, ?_⟩
  · intro a ha
    exact (hgap σ hσ a ha δ hδB).1
  · apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop a₀] with a ha
    exact (hgap σ hσ a ha δ hδB).1.firstShiftedEnergy_eq.symm
  · apply (tendsto_fixedGap_ratio_zero δ).congr'
    filter_upwards [eventually_ge_atTop a₀] with a ha
    rw [(hgap σ hσ a ha δ hδB).1.firstShiftedEnergy_eq]
  · intro φ P L U hL hLU
    obtain ⟨Ap, hAp, hpos⟩ := (hentropy φ).1 L U hL hLU
    obtain ⟨C, hC, Ae, hAe, herr⟩ := (hentropy φ).2 P L U hL hLU
    refine ⟨C, hC, max a₀ (max Ap Ae), le_max_left _ _, ?_⟩
    intro a ha x hx
    have hap : Ap ≤ a := (le_max_left Ap Ae).trans ((le_max_right _ _).trans ha)
    have hae : Ae ≤ a := (le_max_right Ap Ae).trans ((le_max_right _ _).trans ha)
    exact ⟨hpos σ hσ a hap δ hδB x hx, herr σ hσ a hae δ hδB x hx⟩

end BTZEntropy
