import BTZEntropy.Comparison.ReferenceLowBandRate
import BTZEntropy.Comparison.DiscreteReference
import BTZEntropy.Comparison.UniformEstimate

/-! The actual permanent spectrum compared directly with the full integer
reference cone. The fixed low-energy cutoff is removed with its proved
all-descendant estimate. -/

noncomputable section

open Set GapFamily BTZEntropy.Construction

namespace BTZEntropy

universe u

theorem UniformRemainder.sub {ι : Type u} {B : ℝ} {selectors : Set ι} {P : ℕ}
    {f g : ι → ℝ → ℝ → ℝ → ℝ}
    (hf : UniformRemainder B selectors P f) (hg : UniformRemainder B selectors P g) :
    UniformRemainder B selectors P (fun σ a δ x => f σ a δ x - g σ a δ x) := by
  have hneg : UniformRemainder B selectors P (fun σ a δ x => -g σ a δ x) := by
    intro L U hL hLU
    obtain ⟨C, hC, K₀, hK₀, hg⟩ := hg L U hL hLU
    refine ⟨C, hC, K₀, hK₀, ?_⟩
    intro σ hσ a hK δ hδ x hx
    simpa only [abs_neg] using hg σ hσ a hK δ hδ x hx
  simpa only [sub_eq_add_neg] using hf.add hneg

namespace Comparison

/-- The same selected permanent spectrum agrees to every inverse charge
order with the complete integer-spin reference handled by actual Poisson
summation. There is no remaining reference-cutoff premise. -/
theorem fixedFamily_fullIntegerReference_uniformRemainder
    (B : ℝ) (φ : SmoothKernel) (P : ℕ) :
    UniformRemainder B (fixedFamilySelectors B) P
      (fun σ a δ x =>
        (smoothCount φ (gapFamilyCharge a) (fixedFamilySpectrum B σ a δ)
            (x * gapFamilyCharge a) -
          integerLeadingSmoothCount φ (shift (gapFamilyCharge a))
            0 (x * gapFamilyCharge a)) /
          saddleCountScale φ x (gapFamilyCharge a)) := by
  have hd := fixedFamily_discreteReference_uniformRemainder B φ P
  have hl := integerLeadingSmoothCount_cutoff_uniformRemainder B (fixedFamilySelectors B)
    φ (fixedFamilyGeometry B).start (Nat.cast_nonneg _) P
  have h := hd.sub hl
  convert h using 1
  funext σ a δ x
  ring

end Comparison
end BTZEntropy
