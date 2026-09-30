import GapFamily.Construction.PermanentSpectrum
import GapFamily.Construction.PermanentSpectrumRemainderDensity
import GapFamily.Construction.PermanentSpectrumRemainderCorrection

/-! The ordinary unprocessed density discharges the permanent-spectrum
remainder condition. Only its explicit Fourier-Laplace reconstruction,
envelope bound, and escaping cleared cutoff are required. -/

noncomputable section
namespace GapFamily.Construction.PermanentSpectrumData
open Set Filter MeasureTheory Real
open scoped Topology UpperHalfPlane
open Analytic
variable {b : ℝ} (D : PermanentSpectrumData b)

/-- The actual finite-stage residual has a quantitative all-spin thermal tail
bound at every upper-half-plane point. -/
theorem remainder_norm_le_of_tailDensity
    (a T C c : ℝ) (F : ℕ → ℍ → ℂ) (q : ℕ → ℤ → ℝ → ℝ) (R : ℕ → ℝ)
    (ha : 100 ≤ a) (hT : 1 ≤ T)
    (hdecomp : ∀ n τ, F n τ - D.reducedPrefix c n τ = tailDensityPointValue T (q n) τ)
    (hq : ∀ n j, ∀ᵐ E ∂(referenceMeasure j).restrict (Ici (max T |(j : ℝ)|)),
      |q n j E| ≤ C * tailEnvelopeNumerator a E j)
    (hz : ∀ n j, ∀ᵐ E ∂(referenceMeasure j).restrict (Ici (max T |(j : ℝ)|)),
      E < R n → q n j E = 0) (n : ℕ) (τ : ℍ) :
    ‖F n τ - D.reducedPrefix c n τ‖ ≤
      sqrt τ.im * C * tailEnvelopeThermalTail a T (2 * π * τ.im) (R n) := by
  rw [hdecomp]
  exact norm_tailDensityPointValue_le_cutoff a T C (R n) (q n) ha hT (hq n) (hz n) τ

/-- Clearing every fixed energy window makes the complete-output residual
vanish. This replaces a limit assumption by concrete density estimates. -/
theorem tendsto_remainder_of_tailDensity
    (a T C c : ℝ) (F : ℕ → ℍ → ℂ) (q : ℕ → ℤ → ℝ → ℝ) (R : ℕ → ℝ)
    (ha : 100 ≤ a) (hT : 1 ≤ T) (hR : Tendsto R atTop atTop)
    (hdecomp : ∀ n τ, F n τ - D.reducedPrefix c n τ = tailDensityPointValue T (q n) τ)
    (hq : ∀ n j, ∀ᵐ E ∂(referenceMeasure j).restrict (Ici (max T |(j : ℝ)|)),
      |q n j E| ≤ C * tailEnvelopeNumerator a E j)
    (hz : ∀ n j, ∀ᵐ E ∂(referenceMeasure j).restrict (Ici (max T |(j : ℝ)|)),
      E < R n → q n j E = 0) (τ : ℍ) :
    Tendsto (fun n => F n τ - D.reducedPrefix c n τ) atTop (𝓝 0) := by
  simp_rw [hdecomp]
  exact tendsto_tailDensityPointValue_of_cutoff a T C q R ha hT hR hq hz τ

/-- The complete modular correction functions converge to the exact public
character numerator of the permanent unit spectrum. -/
theorem tendsto_reducedNumerator_of_tailDensity
    (a T C c : ℝ) (F : ℕ → ℍ → ℂ) (q : ℕ → ℤ → ℝ → ℝ) (R : ℕ → ℝ)
    (ha : 100 ≤ a) (hT : 1 ≤ T) (hR : Tendsto R atTop atTop)
    (hthermal : ∀ t : ℝ, 0 < t → Summable (D.layerThermal t))
    (hdecomp : ∀ n τ, F n τ - D.reducedPrefix c n τ = tailDensityPointValue T (q n) τ)
    (hq : ∀ n j, ∀ᵐ E ∂(referenceMeasure j).restrict (Ici (max T |(j : ℝ)|)),
      |q n j E| ≤ C * tailEnvelopeNumerator a E j)
    (hz : ∀ n j, ∀ᵐ E ∂(referenceMeasure j).restrict (Ici (max T |(j : ℝ)|)),
      E < R n → q n j E = 0) :
    ∀ τ, Tendsto (fun n => F n τ) atTop (𝓝 (reducedNumerator c (D.spectrum c) τ)) :=
  D.tendsto_reducedNumerator_of_remainder c hthermal F
    (D.tendsto_remainder_of_tailDensity a T C c F q R ha hT hR hdecomp hq hz)

/-- Concrete ordinary density bounds yield the public admissibility and exact
marker gap of the same permanent spectrum. Modularity is required only of the
complete finite correction functions. -/
theorem pureAdmissible_and_hasGap_of_tailDensity
    (a T C : ℝ) {c : ℝ} (hc : 1 < c)
    (F : ℕ → ℍ → ℂ) (q : ℕ → ℤ → ℝ → ℝ) (R : ℕ → ℝ)
    (ha : 100 ≤ a) (hT : 1 ≤ T) (hR : Tendsto R atTop atTop)
    (hthermal : ∀ t : ℝ, 0 < t → Summable (D.layerThermal t))
    (hS : ∀ n τ, F n (ModularGroup.S • τ) = F n τ)
    (hTmod : ∀ n τ, F n (ModularGroup.T • τ) = F n τ)
    (hdecomp : ∀ n τ, F n τ - D.reducedPrefix c n τ = tailDensityPointValue T (q n) τ)
    (hq : ∀ n j, ∀ᵐ E ∂(referenceMeasure j).restrict (Ici (max T |(j : ℝ)|)),
      |q n j E| ≤ C * tailEnvelopeNumerator a E j)
    (hz : ∀ n j, ∀ᵐ E ∂(referenceMeasure j).restrict (Ici (max T |(j : ℝ)|)),
      E < R n → q n j E = 0) :
    PureAdmissible c (D.spectrum c) ∧ HasGap (D.spectrum c) (shift c + b) :=
  D.pureAdmissible_and_hasGap_of_remainder hc hthermal F hS hTmod
    (D.tendsto_remainder_of_tailDensity a T C c F q R ha hT hR hdecomp hq hz)

end GapFamily.Construction.PermanentSpectrumData
