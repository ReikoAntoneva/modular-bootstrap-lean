import GapFamily.Character
import GapFamily.Analytic.Foundation.Eta
import GapFamily.NodeSpectrum

/-!
# Pointwise limits of complete modular corrections

The reduced numerator is the actual character numerator multiplied by the
square root of the imaginary part. Its eta denominator is invariant under
both generators. Hence pointwise convergence of invariant complete corrections
to this specific numerator proves invariance of the public partition function.

These implications do not construct a correction sequence or prove spectral
summability. Those remain separate explicit obligations in an application.
-/

noncomputable section

open Filter
open scoped UpperHalfPlane Topology

namespace GapFamily

/-- The complete reduced numerator, retaining the exact vacuum and primary terms. -/
def reducedNumerator (c : ℝ) (s : Spectrum) (τ : ℍ) : ℂ :=
  (Real.sqrt τ.im : ℂ) * (vacuumNumerator c τ +
    ∑' p : s.support, (s.multiplicity p : ℂ) * primaryNumerator c p τ)

/-- The actual eta factor connects the reduced numerator to the public character sum. -/
theorem partitionFunction_eq_reducedNumerator (c : ℝ) (s : Spectrum) (τ : ℍ) :
    partitionFunction c s τ =
      reducedNumerator c s τ / (Analytic.etaInvariantDenominator τ : ℂ) := by
  have hsqrt : (Real.sqrt τ.im : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr τ.im_pos).ne'
  rw [partitionFunction_eq_numerator]
  simp only [reducedNumerator, Analytic.etaInvariantDenominator,
    Complex.ofReal_mul, Complex.ofReal_pow]
  exact (mul_div_mul_left _ _ hsqrt).symm

/-- Invariance survives pointwise limits, using uniqueness of complex limits. -/
theorem invariant_of_pointwise_tendsto (transform : ℍ → ℍ)
    (F : ℕ → ℍ → ℂ) (limit : ℍ → ℂ)
    (hinvariant : ∀ n τ, F n (transform τ) = F n τ)
    (hlimit : ∀ τ, Tendsto (fun n => F n τ) atTop (𝓝 (limit τ))) :
    ∀ τ, limit (transform τ) = limit τ := by
  intro τ
  have hleft := hlimit (transform τ)
  have heq : (fun n => F n (transform τ)) = (fun n => F n τ) :=
    funext (fun n => hinvariant n τ)
  rw [heq] at hleft
  exact tendsto_nhds_unique hleft (hlimit τ)

/-- Invariance of this particular numerator gives invariance of its character function. -/
theorem partitionFunction_invariant_of_reducedNumerator (c : ℝ) (s : Spectrum)
    (transform : ℍ → ℍ)
    (hnumerator : ∀ τ, reducedNumerator c s (transform τ) = reducedNumerator c s τ)
    (hdenominator : ∀ τ,
      Analytic.etaInvariantDenominator (transform τ) = Analytic.etaInvariantDenominator τ) :
    ∀ τ, partitionFunction c s (transform τ) = partitionFunction c s τ := by
  intro τ
  rw [partitionFunction_eq_reducedNumerator, partitionFunction_eq_reducedNumerator,
    hnumerator τ, hdenominator τ]

/-- Complete modular corrections give full S/T invariance of the same spectral function. -/
theorem partitionFunction_modular_of_pointwise_limit (c : ℝ) (s : Spectrum)
    (F : ℕ → ℍ → ℂ)
    (hS : ∀ n τ, F n (ModularGroup.S • τ) = F n τ)
    (hT : ∀ n τ, F n (ModularGroup.T • τ) = F n τ)
    (hlimit : ∀ τ,
      Tendsto (fun n => F n τ) atTop (𝓝 (reducedNumerator c s τ))) :
    (∀ τ, partitionFunction c s (ModularGroup.S • τ) = partitionFunction c s τ) ∧
    (∀ τ, partitionFunction c s (ModularGroup.T • τ) = partitionFunction c s τ) := by
  constructor
  · exact partitionFunction_invariant_of_reducedNumerator c s (ModularGroup.S • ·)
      (invariant_of_pointwise_tendsto _ F _ hS hlimit)
      Analytic.etaInvariantDenominator_S
  · exact partitionFunction_invariant_of_reducedNumerator c s (ModularGroup.T • ·)
      (invariant_of_pointwise_tendsto _ F _ hT hlimit)
      Analytic.etaInvariantDenominator_T

/-- The complete node-to-spectrum bridge with modularity established by convergence. -/
theorem nodeSpectrum_pureAdmissible_of_pointwise_limit {ι : Type*} {c : ℝ}
    (hc : 1 < c) (E : ι → ℝ) (J : ι → ℤ)
    (hcone : ∀ i, |(J i : ℝ)| ≤ E i)
    (hlocal : ∀ B : ℝ, {i | E i ≤ B}.Finite)
    (hthermal : ∀ y : ℝ, 0 < y →
      Summable (fun i => Real.exp (-2 * Real.pi * y * E i)))
    (F : ℕ → ℍ → ℂ)
    (hS : ∀ n τ, F n (ModularGroup.S • τ) = F n τ)
    (hT : ∀ n τ, F n (ModularGroup.T • τ) = F n τ)
    (hlimit : ∀ τ, Tendsto (fun n => F n τ) atTop
      (𝓝 (reducedNumerator c (nodeSpectrum c E J) τ))) :
    PureAdmissible c (nodeSpectrum c E J) := by
  obtain ⟨hmodS, hmodT⟩ :=
    partitionFunction_modular_of_pointwise_limit c (nodeSpectrum c E J) F hS hT hlimit
  exact nodeSpectrum_pureAdmissible hc E J hcone hlocal hthermal hmodS hmodT

end GapFamily
