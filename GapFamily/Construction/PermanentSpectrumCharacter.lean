import GapFamily.Convergence
import GapFamily.Analytic.Poincare.Poincare

/-! The actual unit-node seed series is exactly the reduced numerator of
the public spectrum after merging repeated coordinates. Absolute convergence
and finite-fibre regrouping follow from the stated thermal and local bounds. -/

noncomputable section

namespace GapFamily

open scoped UpperHalfPlane

variable {ι : Type*}

/-- Reconstructing a node's conformal coordinates preserves its exact
energy-spin exponential and the threshold height factor. -/
theorem sqrt_mul_primaryNumerator_nodeCoordinate
    (c : ℝ) (E : ι → ℝ) (J : ι → ℤ) (i : ι) (τ : ℍ) :
    (Real.sqrt τ.im : ℂ) * primaryNumerator c (nodeCoordinate c E J i) τ =
      Analytic.pointSeed (E i) (J i) (1 / 2) τ := by
  simp only [primaryNumerator, energy_nodeCoordinate, spin_nodeCoordinate,
    Analytic.pointSeed, ← Real.sqrt_eq_rpow]
  congr 2
  push_cast
  ring

/-- Unit-node primary numerators are absolutely summable under the actual
energy thermal sum, with no modularity hypothesis. -/
theorem node_primaryNumerator_norm_summable
    (c : ℝ) (E : ι → ℝ) (J : ι → ℤ) (τ : ℍ)
    (hthermal : Summable (fun i => Real.exp (-2 * Real.pi * τ.im * E i))) :
    Summable (fun i => ‖primaryNumerator c (nodeCoordinate c E J i) τ‖) := by
  simpa only [norm_primaryNumerator, energy_nodeCoordinate] using hthermal

/-- Absolute convergence of the actual unit threshold seed series. -/
theorem node_pointSeed_half_norm_summable
    (E : ι → ℝ) (J : ι → ℤ) (τ : ℍ)
    (hthermal : Summable (fun i => Real.exp (-2 * Real.pi * τ.im * E i))) :
    Summable (fun i => ‖Analytic.pointSeed (E i) (J i) (1 / 2) τ‖) := by
  have harg (i : ι) : -2 * Real.pi * E i * τ.im = -2 * Real.pi * τ.im * E i := by
    ring
  simp_rw [Analytic.norm_pointSeed, harg, ← Real.sqrt_eq_rpow]
  exact hthermal.mul_left _

theorem node_pointSeed_half_summable
    (E : ι → ℝ) (J : ι → ℤ) (τ : ℍ)
    (hthermal : Summable (fun i => Real.exp (-2 * Real.pi * τ.im * E i))) :
    Summable (fun i => Analytic.pointSeed (E i) (J i) (1 / 2) τ) :=
  (node_pointSeed_half_norm_summable E J τ hthermal).of_norm

/-- The literal multiplicities of repeated coordinates preserve the primary
numerator sum, using local finiteness and ordinary absolute convergence. -/
theorem nodeSpectrum_primaryNumerator_tsum
    (c : ℝ) (E : ι → ℝ) (J : ι → ℤ)
    (hlocal : ∀ B : ℝ, {i | E i ≤ B}.Finite) (τ : ℍ)
    (hthermal : Summable (fun i => Real.exp (-2 * Real.pi * τ.im * E i))) :
    (∑' p : (nodeSpectrum c E J).support,
      ((nodeSpectrum c E J).multiplicity p : ℂ) * primaryNumerator c p τ) =
      ∑' i, primaryNumerator c (nodeCoordinate c E J i) τ := by
  simpa only [nodeSpectrum, nsmul_eq_mul] using
    coordinateSpectrum_tsum (nodeCoordinate_locallyFinite c E J hlocal)
      (fun p => primaryNumerator c p τ)
      (node_primaryNumerator_norm_summable c E J τ hthermal).of_norm

/-- The public reduced character numerator is the exact vacuum numerator
plus the actual absolutely convergent unit-node threshold seed series.
No admissibility or modularity premise enters this identification. -/
theorem reducedNumerator_nodeSpectrum_eq_pointSeed_tsum
    (c : ℝ) (E : ι → ℝ) (J : ι → ℤ)
    (hlocal : ∀ B : ℝ, {i | E i ≤ B}.Finite) (τ : ℍ)
    (hthermal : Summable (fun i => Real.exp (-2 * Real.pi * τ.im * E i))) :
    reducedNumerator c (nodeSpectrum c E J) τ =
      (Real.sqrt τ.im : ℂ) * vacuumNumerator c τ +
        ∑' i, Analytic.pointSeed (E i) (J i) (1 / 2) τ := by
  rw [reducedNumerator, nodeSpectrum_primaryNumerator_tsum c E J hlocal τ hthermal,
    mul_add, ← tsum_mul_left]
  congr 1
  exact tsum_congr (fun i => sqrt_mul_primaryNumerator_nodeCoordinate c E J i τ)

end GapFamily
