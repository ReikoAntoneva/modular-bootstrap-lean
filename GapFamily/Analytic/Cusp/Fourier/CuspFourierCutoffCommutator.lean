import GapFamily.Analytic.Cusp.Fourier.CuspFourierCutoffProfile
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

noncomputable section

namespace GapFamily.Analytic.CuspFourierCutoff

open Set Filter
open scoped Topology

def radial (κ : ℂ) (y : ℝ) : ℂ := (cutoff y : ℂ) * (y : ℂ) ^ exponent κ

theorem hasDerivAt_power (a : ℂ) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (fun x : ℝ => (x : ℂ) ^ a) (a * (y : ℂ) ^ (a - 1)) y :=
  (Complex.hasStrictDerivAt_cpow_const (x := (y : ℂ)) (c := a)
    (by simp [hy])).hasDerivAt.comp_ofReal

theorem hasDerivAt_radial (κ : ℂ) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (radial κ)
      (((deriv cutoff y : ℝ) : ℂ) * (y : ℂ) ^ exponent κ +
        (cutoff y : ℂ) * (exponent κ * (y : ℂ) ^ (exponent κ - 1))) y := by
  exact ((contDiff_cutoff.differentiable (by norm_num) y).hasDerivAt.ofReal_comp).mul
    (hasDerivAt_power (exponent κ) hy)

theorem deriv_radial (κ : ℂ) {y : ℝ} (hy : 0 < y) :
    deriv (radial κ) y =
      ((deriv cutoff y : ℝ) : ℂ) * (y : ℂ) ^ exponent κ +
        (cutoff y : ℂ) * (exponent κ * (y : ℂ) ^ (exponent κ - 1)) :=
  (hasDerivAt_radial κ hy).deriv

theorem deriv2_radial (κ : ℂ) {y : ℝ} (hy : 0 < y) :
    deriv (deriv (radial κ)) y =
      ((deriv (deriv cutoff) y : ℝ) : ℂ) * (y : ℂ) ^ exponent κ +
        2 * ((deriv cutoff y : ℝ) : ℂ) * exponent κ * (y : ℂ) ^ (exponent κ - 1) +
        (cutoff y : ℂ) * exponent κ * (exponent κ - 1) *
          (y : ℂ) ^ (exponent κ - 2) := by
  have heq : deriv (radial κ) =ᶠ[𝓝 y]
      (fun x : ℝ => ((deriv cutoff x : ℝ) : ℂ) * (x : ℂ) ^ exponent κ +
        (cutoff x : ℂ) * (exponent κ * (x : ℂ) ^ (exponent κ - 1))) := by
    filter_upwards [Ioi_mem_nhds hy] with x hx using deriv_radial κ hx
  have hc := (contDiff_cutoff.differentiable (by norm_num) y).hasDerivAt.ofReal_comp
  have hc' := (contDiff_deriv_cutoff.differentiable (by norm_num) y).hasDerivAt.ofReal_comp
  have hp := hasDerivAt_power (exponent κ) hy
  have hp' := (hasDerivAt_power (exponent κ - 1) hy).const_mul (exponent κ)
  have hd := ((hc'.mul hp).add (hc.mul hp')).congr_of_eventuallyEq heq
  rw [hd.deriv]
  simp only [sub_sub]
  ring_nf

theorem sq_mul_power (a : ℂ) {y : ℝ} (hy : 0 < y) :
    (y : ℂ) ^ 2 * (y : ℂ) ^ a = (y : ℂ) ^ (a + 2) := by
  calc
    (y : ℂ) ^ 2 * (y : ℂ) ^ a = (y : ℂ) ^ (2 : ℂ) * (y : ℂ) ^ a := by
      simp
    _ = (y : ℂ) ^ ((2 : ℂ) + a) :=
      (Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hy.ne')).symm
    _ = (y : ℂ) ^ (a + 2) := by rw [add_comm]

/-- The radial Laplacian minus its eigenvalue leaves the negative cutoff profile. -/
theorem radial_commutator (κ : ℂ) {y : ℝ} (hy : 0 < y) :
    -(y : ℂ) ^ 2 * deriv (deriv (radial κ)) y -
      exponent κ * (1 - exponent κ) * radial κ y = -profile κ y := by
  have h₀ := sq_mul_power (exponent κ) hy
  have h₁ : (y : ℂ) ^ 2 * (y : ℂ) ^ (exponent κ - 1) =
      (y : ℂ) ^ (exponent κ + 1) := by
    rw [sq_mul_power _ hy]
    congr 1
    ring
  have h₂ : (y : ℂ) ^ 2 * (y : ℂ) ^ (exponent κ - 2) =
      (y : ℂ) ^ exponent κ := by
    rw [sq_mul_power _ hy, sub_add_cancel]
  rw [deriv2_radial κ hy]
  unfold radial profile
  linear_combination
    -((deriv (deriv cutoff) y : ℝ) : ℂ) * h₀ -
      2 * exponent κ * ((deriv cutoff y : ℝ) : ℂ) * h₁ -
      (cutoff y : ℂ) * exponent κ * (exponent κ - 1) * h₂

/-- The literal integer Fourier mode has the expected horizontal second derivative. -/
theorem deriv2_mode (J : ℤ) (x : ℝ) :
    deriv (deriv (cuspFourierMode J)) x =
      -(2 * (Real.pi : ℂ) * (J : ℂ)) ^ 2 * cuspFourierMode J x := by
  have hm : deriv (cuspFourierMode J) =
      (fun t => (2 * (Real.pi : ℂ) * Complex.I * (J : ℂ)) * cuspFourierMode J t) :=
    funext fun t => (hasDerivAt_cuspFourierMode J t).deriv
  rw [hm, deriv_const_mul_field, (hasDerivAt_cuspFourierMode J x).deriv]
  have hI : (2 * (Real.pi : ℂ) * Complex.I * (J : ℂ)) ^ 2 =
      -(2 * (Real.pi : ℂ) * (J : ℂ)) ^ 2 := by
    calc
      _ = (2 * (Real.pi : ℂ) * (J : ℂ)) ^ 2 * Complex.I ^ 2 := by ring
      _ = _ := by rw [Complex.I_sq]; ring
  calc
    _ = (2 * (Real.pi : ℂ) * Complex.I * (J : ℂ)) ^ 2 * cuspFourierMode J x := by ring
    _ = _ := by rw [hI]

/-- A coordinate calculation only: this does not assert membership in any modular
operator domain. The nonzero Fourier potential and cutoff residual are explicit. -/
theorem fourier_coordinate_residual (J : ℤ) (κ : ℂ) (x : ℝ)
    {y : ℝ} (hy : 0 < y) :
    -(y : ℂ) ^ 2 *
        (deriv (deriv (fun t => radial κ y * cuspFourierMode J t)) x +
          deriv (deriv (fun t => radial κ t * cuspFourierMode J x)) y) -
      exponent κ * (1 - exponent κ) * radial κ y * cuspFourierMode J x =
      (2 * (Real.pi : ℂ) * (J : ℂ)) ^ 2 * (cutoff y : ℂ) *
        (y : ℂ) ^ (exponent κ + 2) * cuspFourierMode J x -
      profile κ y * cuspFourierMode J x := by
  rw [deriv_const_mul_field', deriv_const_mul_field,
    deriv_mul_const_field', deriv_mul_const_field, deriv2_mode]
  have hc := radial_commutator κ hy
  have hp := sq_mul_power (exponent κ) hy
  unfold radial at hc ⊢
  linear_combination
    cuspFourierMode J x * hc +
      (2 * (Real.pi : ℂ) * (J : ℂ)) ^ 2 * (cutoff y : ℂ) * cuspFourierMode J x * hp

end GapFamily.Analytic.CuspFourierCutoff
