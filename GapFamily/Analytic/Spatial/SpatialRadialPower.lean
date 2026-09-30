import GapFamily.Analytic.Poincare.PoincarePowerHigher

noncomputable section
namespace GapFamily.Analytic.SpatialPoint
open Filter Set
open scoped Topology ContDiff

/-- The radial-power normalization has constant one-quarter prefactor. -/
def radialPower (s : ℂ) (q : ℝ) : ℂ := (1 / 4 : ℂ) * (q : ℂ) ^ (-s)

theorem radialPower_contDiffAt (s : ℂ) {q : ℝ} (hq : 0 < q) :
    ContDiffAt ℝ ∞ (radialPower s) q := by
  exact contDiffAt_const.mul (PoincarePowerHigher.contDiffAt_realPower (-s) hq)

theorem deriv_radialPower (s : ℂ) {q : ℝ} (hq : 0 < q) :
    deriv (radialPower s) q = (1 / 4 : ℂ) * (-s) * (q : ℂ) ^ (-s - 1) := by
  change deriv (fun t : ℝ => (1 / 4 : ℂ) * (t : ℂ) ^ (-s)) q = _
  simpa only [mul_assoc] using
    ((PoincarePowerHigher.hasDerivAt_realPower (-s) hq).const_mul (1 / 4 : ℂ)).deriv

theorem second_deriv_radialPower (s : ℂ) {q : ℝ} (hq : 0 < q) :
    deriv (deriv (radialPower s)) q =
      (1 / 4 : ℂ) * (-s) * (-s - 1) * (q : ℂ) ^ (-s - 2) := by
  have heq : deriv (radialPower s) =ᶠ[𝓝 q]
      (fun t : ℝ => (1 / 4 : ℂ) * (-s) * (t : ℂ) ^ (-s - 1)) := by
    filter_upwards [Ioi_mem_nhds hq] with t ht
    exact deriv_radialPower s ht
  rw [heq.deriv_eq]
  have h := ((PoincarePowerHigher.hasDerivAt_realPower (-s - 1) hq).const_mul
    ((1 / 4 : ℂ) * (-s))).deriv
  simpa only [show -s - 1 - 1 = -s - 2 by ring, mul_assoc] using h

/-- The exact radial ODE uses the same one-quarter normalization at s and s+1. -/
theorem radialPower_recurrence (s : ℂ) {q : ℝ} (hq : 0 < q) :
    -(q * (q - 1) : ℝ) • deriv (deriv (radialPower s)) q -
        (2 * q - 1 : ℝ) • deriv (radialPower s) q -
        s * (1 - s) * radialPower s q =
      s ^ 2 * radialPower (s + 1) q := by
  have hq0 : (q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hq.ne'
  have hp1 : (q : ℂ) ^ (-s - 1) = (q : ℂ) ^ (-s - 2) * (q : ℂ) := by
    calc
      (q : ℂ) ^ (-s - 1) = (q : ℂ) ^ ((-s - 2) + 1) := by congr 1; ring
      _ = (q : ℂ) ^ (-s - 2) * (q : ℂ) := by
        rw [Complex.cpow_add _ _ hq0, Complex.cpow_one]
  have hp2 : (q : ℂ) ^ (-s) = (q : ℂ) ^ (-s - 2) * (q : ℂ) ^ 2 := by
    calc
      (q : ℂ) ^ (-s) = (q : ℂ) ^ ((-s - 2) + 2) := by congr 1; ring
      _ = (q : ℂ) ^ (-s - 2) * (q : ℂ) ^ 2 := by
        rw [Complex.cpow_add _ _ hq0]
        norm_cast
  rw [second_deriv_radialPower s hq, deriv_radialPower s hq]
  simp only [radialPower, Complex.real_smul, Complex.ofReal_neg,
    Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_ofNat]
  rw [show -(s + 1) = -s - 1 by ring, hp1, hp2]
  ring

end GapFamily.Analytic.SpatialPoint
