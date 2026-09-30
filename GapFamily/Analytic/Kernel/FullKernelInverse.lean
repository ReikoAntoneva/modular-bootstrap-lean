import GapFamily.Analytic.Kernel.FullKernelPositivity
import GapFamily.Analytic.Kernel.FullKernelCoercivityBound
import GapFamily.Analytic.Kernel.FullKernelScalarAnchorBound
import GapFamily.Analytic.Kernel.LowBandSpinSet

/-! The actual physical low-band inverse. Spatial positivity and its proved
energy pairing discharge the positivity premises in the quantitative coercivity estimate.
The scalar Fourier–Laplace formula used by the spatial-energy bridge is
proved from the Gamma integral and ordinary Fourier inversion. -/

noncomputable section

open Real

namespace GapFamily.Analytic

theorem correctedLowBandIdentityPlus_exp_coercive
    {ι : Type*} [Fintype ι] (J : ι → ℤ) (hJ : Function.Injective J)
    (B : ℝ) (hB : 1 ≤ B) (hband : ∀ i, |(J i : ℝ)| < B)
    (f : LowBandHilbert J B) :
    exp (-correctedLowBandCoercivityExponent * B) * ‖f‖ ^ 2 ≤
      (inner ℂ f (correctedLowBandIdentityPlus J B f)).re :=
  correctedLowBandIdentityPlus_exp_coercive_of_positive J hJ B hB hband
    (isPositive_correctedLowBandIdentityPlus J hJ (4 * B)) f

theorem isUnit_correctedLowBandIdentityPlus
    {ι : Type*} [Fintype ι] (J : ι → ℤ) (hJ : Function.Injective J)
    (B : ℝ) (hB : 1 ≤ B) (hband : ∀ i, |(J i : ℝ)| < B) :
    IsUnit (correctedLowBandIdentityPlus J B) :=
  isUnit_correctedLowBandIdentityPlus_of_positive J hJ B hB hband
    (isPositive_correctedLowBandIdentityPlus J hJ (4 * B))

theorem correctedLowBandIdentityPlus_inverse
    {ι : Type*} [Fintype ι] (J : ι → ℤ) (hJ : Function.Injective J)
    (B : ℝ) (hB : 1 ≤ B) (hband : ∀ i, |(J i : ℝ)| < B)
    (f : LowBandHilbert J B) :
    correctedLowBandIdentityPlus J B (correctedLowBandInverse J B f) = f :=
  correctedLowBandIdentityPlus_inverse_of_positive J hJ B hB hband
    (isPositive_correctedLowBandIdentityPlus J hJ (4 * B)) f

theorem correctedLowBandInverse_identityPlus
    {ι : Type*} [Fintype ι] (J : ι → ℤ) (hJ : Function.Injective J)
    (B : ℝ) (hB : 1 ≤ B) (hband : ∀ i, |(J i : ℝ)| < B)
    (f : LowBandHilbert J B) :
    correctedLowBandInverse J B (correctedLowBandIdentityPlus J B f) = f := by
  exact congrArg (fun P : LowBandHilbert J B →L[ℂ] LowBandHilbert J B => P f)
    (Ring.inverse_mul_cancel _ (isUnit_correctedLowBandIdentityPlus J hJ B hB hband))

theorem norm_correctedLowBandInverse_le_exp
    {ι : Type*} [Fintype ι] (J : ι → ℤ) (hJ : Function.Injective J)
    (B : ℝ) (hB : 1 ≤ B) (hband : ∀ i, |(J i : ℝ)| < B) :
    ‖correctedLowBandInverse J B‖ ≤ exp (correctedLowBandCoercivityExponent * B) :=
  norm_correctedLowBandInverse_le_exp_of_positive J hJ B hB hband
    (isPositive_correctedLowBandIdentityPlus J hJ (4 * B))

/-- Every canonical physical band has its actual bounded inverse. -/
theorem isUnit_correctedLowBandIdentityPlus_canonical (B : ℝ) (hB : 1 ≤ B) :
    IsUnit (correctedLowBandIdentityPlus (fun i : LowBandSpin B => (i : ℤ)) B) :=
  isUnit_correctedLowBandIdentityPlus _ (lowBandSpin_injective B) B hB (lowBandSpin_physical B)

end GapFamily.Analytic
