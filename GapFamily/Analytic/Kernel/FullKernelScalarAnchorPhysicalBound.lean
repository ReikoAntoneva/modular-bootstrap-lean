import GapFamily.Analytic.Kernel.FullKernelInverse
import GapFamily.Analytic.Kernel.FullKernelScalarAnchorBound

/-! Physical scalar anchor bounds with the actual kernel positivity discharged. -/

noncomputable section
namespace GapFamily.Analytic
open Real Set

/-- The actual scalar anchor response has a uniform exponential bound on every fixed disk. -/
theorem norm_scalarAnchorResponseHol_le_exp
    {ι : Type*} [Fintype ι] (J : ι → ℤ) (hJ : Function.Injective J)
    (B : ℝ) (hB : 1 ≤ B) (hband : ∀ i, |(J i : ℝ)| < B)
    (R : ℝ) (hR : 0 ≤ R) (z : ℂ) (hz : ‖z‖ ≤ R) :
    ‖scalarAnchorResponseHol J B (by linarith) z‖ ≤
      exp (scalarAnchorResponseDiskExponent R * B) :=
  norm_scalarAnchorResponseHol_le_exp_of_positive J hJ B hB hband
    (isPositive_correctedLowBandIdentityPlus J hJ (4 * B)) R hR z hz

/-- The physical high-band response is controlled by the fixed square-root disk of radius two. -/
theorem abs_scalarAnchorResponsePhysical_le_exp
    {ι : Type*} [Fintype ι] (J : ι → ℤ) (hJ : Function.Injective J)
    (B : ℝ) (hB : 1 ≤ B) (hband : ∀ i, |(J i : ℝ)| < B)
    (E : ℝ) (hE : E ∈ scalarAnchorBand B) :
    |scalarAnchorResponsePhysical J B (by linarith) E| ≤
      exp (scalarAnchorResponseDiskExponent 2 * B) := by
  have hBpos : 0 < B := by linarith
  have hEupper : E ≤ 3 * B := hE.2
  have hratio : E / B ≤ 4 := (div_le_iff₀ hBpos).mpr (by linarith)
  have hroot : sqrt (E / B) ≤ 2 := (sqrt_le_left (by norm_num)).mpr (by norm_num; exact hratio)
  have hz : ‖(sqrt (E / B) : ℂ)‖ ≤ 2 := by
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sqrt_nonneg _)] using hroot
  exact (Complex.abs_re_le_norm _).trans
    (norm_scalarAnchorResponseHol_le_exp J hJ B hB hband 2 (by norm_num) _ hz)

/-- The actual high-band square mass has a uniform exponential lower bound. -/
theorem exp_neg_le_scalarAnchorResponseSquareMass
    {ι : Type*} [Fintype ι] (J : ι → ℤ) (hJ : Function.Injective J)
    (B : ℝ) (hB : 1 ≤ B) (hband : ∀ i, |(J i : ℝ)| < B) :
    exp (-scalarAnchorResponseMassExponent * B) ≤
      scalarAnchorSquareMass B (scalarAnchorResponsePhysical J B (by linarith)) :=
  exp_neg_le_scalarAnchorResponseSquareMass_of_positive J hJ B hB hband
    (isPositive_correctedLowBandIdentityPlus J hJ (4 * B))

/-- The actual high-band response has strictly positive normalizing square mass. -/
theorem scalarAnchorResponseSquareMass_pos
    {ι : Type*} [Fintype ι] (J : ι → ℤ) (hJ : Function.Injective J)
    (B : ℝ) (hB : 1 ≤ B) (hband : ∀ i, |(J i : ℝ)| < B) :
    0 < scalarAnchorSquareMass B (scalarAnchorResponsePhysical J B (by linarith)) :=
  (exp_pos _).trans_le (exp_neg_le_scalarAnchorResponseSquareMass J hJ B hB hband)

/-- The inverse square mass used to normalize the physical anchor has an exponential bound. -/
theorem scalarAnchorResponseSquareMass_inv_le_exp
    {ι : Type*} [Fintype ι] (J : ι → ℤ) (hJ : Function.Injective J)
    (B : ℝ) (hB : 1 ≤ B) (hband : ∀ i, |(J i : ℝ)| < B) :
    (scalarAnchorSquareMass B (scalarAnchorResponsePhysical J B (by linarith)))⁻¹ ≤
      exp (scalarAnchorResponseMassExponent * B) :=
  scalarAnchorResponseSquareMass_inv_le_exp_of_positive J hJ B hB hband
    (isPositive_correctedLowBandIdentityPlus J hJ (4 * B))

end GapFamily.Analytic
