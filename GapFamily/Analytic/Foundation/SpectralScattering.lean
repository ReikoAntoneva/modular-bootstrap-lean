import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# The regularized modular scattering coefficient

The actual completed Riemann zeta function determines the scalar scattering
formula. Its removable value at `s = 1/2` is `-1`; reading the totalized values
of the two completed-zeta poles would not give the analytic continuation.

This module proves properties of that precise arithmetic formula. It does not
identify it with the constant term of a continued automorphic Eisenstein series.
-/

noncomputable section

namespace GapFamily.Analytic

open Complex Filter
open scoped Topology

/-- Twice the conventional Riemann xi function, normalized to one at zero and one. -/
def spectralXi (s : ℂ) : ℂ := s * (s - 1) * completedRiemannZeta₀ s + 1

@[simp] theorem spectralXi_zero : spectralXi 0 = 1 := by simp [spectralXi]

@[simp] theorem spectralXi_one : spectralXi 1 = 1 := by simp [spectralXi]

/-- The completed zeta with its two simple poles removed by multiplication. -/
theorem spectralXi_eq_mul_completedZeta {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    spectralXi s = s * (s - 1) * completedRiemannZeta s := by
  rw [completedRiemannZeta_eq]
  unfold spectralXi
  have h1 : 1 - s ≠ 0 := sub_ne_zero.mpr hs1.symm
  field_simp
  ring

/-- The pole-removed completed zeta is entire. -/
theorem differentiable_spectralXi : Differentiable ℂ spectralXi := by
  unfold spectralXi
  exact ((differentiable_id.mul (differentiable_id.sub_const 1)).mul
    differentiable_completedZeta₀).add_const 1

theorem spectralXi_analyticAt (s : ℂ) : AnalyticAt ℂ spectralXi s :=
  differentiable_spectralXi.analyticAt s

/-- The reflection law includes the formerly singular endpoints. -/
theorem spectralXi_one_sub (s : ℂ) : spectralXi (1 - s) = spectralXi s := by
  unfold spectralXi
  rw [completedRiemannZeta₀_one_sub]
  ring

/-- The zero-free line and half-plane give nonvanishing of the actual regularized zeta. -/
theorem spectralXi_ne_zero_of_one_le_re {s : ℂ} (hs : 1 ≤ s.re) : spectralXi s ≠ 0 := by
  by_cases hs1 : s = 1
  · simp [hs1]
  have hs0 : s ≠ 0 := by
    intro h
    norm_num [h] at hs
  have hzeta := riemannZeta_ne_zero_of_one_le_re hs
  have hcomp : completedRiemannZeta s ≠ 0 := by
    intro h
    apply hzeta
    rw [riemannZeta_def_of_ne_zero hs0, h, zero_div]
  rw [spectralXi_eq_mul_completedZeta hs0 hs1]
  exact mul_ne_zero (mul_ne_zero hs0 (sub_ne_zero.mpr hs1)) hcomp

/-- The reciprocal completed zeta with its endpoint zero supplied by analytic continuation. -/
def spectralZetaReciprocal (s : ℂ) : ℂ := s * (s - 1) / spectralXi s

@[simp] theorem spectralZetaReciprocal_one : spectralZetaReciprocal 1 = 0 := by
  simp [spectralZetaReciprocal]

theorem spectralZetaReciprocal_eq_inv {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    spectralZetaReciprocal s = (completedRiemannZeta s)⁻¹ := by
  rw [spectralZetaReciprocal, spectralXi_eq_mul_completedZeta hs0 hs1,
    ← one_div (completedRiemannZeta s)]
  simpa only [mul_one] using mul_div_mul_left 1 (completedRiemannZeta s)
    (mul_ne_zero hs0 (sub_ne_zero.mpr hs1))

theorem spectralZetaReciprocal_analyticAt {s : ℂ} (hs : 1 ≤ s.re) :
    AnalyticAt ℂ spectralZetaReciprocal s := by
  exact (analyticAt_id.mul (analyticAt_id.sub analyticAt_const)).div
    (spectralXi_analyticAt s) (spectralXi_ne_zero_of_one_le_re hs)

/-- The simple zero has derivative one, fixing the completed-zeta residue normalization. -/
theorem spectralZetaReciprocal_hasDerivAt_one : HasDerivAt spectralZetaReciprocal 1 1 := by
  have h := ((hasDerivAt_id (1 : ℂ)).mul ((hasDerivAt_id (1 : ℂ)).sub_const 1)).div
    (differentiable_spectralXi 1).hasDerivAt (by simp : spectralXi 1 ≠ 0)
  convert h using 1 <;> first | rfl | simp

/-- The coefficient of the nonconstant Fourier modes, before the factor `sqrt y`. -/
def spectralFourierFactor (s : ℂ) : ℂ := 2 * spectralZetaReciprocal (2 * s)

@[simp] theorem spectralFourierFactor_half : spectralFourierFactor (1 / 2) = 0 := by
  norm_num [spectralFourierFactor]

theorem spectralFourierFactor_eq_quotient {s : ℂ}
    (hs0 : s ≠ 0) (hshalf : s ≠ 1 / 2) :
    spectralFourierFactor s = 2 / completedRiemannZeta (2 * s) := by
  have h2s0 : 2 * s ≠ 0 := mul_ne_zero (by norm_num) hs0
  have h2s1 : 2 * s ≠ 1 := by intro h; apply hshalf; linear_combination h / 2
  rw [spectralFourierFactor, spectralZetaReciprocal_eq_inv h2s0 h2s1, div_eq_mul_inv]

/-- The first Fourier coefficient variation at the threshold carries exactly the factor four. -/
theorem spectralFourierFactor_hasDerivAt_half : HasDerivAt spectralFourierFactor 4 (1 / 2) := by
  have harg : HasDerivAt (fun s : ℂ => 2 * s) 2 (1 / 2) := by
    simpa using (hasDerivAt_id (1 / 2 : ℂ)).const_mul 2
  have hrec : HasDerivAt spectralZetaReciprocal 1 (2 * (1 / 2 : ℂ)) := by
    norm_num
    exact spectralZetaReciprocal_hasDerivAt_one
  have h := (hrec.comp (1 / 2 : ℂ) harg).const_mul 2
  convert h using 1 <;> first | rfl | norm_num [Function.comp_def]

/-- The modular scattering formula with its removable threshold singularity filled in. -/
def spectralScattering (s : ℂ) : ℂ :=
  (s / (s - 1)) * spectralXi (2 * s - 1) / spectralXi (2 * s)

/-- Off the two completed-zeta poles, the regular formula is the precise zeta quotient. -/
theorem spectralScattering_eq_completedZeta_quotient {s : ℂ}
    (hs0 : s ≠ 0) (hshalf : s ≠ 1 / 2) (hs1 : s ≠ 1) :
    spectralScattering s = completedRiemannZeta (2 * s - 1) /
      completedRiemannZeta (2 * s) := by
  have h2s0 : 2 * s ≠ 0 := mul_ne_zero (by norm_num) hs0
  have h2s1 : 2 * s ≠ 1 := by intro h; apply hshalf; linear_combination h / 2
  have h2sm0 : 2 * s - 1 ≠ 0 := sub_ne_zero.mpr h2s1
  have h2sm1 : 2 * s - 1 ≠ 1 := by intro h; apply hs1; linear_combination h / 2
  rw [spectralScattering, spectralXi_eq_mul_completedZeta h2sm0 h2sm1,
    spectralXi_eq_mul_completedZeta h2s0 h2s1]
  have hcancel : (s / (s - 1)) * ((2 * s - 1) * (2 * s - 1 - 1)) =
      (2 * s) * (2 * s - 1) := by
    field_simp
    ring
  rw [← mul_assoc, hcancel, mul_div_mul_left _ _ (mul_ne_zero h2s0 h2sm0)]

/-- The scalar incoming and outgoing coefficients cancel at the spectral threshold. -/
@[simp] theorem spectralScattering_half : spectralScattering (1 / 2) = -1 := by
  norm_num [spectralScattering]

/-- Reflection exchanges the scalar incoming and outgoing coefficients. -/
theorem spectralScattering_one_sub (s : ℂ) :
    spectralScattering (1 - s) = (spectralScattering s)⁻¹ := by
  have hnum : spectralXi (2 * (1 - s) - 1) = spectralXi (2 * s) := by
    rw [show 2 * (1 - s) - 1 = 1 - 2 * s by ring, spectralXi_one_sub]
  have hden : spectralXi (2 * (1 - s)) = spectralXi (2 * s - 1) := by
    rw [show 2 * (1 - s) = 1 - (2 * s - 1) by ring, spectralXi_one_sub]
  have hrat : (1 - s) / (1 - s - 1) = (s / (s - 1))⁻¹ := by
    rw [show 1 - s - 1 = -s by ring, show 1 - s = -(s - 1) by ring,
      neg_div_neg_eq, inv_div]
  simp only [spectralScattering, hnum, hden, hrat, div_eq_mul_inv,
    mul_inv_rev, inv_inv]
  ring

/-- The regularized denominator never vanishes in the closed physical half-plane. -/
theorem spectralXi_two_mul_ne_zero {s : ℂ} (hs : 1 / 2 ≤ s.re) :
    spectralXi (2 * s) ≠ 0 := by
  apply spectralXi_ne_zero_of_one_le_re
  norm_num
  linarith

/-- The only possible pole in the physical half-plane is at `s = 1`. -/
theorem spectralScattering_analyticAt {s : ℂ} (hs : 1 / 2 ≤ s.re) (hs1 : s ≠ 1) :
    AnalyticAt ℂ spectralScattering s := by
  unfold spectralScattering
  have hid : AnalyticAt ℂ (fun z : ℂ => z) s := analyticAt_id
  exact ((hid.div (hid.sub analyticAt_const) (sub_ne_zero.mpr hs1)).mul
    ((spectralXi_analyticAt (2 * s - 1)).comp (f := fun z : ℂ => 2 * z - 1)
      ((analyticAt_const.mul hid).sub analyticAt_const))).div
    ((spectralXi_analyticAt (2 * s)).comp (f := fun z : ℂ => 2 * z)
      (analyticAt_const.mul hid))
    (spectralXi_two_mul_ne_zero hs)

/-- Analyticity at one half proves that the value `-1` is a genuine removable value. -/
theorem spectralScattering_analyticAt_half : AnalyticAt ℂ spectralScattering (1 / 2) := by
  apply spectralScattering_analyticAt
  · norm_num
  · norm_num

/-- The limit is taken through the actual regular coefficient, not a default quotient value. -/
theorem spectralScattering_tendsto_half :
    Tendsto spectralScattering (𝓝 (1 / 2)) (𝓝 (-1)) := by
  rw [← spectralScattering_half]
  exact spectralScattering_analyticAt_half.continuousAt

/-- The actual completed-zeta quotient has limit `-1` through the punctured threshold. -/
theorem completedZeta_scattering_quotient_tendsto_half :
    Tendsto (fun s : ℂ => completedRiemannZeta (2 * s - 1) /
      completedRiemannZeta (2 * s)) (𝓝[≠] (1 / 2)) (𝓝 (-1)) := by
  apply (spectralScattering_tendsto_half.mono_left nhdsWithin_le_nhds).congr'
  have h0 : ∀ᶠ s : ℂ in 𝓝[≠] (1 / 2), s ≠ 0 :=
    (eventually_ne_nhds (by norm_num : (1 / 2 : ℂ) ≠ 0)).filter_mono nhdsWithin_le_nhds
  have h1 : ∀ᶠ s : ℂ in 𝓝[≠] (1 / 2), s ≠ 1 :=
    (eventually_ne_nhds (by norm_num : (1 / 2 : ℂ) ≠ 1)).filter_mono nhdsWithin_le_nhds
  filter_upwards [h0, h1, self_mem_nhdsWithin] with s hs0 hs1 hshalf
  exact spectralScattering_eq_completedZeta_quotient hs0 hshalf hs1

end GapFamily.Analytic
