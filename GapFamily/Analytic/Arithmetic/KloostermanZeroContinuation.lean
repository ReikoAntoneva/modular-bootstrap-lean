import GapFamily.Analytic.Arithmetic.KloostermanZeroContinuationReciprocal
import GapFamily.Analytic.Arithmetic.KloostermanZeroContinuationRamanujan
import GapFamily.Analytic.Arithmetic.KloostermanZeroContinuationTotient
import GapFamily.Analytic.Arithmetic.KloostermanDirichletSelberg
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# The zero-frequency Kloosterman continuation

The actual absolutely convergent series agrees with the explicit divisor/zeta
formula. Its canonical regularization is analytic at the spectral threshold.
The threshold derivatives are arithmetic coefficients, without any assumed
identification with an inverse Fourier–Laplace transform.
-/

noncomputable section

namespace GapFamily.Analytic

open Complex Filter
open scoped Topology

/-- The finite divisor factor, for a signed Fourier frequency. -/
def zeroFrequencyDivisorFactor (j : ℤ) (s : ℂ) : ℂ :=
  ∑ d ∈ j.natAbs.divisors, (d : ℂ) ^ (1 - 2 * s)

theorem zeroFrequencyDivisorFactor_differentiable (j : ℤ) :
    Differentiable ℂ (zeroFrequencyDivisorFactor j) := by
  apply Differentiable.fun_sum
  intro d hd
  exact ((differentiable_const (1 : ℂ)).sub ((differentiable_const (2 : ℂ)).mul differentiable_id)).const_cpow
    (Or.inl (Nat.cast_ne_zero.mpr (Nat.pos_of_mem_divisors hd).ne'))

theorem zeroFrequencyDivisorFactor_analyticAt (j : ℤ) (s : ℂ) :
    AnalyticAt ℂ (zeroFrequencyDivisorFactor j) s :=
  (zeroFrequencyDivisorFactor_differentiable j).analyticAt s

@[simp] theorem zeroFrequencyDivisorFactor_half (j : ℤ) :
    zeroFrequencyDivisorFactor j (1 / 2) = (j.natAbs.divisors.card : ℂ) := by
  simp [zeroFrequencyDivisorFactor]

/-- The primitive zero-frequency Dirichlet series is the actual reciprocal zeta. -/
theorem kloostermanDirichlet_zero_one_eq_inv_zeta {s : ℂ} (hs : 1 < s.re) :
    kloostermanDirichlet 0 1 s = (riemannZeta (2 * s))⁻¹ := by
  have h2s : 1 < (2 * s).re := by
    simp only [mul_re]; norm_num; linarith
  rw [kloostermanDirichlet_zero_one_eq_moebius_LSeries]
  have h := LSeries_one_mul_Lseries_moebius h2s
  rw [LSeries_one_eq_riemannZeta h2s] at h
  exact eq_inv_of_mul_eq_one_right h

/-- The Ramanujan divisor formula is an equality of genuine convergent sums. -/
theorem kloostermanDirichlet_zero_left_eq_zeta_div (j : ℤ) (hj : j ≠ 0)
    {s : ℂ} (hs : 1 < s.re) :
    kloostermanDirichlet 0 j s = zeroFrequencyDivisorFactor j s / riemannZeta (2 * s) := by
  rw [kloostermanDirichlet_zero_left j hj hs, kloostermanDirichlet_zero_one_eq_inv_zeta hs]
  rfl

/-- The zero-frequency continuation, using the actual ordinary zeta and divisor factor. -/
def zeroFrequencyKloostermanContinuation (j : ℤ) (s : ℂ) : ℂ :=
  (if j = 0 then riemannZeta (2 * s - 1) else zeroFrequencyDivisorFactor j s) *
    ordinaryZetaReciprocal (2 * s)

/-- Agreement on the original half-plane of absolute convergence. -/
theorem zeroFrequencyKloostermanContinuation_eq_series (j : ℤ)
    {s : ℂ} (hs : 1 < s.re) :
    zeroFrequencyKloostermanContinuation j s = kloostermanDirichlet 0 j s := by
  have h2s0 : 2 * s ≠ 0 := by
    intro h; have hr := congrArg Complex.re h; simp at hr; linarith
  have h2s1 : 2 * s ≠ 1 := by
    intro h; have hr := congrArg Complex.re h; simp at hr; linarith
  rw [zeroFrequencyKloostermanContinuation, ordinaryZetaReciprocal_eq_inv h2s0 h2s1]
  by_cases hj : j = 0
  · simp only [hj, ↓reduceIte]
    rw [kloostermanDirichlet_zero_zero_eq_zeta_div hs, div_eq_mul_inv]
  · simp only [hj, ↓reduceIte]
    rw [kloostermanDirichlet_zero_left_eq_zeta_div j hj hs, div_eq_mul_inv]

/-- The continued expression is itself the sum in the convergence region. -/
theorem zeroFrequencyKloostermanContinuation_hasSum (j : ℤ)
    {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun k : ℕ => kloostermanSum 0 j k / (k + 1 : ℂ) ^ (2 * s))
      (zeroFrequencyKloostermanContinuation j s) := by
  rw [zeroFrequencyKloostermanContinuation_eq_series j hs]
  exact kloostermanDirichlet_hasSum 0 j hs

theorem zeroFrequencyKloostermanContinuation_analyticAt (j : ℤ)
    {s : ℂ} (hs : 1 / 2 ≤ s.re) (hs1 : j = 0 → s ≠ 1) :
    AnalyticAt ℂ (zeroFrequencyKloostermanContinuation j) s := by
  have hr := ordinaryZetaReciprocal_two_mul_analyticAt hs
  by_cases hj : j = 0
  · have hz : 2 * s - 1 ≠ 1 := by
      intro h
      apply hs1 hj
      linear_combination h / 2
    have hn : AnalyticAt ℂ (fun z : ℂ => riemannZeta (2 * z - 1)) s :=
      (analyticOn_riemannZeta _ hz).comp (f := fun z : ℂ => 2 * z - 1)
        ((analyticAt_const.mul analyticAt_id).sub analyticAt_const)
    convert hn.mul hr using 1
    ext z
    simp [zeroFrequencyKloostermanContinuation, hj]
  · convert (zeroFrequencyDivisorFactor_analyticAt j s).mul hr using 1
    ext z
    simp [zeroFrequencyKloostermanContinuation, hj]

theorem zeroFrequencyKloostermanContinuation_analyticAt_half (j : ℤ) :
    AnalyticAt ℂ (zeroFrequencyKloostermanContinuation j) (1 / 2) := by
  apply zeroFrequencyKloostermanContinuation_analyticAt j
  · norm_num
  · intro _
    norm_num

@[simp] theorem zeroFrequencyKloostermanContinuation_half (j : ℤ) :
    zeroFrequencyKloostermanContinuation j (1 / 2) = 0 := by
  norm_num [zeroFrequencyKloostermanContinuation]

/-- The first threshold variation is the precise arithmetic coefficient. -/
theorem zeroFrequencyKloostermanContinuation_hasDerivAt_half (j : ℤ) :
    HasDerivAt (zeroFrequencyKloostermanContinuation j)
      (if j = 0 then -1 else 2 * (j.natAbs.divisors.card : ℂ)) (1 / 2) := by
  have hr := ordinaryZetaReciprocal_two_mul_hasDerivAt_half
  by_cases hj : j = 0
  · have hn : DifferentiableAt ℂ (fun z : ℂ => riemannZeta (2 * z - 1)) (1 / 2) :=
      (differentiableAt_riemannZeta (by norm_num : 2 * (1 / 2 : ℂ) - 1 ≠ 1)).comp
        (1 / 2) (((differentiableAt_const (2 : ℂ)).mul differentiableAt_id).sub_const 1)
    have h := hn.hasDerivAt.mul hr
    convert h using 1
    · ext s
      simp only [zeroFrequencyKloostermanContinuation, hj, ↓reduceIte, Pi.mul_apply]
    · norm_num [hj, riemannZeta_zero]
  · have h := (zeroFrequencyDivisorFactor_differentiable j (1 / 2)).hasDerivAt.mul hr
    convert h using 1
    · ext s
      simp only [zeroFrequencyKloostermanContinuation, hj, ↓reduceIte, Pi.mul_apply]
    · simp only [ite_eq_right hj, show 2 * (1 / 2 : ℂ) = 1 by norm_num,
        ordinaryZetaReciprocal_one, mul_zero, zero_add, zeroFrequencyDivisorFactor_half]
      ring

theorem zeroFrequencyKloostermanContinuation_tendsto_half (j : ℤ) :
    Tendsto (zeroFrequencyKloostermanContinuation j) (𝓝 (1 / 2)) (𝓝 0) := by
  rw [← zeroFrequencyKloostermanContinuation_half j]
  exact (zeroFrequencyKloostermanContinuation_analyticAt_half j).continuousAt

/-- Away from the denominator pole, the continuation is the ordinary zeta quotient. -/
theorem zeroFrequencyKloostermanContinuation_eq_quotient (j : ℤ) {s : ℂ}
    (hs0 : s ≠ 0) (hshalf : s ≠ 1 / 2) :
    zeroFrequencyKloostermanContinuation j s =
      (if j = 0 then riemannZeta (2 * s - 1) else zeroFrequencyDivisorFactor j s) /
        riemannZeta (2 * s) := by
  have h2s0 : 2 * s ≠ 0 := mul_ne_zero (by norm_num) hs0
  have h2s1 : 2 * s ≠ 1 := by
    intro h
    apply hshalf
    linear_combination h / 2
  rw [zeroFrequencyKloostermanContinuation,
    ordinaryZetaReciprocal_eq_inv h2s0 h2s1, div_eq_mul_inv]

/-- Either placement of the zero Fourier frequency gives the same continuation. -/
theorem zeroFrequencyKloostermanContinuation_eq_series_right (j : ℤ)
    {s : ℂ} (hs : 1 < s.re) :
    zeroFrequencyKloostermanContinuation j s = kloostermanDirichlet j 0 s := by
  rw [kloostermanDirichlet_symm j 0]
  exact zeroFrequencyKloostermanContinuation_eq_series j hs

/-- The limit uses the actual zeta quotient through the punctured threshold. -/
theorem zeroFrequencyKloosterman_quotient_tendsto_half (j : ℤ) :
    Tendsto (fun s : ℂ =>
      (if j = 0 then riemannZeta (2 * s - 1) else zeroFrequencyDivisorFactor j s) /
        riemannZeta (2 * s)) (𝓝[≠] (1 / 2)) (𝓝 0) := by
  apply ((zeroFrequencyKloostermanContinuation_tendsto_half j).mono_left
    nhdsWithin_le_nhds).congr'
  have h0 : ∀ᶠ s : ℂ in 𝓝[≠] (1 / 2), s ≠ 0 :=
    (eventually_ne_nhds (by norm_num : (1 / 2 : ℂ) ≠ 0)).filter_mono nhdsWithin_le_nhds
  filter_upwards [h0, self_mem_nhdsWithin] with s hs0 hshalf
  exact zeroFrequencyKloostermanContinuation_eq_quotient j hs0 hshalf

/-- Dividing out the simple threshold zero gives the exact arithmetic limit. -/
theorem zeroFrequencyKloostermanContinuation_div_tendsto_half (j : ℤ) :
    Tendsto (fun s : ℂ => zeroFrequencyKloostermanContinuation j s / (s - 1 / 2))
      (𝓝[≠] (1 / 2)) (𝓝 (if j = 0 then -1 else 2 * (j.natAbs.divisors.card : ℂ))) := by
  convert (zeroFrequencyKloostermanContinuation_hasDerivAt_half j).tendsto_slope using 1
  ext s
  rw [slope_def_field, zeroFrequencyKloostermanContinuation_half, sub_zero]

/-- The normalized limit also belongs to the actual punctured zeta quotient. -/
theorem zeroFrequencyKloosterman_quotient_div_tendsto_half (j : ℤ) :
    Tendsto (fun s : ℂ =>
      ((if j = 0 then riemannZeta (2 * s - 1) else zeroFrequencyDivisorFactor j s) /
        riemannZeta (2 * s)) / (s - 1 / 2))
      (𝓝[≠] (1 / 2)) (𝓝 (if j = 0 then -1 else 2 * (j.natAbs.divisors.card : ℂ))) := by
  apply (zeroFrequencyKloostermanContinuation_div_tendsto_half j).congr'
  have h0 : ∀ᶠ s : ℂ in 𝓝[≠] (1 / 2), s ≠ 0 :=
    (eventually_ne_nhds (by norm_num : (1 / 2 : ℂ) ≠ 0)).filter_mono nhdsWithin_le_nhds
  filter_upwards [h0, self_mem_nhdsWithin] with s hs0 hshalf
  rw [zeroFrequencyKloostermanContinuation_eq_quotient j hs0 hshalf]

end GapFamily.Analytic
