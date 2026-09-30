import BTZEntropy.Comparison.SmoothApproximation
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-! Recover a smooth unit-interval function from its cosine Fourier coefficients. -/

noncomputable section

open Set
open scoped Real

namespace BTZEntropy

/-- The cosine pullback of a real function, as a continuous function on the unit circle. -/
def cosineCircle (h : ℝ → ℝ) (hh : Continuous h) : C(AddCircle (1 : ℝ), ℂ) where
  toFun z := (h ((1 + (fourier 1 z).re) / 2) : ℂ)
  continuous_toFun := Complex.continuous_ofReal.comp
    (hh.comp ((continuous_const.add (Complex.continuous_re.comp (fourier 1).continuous)).div_const 2))

/-- The period-one real-line representative of `cosineCircle`. -/
def cosineLine (h : ℝ → ℝ) (t : ℝ) : ℂ :=
  (h ((1 + Real.cos (2 * Real.pi * t)) / 2) : ℂ)

theorem fourier_unit_re (n : ℤ) (t : ℝ) :
    (fourier n (t : AddCircle (1 : ℝ))).re = Real.cos (2 * Real.pi * n * t) := by
  rw [fourier_coe_apply, Complex.exp_re]
  simp [Complex.mul_re, Complex.mul_im]

theorem cosineCircle_coe (h : ℝ → ℝ) (hh : Continuous h) (t : ℝ) :
    cosineCircle h hh (t : AddCircle (1 : ℝ)) = cosineLine h t := by
  change (h ((1 + (fourier 1 (t : AddCircle (1 : ℝ))).re) / 2) : ℂ) = _
  rw [fourier_unit_re]
  simp [cosineLine]

theorem fourierCoeff_cosineCircle (h : ℝ → ℝ) (hh : Continuous h) (n : ℤ) :
    fourierCoeff (cosineCircle h hh) n =
      fourierCoeffOn (by norm_num : (0 : ℝ) < 1) (cosineLine h) n := by
  rw [fourierCoeff_eq_intervalIntegral _ _ 0, fourierCoeffOn_eq_integral]
  simp only [zero_add, sub_zero, div_one, one_smul, cosineCircle_coe]
  congr 1
  ext x
  simp only [fourier_coe_apply, sub_zero]

theorem cosineLine_periodic (h : ℝ → ℝ) : Function.Periodic (cosineLine h) 1 := by
  intro t
  simp only [cosineLine]
  rw [show 2 * Real.pi * (t + 1) = 2 * Real.pi * t + 2 * Real.pi by ring,
    Real.cos_add_two_pi]

theorem cosineLine_contDiff {h : ℝ → ℝ} {m : WithTop ℕ∞} (hh : ContDiff ℝ m h) :
    ContDiff ℝ m (cosineLine h) := by
  exact Complex.ofRealCLM.contDiff.comp
    (hh.comp ((contDiff_const.add
      (Real.contDiff_cos.comp (contDiff_const.mul contDiff_id))).div_const 2))

theorem fourier_unit_neg_argument (n : ℤ) (z : AddCircle (1 : ℝ)) :
    fourier n (-z) = star (fourier n z) := by
  change (↑(AddCircle.toCircle (n • -z)) : ℂ) = _
  rw [smul_neg]
  exact fourier_neg'

theorem cosineCircle_neg (h : ℝ → ℝ) (hh : Continuous h) (z : AddCircle (1 : ℝ)) :
    cosineCircle h hh (-z) = cosineCircle h hh z := by
  change (h ((1 + (fourier 1 (-z)).re) / 2) : ℂ) = _
  rw [fourier_unit_neg_argument]
  rfl

/-- Real Fourier coefficients of the cosine pullback. -/
def cosineCoefficient (h : ℝ → ℝ) (hh : Continuous h) (n : ℤ) : ℝ :=
  (fourierCoeff (cosineCircle h hh) n).re

theorem hasSum_cosineCircle (h : ℝ → ℝ) (hh : Continuous h)
    (hs : Summable (fourierCoeff (cosineCircle h hh))) (z : AddCircle (1 : ℝ)) :
    HasSum (fun n : ℤ => cosineCoefficient h hh n * (fourier n z).re)
      (h ((1 + (fourier 1 z).re) / 2)) := by
  have hp := has_pointwise_sum_fourier_series_of_summable hs z
  have hn := has_pointwise_sum_fourier_series_of_summable hs (-z)
  have ha := (Complex.hasSum_re (hp.add hn)).div_const 2
  convert ha using 1
  · ext n
    simp only [cosineCoefficient, smul_eq_mul, Complex.add_re,
      fourier_unit_neg_argument, Complex.mul_re, Complex.star_def,
      Complex.conj_re, Complex.conj_im]
    ring
  · rw [cosineCircle_neg]
    change _ = (h ((1 + (fourier 1 z).re) / 2) + h ((1 + (fourier 1 z).re) / 2)) / 2
    ring

/-- Summable Fourier coefficients recover the original function everywhere on `[0,1]`. -/
theorem hasSum_cosineCoefficient (h : ℝ → ℝ) (hh : Continuous h)
    (hs : Summable (fourierCoeff (cosineCircle h hh)))
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    HasSum (fun n : ℤ => cosineCoefficient h hh n * (unitChebyshev n).eval x) (h x) := by
  let θ := Real.arccos (2 * x - 1)
  let t := θ / (2 * Real.pi)
  have hcos : Real.cos θ = 2 * x - 1 :=
    Real.cos_arccos (by linarith [hx.1]) (by linarith [hx.2])
  have ht : 2 * Real.pi * t = θ := by
    dsimp [t]
    field_simp
  have hp : ∀ n : ℤ, (fourier n (t : AddCircle (1 : ℝ))).re =
      (unitChebyshev n).eval x := by
    intro n
    rw [fourier_unit_re, unitChebyshev_eval, ← hcos, Polynomial.Chebyshev.T_real_cos]
    congr 1
    rw [← ht]
    ring
  have hc : (1 + (fourier 1 (t : AddCircle (1 : ℝ))).re) / 2 = x := by
    rw [fourier_unit_re]
    norm_num
    rw [ht, hcos]
    ring
  have hs' := hasSum_cosineCircle h hh hs (t : AddCircle (1 : ℝ))
  rw [hc] at hs'
  simpa only [hp] using hs'

end BTZEntropy
