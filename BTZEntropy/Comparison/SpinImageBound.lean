import GapFamily.Analytic.Transform.CosRootHigherFourier
import BTZEntropy.Comparison.SpinFourier
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Asymptotics.Defs

/-!
# Noncentral spin image bound

At a nonzero integer translation the denominator-one modular image loses a
strict amount in its leading exponential. The estimate retains polynomial
decay in the translation, so it can be summed. It is an estimate of the actual
kernel, not a presumed Poisson or spectral-comparison error.
-/

noncomputable section

open GapFamily.Analytic GapFamily.Analytic.CosRootLaplace

namespace BTZEntropy

/-- A summable bound for a single translated seed, before combining the four
vacuum seeds. The `a` dependence outside the exponential is only linear. -/
theorem norm_higherFourierKernel_one_le {a y E t : ℝ} {J : ℤ}
    (ha : 0 ≤ a) (hy : 0 < y) (hE : |E| ≤ a) (hJ : |(J : ℝ)| ≤ 1)
    (ht : 1 ≤ |t|) :
    ‖higherFourierKernel 1 y E 0 J t‖ ≤
      (2 * Real.pi * Real.sqrt y * (a * y + 1) *
        Real.exp (2 * Real.pi * (a * y / (1 + y ^ 2) + 1))) / t ^ 2 := by
  have htpos : 0 < |t| := lt_of_lt_of_le zero_lt_one ht
  have hD : 0 < t ^ 2 + y ^ 2 := by positivity
  have hD1 : 1 + y ^ 2 ≤ t ^ 2 + y ^ 2 := by nlinarith [sq_abs t]
  have habsD : |t| ≤ t ^ 2 + y ^ 2 := by nlinarith [sq_abs t, sq_nonneg y]
  have htD : t ^ 2 ≤ t ^ 2 + y ^ 2 := le_add_of_nonneg_right (sq_nonneg y)
  let z : ℂ := -2 * (Real.pi : ℂ) *
    (((E * y : ℝ) : ℂ) + (((J : ℝ) * t : ℝ) : ℂ) * Complex.I) /
      ((t ^ 2 + y ^ 2 : ℝ) : ℂ)
  have hDC : ‖(t : ℂ) ^ 2 + (y : ℂ) ^ 2‖ = t ^ 2 + y ^ 2 := by
    rw [← Complex.ofReal_pow, ← Complex.ofReal_pow, ← Complex.ofReal_add,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hD]
  have hz : ‖z‖ ≤ 2 * Real.pi * (a * y + |t|) / (t ^ 2 + y ^ 2) := by
    have hn : ‖(((E * y : ℝ) : ℂ) + (((J : ℝ) * t : ℝ) : ℂ) * Complex.I)‖ ≤
        a * y + |t| := by
      calc
        _ ≤ ‖((E * y : ℝ) : ℂ)‖ + ‖(((J : ℝ) * t : ℝ) : ℂ) * Complex.I‖ := norm_add_le _ _
        _ = |E| * y + |(J : ℝ)| * |t| := by
          simp [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hy]
        _ ≤ a * y + |t| := by nlinarith [mul_le_mul_of_nonneg_right hJ (abs_nonneg t)]
    simpa [z, norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hD, abs_of_pos Real.pi_pos, hDC] using
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hn
        (by positivity : 0 ≤ 2 * Real.pi)) hD.le
  have hzUniform : ‖z‖ ≤ 2 * Real.pi * (a * y / (1 + y ^ 2) + 1) := by
    apply hz.trans
    rw [mul_div_assoc, add_div]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact add_le_add (div_le_div_of_nonneg_left (mul_nonneg ha hy.le) (by positivity) hD1)
      ((div_le_one hD).mpr habsD)
  have hzDecay : ‖z‖ ≤ 2 * Real.pi * (a * y + 1) / |t| := by
    apply hz.trans
    rw [mul_div_assoc, mul_div_assoc, add_div, add_div]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply add_le_add (div_le_div_of_nonneg_left (mul_nonneg ha hy.le) htpos habsD)
    apply (div_le_div_iff₀ hD htpos).mpr
    nlinarith [sq_abs t]
  have hexp : ‖Complex.exp z - 1‖ ≤
      (2 * Real.pi * (a * y + 1) / |t|) *
        Real.exp (2 * Real.pi * (a * y / (1 + y ^ 2) + 1)) := by
    have he : ‖Complex.exp z - 1‖ ≤ ‖z‖ * Real.exp ‖z‖ := by
      simpa using Complex.norm_exp_sub_sum_le_norm_mul_exp z 1
    exact he.trans (mul_le_mul hzDecay (Real.exp_le_exp.mpr hzUniform)
      (Real.exp_pos _).le (by positivity))
  have hsqrt : |t| ≤ Real.sqrt (t ^ 2 + y ^ 2) := by
    rw [← Real.sqrt_sq_eq_abs t]
    exact Real.sqrt_le_sqrt htD
  rw [higherFourierKernel_eq_exp zero_lt_one hy E 0 J t]
  simp only [one_pow, one_mul, neg_zero, cuspFourierMode, Int.cast_zero, mul_zero,
    zero_mul, Complex.exp_zero, mul_one]
  change ‖((Real.sqrt y / Real.sqrt (t ^ 2 + y ^ 2) : ℝ) : ℂ) *
    (Complex.exp z - 1)‖ ≤ _
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc
    _ ≤ (Real.sqrt y / |t|) *
        ((2 * Real.pi * (a * y + 1) / |t|) *
          Real.exp (2 * Real.pi * (a * y / (1 + y ^ 2) + 1))) :=
      mul_le_mul (div_le_div_of_nonneg_left (Real.sqrt_nonneg y) htpos hsqrt) hexp
        (norm_nonneg _) (by positivity)
    _ = _ := by rw [← sq_abs t]; ring

/-- The nonzero translation exponent is strictly smaller than the central one. -/
def spinImageDecayRate (y : ℝ) : ℝ := 2 * Real.pi / (y * (1 + y ^ 2))

theorem spinImageDecayRate_pos {y : ℝ} (hy : 0 < y) :
    0 < spinImageDecayRate y := by unfold spinImageDecayRate; positivity

theorem spinImage_exponent_gap (a : ℝ) {y : ℝ} (hy : 0 < y) :
    2 * Real.pi * (a * y / (1 + y ^ 2) + 1) - 2 * Real.pi * a / y =
      2 * Real.pi - spinImageDecayRate y * a := by
  unfold spinImageDecayRate
  field_simp
  ring

/-- A compact interval of positive temperatures has one positive decay rate. -/
theorem spinImageDecayRate_antitone {y Y : ℝ} (hy : 0 < y) (hY : y ≤ Y) :
    spinImageDecayRate Y ≤ spinImageDecayRate y := by
  unfold spinImageDecayRate
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  have hsq : y ^ 2 ≤ Y ^ 2 := pow_le_pow_left₀ hy.le hY 2
  exact mul_le_mul hY (by linarith) (by positivity) (le_trans hy.le hY)

/-- Polynomial decay of the actual seed is sufficient for Poisson periodization. -/
theorem higherFourierKernel_one_isBigO {a y E : ℝ} {J : ℤ}
    (ha : 0 ≤ a) (hy : 0 < y) (hE : |E| ≤ a) (hJ : |(J : ℝ)| ≤ 1) :
    Asymptotics.IsBigO (Filter.cocompact ℝ) (higherFourierKernel 1 y E 0 J)
      (fun t : ℝ => |t| ^ (-(2 : ℝ))) := by
  refine Asymptotics.IsBigO.of_bound
    (2 * Real.pi * Real.sqrt y * (a * y + 1) *
      Real.exp (2 * Real.pi * (a * y / (1 + y ^ 2) + 1))) ?_
  filter_upwards [(isCompact_Icc (a := (-1 : ℝ)) (b := 1)).compl_mem_cocompact] with t ht
  have ht1 : 1 ≤ |t| := by
    by_contra h
    have habs : |t| < 1 := lt_of_not_ge h
    exact ht ⟨by linarith [(abs_lt.mp habs).1], (abs_lt.mp habs).2.le⟩
  have hpow : |t| ^ (-(2 : ℝ)) = 1 / t ^ 2 := by
    rw [Real.rpow_neg (abs_nonneg t), Real.rpow_two, sq_abs, one_div]
  rw [hpow, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ 1 / t ^ 2)]
  simpa only [mul_one_div] using norm_higherFourierKernel_one_le ha hy hE hJ ht1

/-- The four-seed image has one explicit, polynomial-in-`a` prefactor. -/
def spinImageBoundConstant (a y : ℝ) : ℝ :=
  8 * Real.pi * Real.sqrt y * (a * y + 1) *
    Real.exp (2 * Real.pi * (a * y / (1 + y ^ 2) + 1))

theorem norm_spinImageKernel_le {a y t : ℝ} (ha : 2 ≤ a) (hy : 0 < y)
    (ht : 1 ≤ |t|) :
    ‖spinImageKernel a y t‖ ≤ spinImageBoundConstant a y / t ^ 2 := by
  have h0 := norm_higherFourierKernel_one_le (by linarith : 0 ≤ a) hy
    (show |-a| ≤ a by rw [abs_neg, abs_of_nonneg (by linarith)])
    (by norm_num : |((0 : ℤ) : ℝ)| ≤ 1) ht
  have h1 : |1 - a| ≤ a := by rw [abs_of_nonpos (by linarith)]; linarith
  have h2 : |2 - a| ≤ a := by rw [abs_of_nonpos (by linarith)]; linarith
  have hp := norm_higherFourierKernel_one_le (by linarith : 0 ≤ a) hy h1
    (by norm_num : |((1 : ℤ) : ℝ)| ≤ 1) ht
  have hm := norm_higherFourierKernel_one_le (by linarith : 0 ≤ a) hy h1
    (by norm_num : |((-1 : ℤ) : ℝ)| ≤ 1) ht
  have hlast := norm_higherFourierKernel_one_le (by linarith : 0 ≤ a) hy h2
    (by norm_num : |((0 : ℤ) : ℝ)| ≤ 1) ht
  have h01 := norm_sub_le (higherFourierKernel 1 y (-a) 0 0 t)
    (higherFourierKernel 1 y (1 - a) 0 1 t)
  have h012 := norm_sub_le
    (higherFourierKernel 1 y (-a) 0 0 t - higherFourierKernel 1 y (1 - a) 0 1 t)
    (higherFourierKernel 1 y (1 - a) 0 (-1) t)
  have hall := norm_add_le
    (higherFourierKernel 1 y (-a) 0 0 t - higherFourierKernel 1 y (1 - a) 0 1 t -
      higherFourierKernel 1 y (1 - a) 0 (-1) t)
    (higherFourierKernel 1 y (2 - a) 0 0 t)
  calc
    _ ≤ 4 * ((2 * Real.pi * Real.sqrt y * (a * y + 1) *
        Real.exp (2 * Real.pi * (a * y / (1 + y ^ 2) + 1))) / t ^ 2) := by
      dsimp only [spinImageKernel]
      linarith only [hall, h012, h01, h0, hp, hm, hlast]
    _ = _ := by unfold spinImageBoundConstant; ring

/-- The actual nonzero integer translations, with the central image removed. -/
def spinImageTail (a y : ℝ) (n : ℤ) : ℂ :=
  if n = 0 then 0 else spinImageKernel a y n

theorem norm_spinImageTail_le {a y : ℝ} (ha : 2 ≤ a) (hy : 0 < y) (n : ℤ) :
    ‖spinImageTail a y n‖ ≤ spinImageBoundConstant a y / (n : ℝ) ^ 2 := by
  by_cases hn : n = 0
  · simp [spinImageTail, hn]
  · rw [spinImageTail, ite_eq_right hn]
    exact norm_spinImageKernel_le ha hy (by exact_mod_cast Int.one_le_abs hn)

theorem summable_norm_spinImageTail {a y : ℝ} (ha : 2 ≤ a) (hy : 0 < y) :
    Summable (fun n : ℤ => ‖spinImageTail a y n‖) := by
  have hs : Summable (fun n : ℤ => spinImageBoundConstant a y / (n : ℝ) ^ 2) := by
    simpa only [mul_one_div] using
      (Real.summable_one_div_int_pow.mpr (by decide : 1 < (2 : ℕ))).mul_left
        (spinImageBoundConstant a y)
  exact hs.of_nonneg_of_le (fun _ => norm_nonneg _) (norm_spinImageTail_le ha hy)

theorem norm_tsum_spinImageTail_le {a y : ℝ} (ha : 2 ≤ a) (hy : 0 < y) :
    ‖∑' n : ℤ, spinImageTail a y n‖ ≤
      spinImageBoundConstant a y * ∑' n : ℤ, 1 / (n : ℝ) ^ 2 := by
  have hs : Summable (fun n : ℤ => spinImageBoundConstant a y / (n : ℝ) ^ 2) := by
    simpa only [mul_one_div] using
      (Real.summable_one_div_int_pow.mpr (by decide : 1 < (2 : ℕ))).mul_left
        (spinImageBoundConstant a y)
  calc
    _ ≤ ∑' n : ℤ, ‖spinImageTail a y n‖ := norm_tsum_le_tsum_norm (summable_norm_spinImageTail ha hy)
    _ ≤ ∑' n : ℤ, spinImageBoundConstant a y / (n : ℝ) ^ 2 :=
      Summable.tsum_le_tsum (norm_spinImageTail_le ha hy) (summable_norm_spinImageTail ha hy) hs
    _ = _ := by simp only [div_eq_mul_inv, tsum_mul_left, one_mul]

theorem summable_spinImageKernel_int {a y : ℝ} (ha : 2 ≤ a) (hy : 0 < y) :
    Summable (fun n : ℤ => spinImageKernel a y n) := by
  have hs := (hasSum_ite_eq (0 : ℤ) (spinImageKernel a y 0)).summable.add
    (summable_norm_spinImageTail ha hy).of_norm
  convert hs using 1
  funext n
  by_cases hn : n = 0 <;> simp [spinImageTail, hn]

theorem tsum_spinImageKernel_eq_central_add_tail {a y : ℝ} (ha : 2 ≤ a) (hy : 0 < y) :
    (∑' n : ℤ, spinImageKernel a y n) = spinImageKernel a y 0 +
      ∑' n : ℤ, spinImageTail a y n := by
  simpa only [spinImageTail, Int.cast_zero] using
    (summable_spinImageKernel_int ha hy).tsum_eq_add_tsum_ite (0 : ℤ)

theorem spinImageKernel_isBigO {a y : ℝ} (ha : 2 ≤ a) (hy : 0 < y) :
    Asymptotics.IsBigO (Filter.cocompact ℝ) (spinImageKernel a y)
      (fun t : ℝ => |t| ^ (-(2 : ℝ))) := by
  refine Asymptotics.IsBigO.of_bound (spinImageBoundConstant a y) ?_
  filter_upwards [(isCompact_Icc (a := (-1 : ℝ)) (b := 1)).compl_mem_cocompact] with t ht
  have ht1 : 1 ≤ |t| := by
    by_contra h
    have habs : |t| < 1 := lt_of_not_ge h
    exact ht ⟨by linarith [(abs_lt.mp habs).1], (abs_lt.mp habs).2.le⟩
  have hpow : |t| ^ (-(2 : ℝ)) = 1 / t ^ 2 := by
    rw [Real.rpow_neg (abs_nonneg t), Real.rpow_two, sq_abs, one_div]
  rw [hpow, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ 1 / t ^ 2)]
  simpa only [mul_one_div] using norm_spinImageKernel_le ha hy ht1

theorem spinImageBoundConstant_normalized (a : ℝ) {y : ℝ} (hy : 0 < y) :
    spinImageBoundConstant a y * Real.exp (-(2 * Real.pi * a / y)) =
      (8 * Real.pi * Real.sqrt y * (a * y + 1) * Real.exp (2 * Real.pi)) *
        Real.exp (-spinImageDecayRate y * a) := by
  unfold spinImageBoundConstant
  rw [mul_assoc, ← Real.exp_add]
  have he := spinImage_exponent_gap a hy
  rw [show 2 * Real.pi * (a * y / (1 + y ^ 2) + 1) + -(2 * Real.pi * a / y) =
    2 * Real.pi + -spinImageDecayRate y * a by linarith [he], Real.exp_add]
  ring

end BTZEntropy
