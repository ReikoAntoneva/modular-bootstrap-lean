import GapFamily.Analytic.Transform.CosRootHalfFourier

/-! Exact physical normalization of the product of the two half-profile Fourier values. -/
noncomputable section
namespace GapFamily.Analytic.CosRootLaplace

/-- Reflection conjugates the Fourier rate. -/
theorem halfFourierRate_neg (a t : ℝ) :
    halfFourierRate a (-t) = (starRingEnd ℂ) (halfFourierRate a t) := by
  simp [halfFourierRate, map_ofNat]

private theorem conj_neg_half_mul {z : ℂ} (hz : 0 < z.re) :
    ((starRingEnd ℂ) z) ^ (-(1 / 2 : ℂ)) * z ^ (-(1 / 2 : ℂ)) =
      ((‖z‖⁻¹ : ℝ) : ℂ) := by
  have harg : z.arg ≠ Real.pi := by
    intro h
    exact (not_lt_of_ge hz.le) (Complex.arg_eq_pi_iff.mp h).1
  rw [Complex.conj_cpow z (-(1 / 2 : ℂ)) harg]
  norm_num only [map_neg, map_div₀, map_one, map_ofNat]
  rw [Complex.conj_mul']
  have hn : ‖z ^ (-(1 / 2 : ℂ))‖ = ‖z‖ ^ (-(1 / 2 : ℝ)) := by
    simpa only [Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_one,
      Complex.ofReal_ofNat] using Complex.norm_cpow_real z (-(1 / 2 : ℝ))
  rw [hn, ← Complex.ofReal_pow, Real.rpow_neg (norm_nonneg z),
    ← Real.sqrt_eq_rpow, inv_pow, Real.sq_sqrt (norm_nonneg z)]

/-- The norm of the physical Fourier rate retains its exact factor of two pi. -/
theorem norm_halfFourierRate_physical {y : ℝ} (hy : 0 < y) (t : ℝ) :
    ‖halfFourierRate (2 * Real.pi * y) t‖ =
      2 * Real.pi * Real.sqrt (t ^ 2 + y ^ 2) := by
  apply (sq_eq_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [← Complex.normSq_eq_norm_sq]
  simp only [halfFourierRate, Complex.normSq_apply, Complex.add_re,
    Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.ofReal_im,
    Complex.I_im, mul_zero, sub_zero, add_zero, Complex.add_im,
    Complex.mul_im, mul_one, zero_add]
  rw [mul_pow, Real.sq_sqrt (by positivity : 0 ≤ t ^ 2 + y ^ 2)]
  ring

/-- The two principal inverse square roots have their exact positive real product. -/
theorem halfFourierRate_physical_neg_half_product {y : ℝ} (hy : 0 < y) (t : ℝ) :
    halfFourierRate (2 * Real.pi * y) (-t) ^ (-(1 / 2 : ℂ)) *
      halfFourierRate (2 * Real.pi * y) t ^ (-(1 / 2 : ℂ)) =
        ((1 / (2 * Real.pi * Real.sqrt (t ^ 2 + y ^ 2)) : ℝ) : ℂ) := by
  rw [halfFourierRate_neg, conj_neg_half_mul]
  · rw [norm_halfFourierRate_physical hy, one_div]
  · simpa [halfFourierRate] using (show 0 < 2 * Real.pi * y by positivity)

/-- The physical energy and spin parameters give the exact combined complex exponent. -/
theorem halfFourierRate_physical_exponent {c y : ℝ} (hc : 0 < c) (hy : 0 < y)
    (E J t : ℝ) :
    -((8 * Real.pi ^ 2 * (E + J) / c ^ 2 : ℝ) : ℂ) /
        (4 * halfFourierRate (2 * Real.pi * y) (-t)) +
      -((8 * Real.pi ^ 2 * (E - J) / c ^ 2 : ℝ) : ℂ) /
        (4 * halfFourierRate (2 * Real.pi * y) t) =
      -2 * (Real.pi : ℂ) * (((E * y : ℝ) : ℂ) + ((J * t : ℝ) : ℂ) * Complex.I) /
        ((c ^ 2 * (t ^ 2 + y ^ 2) : ℝ) : ℂ) := by
  have hcC : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc.ne'
  have hqC : (t : ℂ) ^ 2 + (y : ℂ) ^ 2 ≠ 0 := by
    exact_mod_cast (show t ^ 2 + y ^ 2 ≠ 0 by positivity)
  have hpm : (y : ℂ) - (t : ℂ) * Complex.I ≠ 0 := by
    intro h
    have hre : y = 0 := by simpa using congrArg Complex.re h
    exact hy.ne' hre
  have hpp : (y : ℂ) + (t : ℂ) * Complex.I ≠ 0 := by
    intro h
    have hre : y = 0 := by simpa using congrArg Complex.re h
    exact hy.ne' hre
  have hi3 : Complex.I ^ 3 = -Complex.I := by
    rw [pow_succ, Complex.I_sq]
    ring
  have hr (u : ℝ) : halfFourierRate (2 * Real.pi * y) u ≠ 0 := by
    intro h
    have hre : 2 * Real.pi * y = 0 := by
      simpa [halfFourierRate] using congrArg Complex.re h
    exact (show 0 < 2 * Real.pi * y by positivity).ne' hre
  have hrm := hr (-t)
  have hrp := hr t
  dsimp [halfFourierRate] at hrm hrp ⊢
  push_cast at hrm hrp ⊢
  field_simp [hcC, hqC, hrm, hrp, hpm, hpp, Complex.ofReal_ne_zero.mpr Real.pi_ne_zero]
  ring_nf
  field_simp [hpm, hpp]
  ring_nf
  simp only [Complex.I_sq, hi3]
  ring

/-- The product of the two literal half-profile Fourier values has its full physical normalization. -/
theorem halfFourierValue_physical_product {c y : ℝ} (hc : 0 < c) (hy : 0 < y)
    (E J t : ℝ) :
    halfFourierValue (2 * Real.pi * y)
        ((8 * Real.pi ^ 2 * (E + J) / c ^ 2 : ℝ) : ℂ) (-t) *
      halfFourierValue (2 * Real.pi * y)
        ((8 * Real.pi ^ 2 * (E - J) / c ^ 2 : ℝ) : ℂ) t =
      ((1 / (2 * Real.sqrt (t ^ 2 + y ^ 2)) : ℝ) : ℂ) *
        Complex.exp (-2 * (Real.pi : ℂ) *
          (((E * y : ℝ) : ℂ) + ((J * t : ℝ) : ℂ) * Complex.I) /
          ((c ^ 2 * (t ^ 2 + y ^ 2) : ℝ) : ℂ)) := by
  unfold halfFourierValue
  calc
    _ = (Real.sqrt Real.pi : ℂ) ^ 2 *
        (halfFourierRate (2 * Real.pi * y) (-t) ^ (-(1 / 2 : ℂ)) *
          halfFourierRate (2 * Real.pi * y) t ^ (-(1 / 2 : ℂ))) *
        (Complex.exp (-((8 * Real.pi ^ 2 * (E + J) / c ^ 2 : ℝ) : ℂ) /
          (4 * halfFourierRate (2 * Real.pi * y) (-t))) *
        Complex.exp (-((8 * Real.pi ^ 2 * (E - J) / c ^ 2 : ℝ) : ℂ) /
          (4 * halfFourierRate (2 * Real.pi * y) t))) := by ring
    _ = _ := by
      rw [halfFourierRate_physical_neg_half_product hy, ← Complex.exp_add,
        halfFourierRate_physical_exponent hc hy, ← Complex.ofReal_pow,
        Real.sq_sqrt Real.pi_pos.le, ← Complex.ofReal_mul]
      congr 1
      congr 1
      field_simp [Real.pi_ne_zero]

end GapFamily.Analytic.CosRootLaplace
