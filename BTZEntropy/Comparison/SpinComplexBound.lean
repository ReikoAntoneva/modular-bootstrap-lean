import BTZEntropy.Comparison.SpinComplexImage
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# A summable envelope for complex spin images

Both vacuum null factors supply inverse chiral denominators. Together with
the square root they yield a `|n|^(-3/2)` majorant, uniform along an entire
vertical contour. The phase keeps the strict noncentral exponential loss.
-/

noncomputable section

namespace BTZEntropy

def spinNullBound (x : ℝ) : ℝ := 2 * Real.pi * Real.exp (2 * Real.pi / x)

theorem norm_spinNull_le {x : ℝ} (hx : 0 < x) {w : ℂ} (hw : x ≤ w.re) :
    ‖1 - Complex.exp (-2 * (Real.pi : ℂ) / w)‖ ≤ spinNullBound x / ‖w‖ := by
  have hn : x ≤ ‖w‖ := hw.trans (Complex.re_le_norm w)
  have hwpos : 0 < ‖w‖ := hx.trans_le hn
  have hq : ‖-2 * (Real.pi : ℂ) / w‖ = 2 * Real.pi / ‖w‖ := by
    simp [Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  have hle : ‖-2 * (Real.pi : ℂ) / w‖ ≤ 2 * Real.pi / x := by
    rw [hq]
    exact div_le_div_of_nonneg_left (by positivity) hx hn
  have he : ‖Complex.exp (-2 * (Real.pi : ℂ) / w) - 1‖ ≤
      ‖-2 * (Real.pi : ℂ) / w‖ * Real.exp ‖-2 * (Real.pi : ℂ) / w‖ := by
    simpa using Complex.norm_exp_sub_sum_le_norm_mul_exp (-2 * (Real.pi : ℂ) / w) 1
  rw [norm_sub_rev]
  calc
    _ ≤ _ := he
    _ ≤ (2 * Real.pi / ‖w‖) * Real.exp (2 * Real.pi / x) := by
      rw [hq]
      rw [hq] at hle
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hle) (by positivity)
    _ = _ := by unfold spinNullBound; ring

private theorem spin_norm_sqrt (w : ℂ) : ‖Complex.sqrt w‖ = Real.sqrt ‖w‖ := by
  simpa only [Complex.sqrt, one_div, Real.sqrt_eq_rpow, Nat.cast_ofNat] using
    Complex.norm_cpow_inv_nat w 2

/-- Explicit bound retaining the actual denominator, before the lattice estimate. -/
theorem norm_complexSpinImage_le_denominator {a : ℝ} (ha : 0 ≤ a) {z : ℂ}
    (hz : 0 < z.re) {n : ℤ} (hn : n ≠ 0) :
    ‖complexSpinImage a z n‖ ≤
      (spinNullBound z.re ^ 2 /
        (Real.sqrt ‖z ^ 2 + (n : ℂ) ^ 2‖ * ‖z ^ 2 + (n : ℂ) ^ 2‖)) *
        (Real.exp (2 * Real.pi * a / z.re) * Real.exp (-(spinImageDecayRate z.re / 2) * a)) := by
  let p : ℂ := z + (n : ℂ) * Complex.I
  let m : ℂ := z - (n : ℂ) * Complex.I
  let D : ℂ := z ^ 2 + (n : ℂ) ^ 2
  have hp : z.re ≤ p.re := by simp [p]
  have hm : z.re ≤ m.re := by simp [m]
  have hnullp := norm_spinNull_le hz hp
  have hnullm := norm_spinNull_le hz hm
  have hf : p * m = D := by
    dsimp [p, m, D]
    calc
      _ = z ^ 2 - (n : ℂ) ^ 2 * Complex.I ^ 2 := by ring
      _ = _ := by rw [Complex.I_sq]; ring
  have hnormD : ‖p‖ * ‖m‖ = ‖D‖ := by rw [← norm_mul, hf]
  have hexp : ‖Complex.exp ((2 * (Real.pi : ℂ) * (a : ℂ)) * (z / D))‖ ≤
      Real.exp (2 * Real.pi * a / z.re) *
        Real.exp (-(spinImageDecayRate z.re / 2) * a) := by
    simpa [Complex.norm_exp, Complex.mul_re, D] using spinComplexPhase_exp_le ha hz hn
  have heq : (Real.pi : ℂ) * (a : ℂ) * (p⁻¹ + m⁻¹) =
      (2 * (Real.pi : ℂ) * (a : ℂ)) * (z / D) := by
    have h := spinComplexPhase_partialFraction z (n : ℝ) hz
    simp only [Complex.ofReal_intCast] at h
    dsimp [p, m, D]
    rw [h]
    ring
  rw [complexSpinImage_eq_reciprocal a hz n]
  change ‖(Complex.sqrt D)⁻¹ * Complex.exp ((Real.pi : ℂ) * (a : ℂ) * (p⁻¹ + m⁻¹)) *
    (1 - Complex.exp (-2 * (Real.pi : ℂ) / m)) *
    (1 - Complex.exp (-2 * (Real.pi : ℂ) / p))‖ ≤ _
  rw [heq, norm_mul, norm_mul, norm_mul, norm_inv, spin_norm_sqrt]
  calc
    _ ≤ ((Real.sqrt ‖D‖)⁻¹ *
        (Real.exp (2 * Real.pi * a / z.re) * Real.exp (-(spinImageDecayRate z.re / 2) * a)) *
          (spinNullBound z.re / ‖m‖)) * (spinNullBound z.re / ‖p‖) := by
      gcongr
      unfold spinNullBound
      positivity
    _ = _ := by
      change _ = spinNullBound z.re ^ 2 / (Real.sqrt ‖D‖ * ‖D‖) * _
      rw [← hnormD]
      ring

private theorem inv_sqrt_mul_eq_rpow {d : ℝ} (hd : 0 < d) :
    (Real.sqrt d * d)⁻¹ = d ^ (-(3 / 2 : ℝ)) := by
  have he : Real.sqrt d * d = d ^ (3 / 2 : ℝ) := by
    calc
      _ = d ^ (1 / 2 : ℝ) * d ^ (1 : ℝ) := by rw [Real.sqrt_eq_rpow, Real.rpow_one]
      _ = d ^ ((1 / 2 : ℝ) + 1) := (Real.rpow_add hd _ _).symm
      _ = _ := by norm_num
  rw [he, Real.rpow_neg hd.le]

/-- The lattice majorant is summable in `n` and uniform along every vertical line. -/
theorem norm_complexSpinImage_le_lattice {a : ℝ} (ha : 0 ≤ a) {z : ℂ}
    (hz : 0 < z.re) {n : ℤ} (hn : n ≠ 0) :
    ‖complexSpinImage a z n‖ ≤
      (spinNullBound z.re ^ 2 * z.re ^ (-(3 / 2 : ℝ))) *
        |(n : ℝ)| ^ (-(3 / 2 : ℝ)) *
        (Real.exp (2 * Real.pi * a / z.re) * Real.exp (-(spinImageDecayRate z.re / 2) * a)) := by
  have hnpos : 0 < |(n : ℝ)| := abs_pos.mpr (by exact_mod_cast hn)
  have hDpos : 0 < ‖z ^ 2 + (n : ℂ) ^ 2‖ :=
    norm_pos_iff.mpr (spinComplexDenominator_ne_zero hz n)
  have hD := norm_spinComplexDenominator_ge hz.le (n : ℝ)
  simp only [Complex.ofReal_intCast] at hD
  have hr := Real.rpow_le_rpow_of_nonpos (mul_pos hz hnpos) hD
    (by norm_num : -(3 / 2 : ℝ) ≤ 0)
  rw [Real.mul_rpow hz.le hnpos.le] at hr
  have h := norm_complexSpinImage_le_denominator ha hz hn
  rw [div_eq_mul_inv, inv_sqrt_mul_eq_rpow hDpos] at h
  calc
    _ ≤ _ := h
    _ ≤ spinNullBound z.re ^ 2 *
        (z.re ^ (-(3 / 2 : ℝ)) * |(n : ℝ)| ^ (-(3 / 2 : ℝ))) *
          (Real.exp (2 * Real.pi * a / z.re) * Real.exp (-(spinImageDecayRate z.re / 2) * a)) := by
      gcongr
    _ = _ := by ring

theorem spinNullBound_pos (x : ℝ) : 0 < spinNullBound x := by
  unfold spinNullBound
  positivity

theorem spinNullBound_antitone {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    spinNullBound y ≤ spinNullBound x := by
  unfold spinNullBound
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact Real.exp_le_exp.mpr (div_le_div_of_nonneg_left (by positivity) hx hxy)

/-- One fixed summable bound works on an entire closed right half-plane. -/
theorem norm_complexSpinImage_le_strip {a ε : ℝ} (ha : 0 ≤ a) (hε : 0 < ε)
    {z : ℂ} (hz : ε ≤ z.re) {n : ℤ} (hn : n ≠ 0) :
    ‖complexSpinImage a z n‖ ≤
      (spinNullBound ε ^ 2 * ε ^ (-(3 / 2 : ℝ)) * Real.exp (2 * Real.pi * a / ε)) *
        |(n : ℝ)| ^ (-(3 / 2 : ℝ)) := by
  have hx : 0 < z.re := hε.trans_le hz
  have hn0 : 0 ≤ |(n : ℝ)| ^ (-(3 / 2 : ℝ)) := Real.rpow_nonneg (abs_nonneg _) _
  have hnull : spinNullBound z.re ^ 2 ≤ spinNullBound ε ^ 2 :=
    pow_le_pow_left₀ (spinNullBound_pos _).le (spinNullBound_antitone hε hz) 2
  have hr : z.re ^ (-(3 / 2 : ℝ)) ≤ ε ^ (-(3 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hε hz (by norm_num)
  have he : Real.exp (2 * Real.pi * a / z.re) ≤ Real.exp (2 * Real.pi * a / ε) :=
    Real.exp_le_exp.mpr (div_le_div_of_nonneg_left (by positivity) hε hz)
  have hloss : Real.exp (-(spinImageDecayRate z.re / 2) * a) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    have hrate := spinImageDecayRate_pos hx
    exact mul_nonpos_of_nonpos_of_nonneg (by linarith) ha
  calc
    _ ≤ _ := norm_complexSpinImage_le_lattice ha hx hn
    _ ≤ (spinNullBound ε ^ 2 * ε ^ (-(3 / 2 : ℝ))) *
        |(n : ℝ)| ^ (-(3 / 2 : ℝ)) * (Real.exp (2 * Real.pi * a / ε) * 1) := by
      gcongr
    _ = _ := by ring

/-- A vertical-strip envelope with one strict exponential loss for all its points. -/
theorem norm_complexSpinImage_le_uniform {a ε Y : ℝ} (ha : 0 ≤ a) (hε : 0 < ε)
    {z : ℂ} (hlo : ε ≤ z.re) (hhi : z.re ≤ Y) {n : ℤ} (hn : n ≠ 0) :
    ‖complexSpinImage a z n‖ ≤
      (spinNullBound ε ^ 2 * ε ^ (-(3 / 2 : ℝ))) *
        |(n : ℝ)| ^ (-(3 / 2 : ℝ)) *
        (Real.exp (2 * Real.pi * a / z.re) * Real.exp (-(spinImageDecayRate Y / 2) * a)) := by
  have hx : 0 < z.re := hε.trans_le hlo
  have hnull : spinNullBound z.re ^ 2 ≤ spinNullBound ε ^ 2 :=
    pow_le_pow_left₀ (spinNullBound_pos _).le (spinNullBound_antitone hε hlo) 2
  have hr : z.re ^ (-(3 / 2 : ℝ)) ≤ ε ^ (-(3 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hε hlo (by norm_num)
  have hrate := spinImageDecayRate_antitone hx hhi
  have hloss : Real.exp (-(spinImageDecayRate z.re / 2) * a) ≤
      Real.exp (-(spinImageDecayRate Y / 2) * a) := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_right (by linarith) ha
  calc
    _ ≤ _ := norm_complexSpinImage_le_lattice ha hx hn
    _ ≤ _ := by gcongr

end BTZEntropy
