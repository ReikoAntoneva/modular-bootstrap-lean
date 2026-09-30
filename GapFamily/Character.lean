import GapFamily.Contract
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Tactic.Ring

/-!
# Absolute convergence of the prescribed character expansion

Thermal summability implies summability of the norms of the complex character
terms at every upper half-plane point. Thus the totalized `tsum` in the public
definition denotes the convergent character series on every admissible spectrum.
-/

noncomputable section

open scoped UpperHalfPlane

namespace GapFamily

theorem norm_qPower (r : ℝ) (τ : ℍ) :
    ‖qPower r τ‖ = Real.exp (-2 * Real.pi * r * τ.im) := by
  rw [qPower, Complex.norm_exp]
  congr 1
  simp [Complex.mul_re, Complex.mul_im]

theorem norm_primaryCharacter (c h : ℝ) (τ : ℍ) :
    ‖primaryCharacter c h τ‖ =
      Real.exp (-2 * Real.pi * (h - shift c / 2) * τ.im) /
        ‖ModularForm.eta τ‖ := by
  rw [primaryCharacter, norm_div, norm_qPower]

/-- The norm of a full left-right primary term has the common eta factor. -/
theorem norm_primary_term (c : ℝ) (p : ℝ × ℝ) (d : ℕ) (τ : ℍ) :
    ‖(d : ℂ) * primaryCharacter c p.1 τ * star (primaryCharacter c p.2 τ)‖ =
      ((d : ℝ) * Real.exp (-2 * Real.pi * τ.im * dimension p)) *
        (Real.exp (2 * Real.pi * τ.im * shift c) / ‖ModularForm.eta τ‖ ^ 2) := by
  rw [norm_mul, norm_mul, norm_star, norm_natCast, norm_primaryCharacter,
    norm_primaryCharacter]
  have he : Real.exp (-2 * Real.pi * (p.1 - shift c / 2) * τ.im) *
      Real.exp (-2 * Real.pi * (p.2 - shift c / 2) * τ.im) =
      Real.exp (-2 * Real.pi * τ.im * dimension p) *
        Real.exp (2 * Real.pi * τ.im * shift c) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    dsimp [dimension]
    ring
  calc
    _ = (d : ℝ) *
        (Real.exp (-2 * Real.pi * (p.1 - shift c / 2) * τ.im) *
         Real.exp (-2 * Real.pi * (p.2 - shift c / 2) * τ.im)) /
          ‖ModularForm.eta τ‖ ^ 2 := by ring
    _ = _ := by rw [he]; ring

theorem TorusAdmissible.character_norm_summable {c : ℝ} {s : Spectrum}
    (h : TorusAdmissible c s) (τ : ℍ) :
    Summable (fun p : s.support =>
      ‖(s.multiplicity p : ℂ) * primaryCharacter c p.val.1 τ *
        star (primaryCharacter c p.val.2 τ)‖) := by
  simp_rw [norm_primary_term]
  exact (h.thermal_summable τ.im τ.im_pos).mul_right _

theorem TorusAdmissible.character_summable {c : ℝ} {s : Spectrum}
    (h : TorusAdmissible c s) (τ : ℍ) :
    Summable (fun p : s.support =>
      (s.multiplicity p : ℂ) * primaryCharacter c p.val.1 τ *
        star (primaryCharacter c p.val.2 τ)) :=
  (h.character_norm_summable τ).of_norm

/-- The Fourier--Laplace term in energy and spin coordinates. -/
def primaryNumerator (c : ℝ) (p : ℝ × ℝ) (τ : ℍ) : ℂ :=
  Complex.exp ((-2 * Real.pi * τ.im * energy c p : ℝ) +
    (2 * Real.pi * spin p * τ.re : ℝ) * Complex.I)

theorem qPower_mul_star (r s : ℝ) (τ : ℍ) :
    qPower r τ * star (qPower s τ) =
      Complex.exp ((-2 * Real.pi * (r + s) * τ.im : ℝ) +
        (2 * Real.pi * (r - s) * τ.re : ℝ) * Complex.I) := by
  simp only [qPower, Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring

/-- There is no extra energy-shift exponential in the nonvacuum numerator. -/
theorem primaryCharacter_product (c : ℝ) (p : ℝ × ℝ) (τ : ℍ) :
    primaryCharacter c p.1 τ * star (primaryCharacter c p.2 τ) =
      primaryNumerator c p τ / (‖ModularForm.eta τ‖ : ℂ) ^ 2 := by
  simp only [primaryCharacter, star_div₀, div_mul_div_comm, Complex.star_def,
    Complex.mul_conj']
  rw [← Complex.star_def, qPower_mul_star]
  congr 2
  dsimp [primaryNumerator, energy, dimension, spin]
  push_cast
  ring

/-- The single prescribed vacuum contribution to the numerator. -/
def vacuumNumerator (c : ℝ) (τ : ℍ) : ℂ :=
  (Real.exp (2 * Real.pi * τ.im * shift c) : ℂ) *
    (‖1 - qPower 1 τ‖ : ℂ) ^ 2

theorem vacuumCharacter_product (c : ℝ) (τ : ℍ) :
    vacuumCharacter c τ * star (vacuumCharacter c τ) =
      vacuumNumerator c τ / (‖ModularForm.eta τ‖ : ℂ) ^ 2 := by
  have hq : qPower (-shift c / 2) τ * star (qPower (-shift c / 2) τ) =
      (Real.exp (2 * Real.pi * τ.im * shift c) : ℂ) := by
    rw [qPower_mul_star, Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  simp only [vacuumCharacter, star_div₀, star_mul, div_mul_div_comm]
  have hprod (x y : ℂ) : x * y * (star y * star x) =
      (x * star x) * (y * star y) := by ring
  rw [hprod, hq]
  simp only [vacuumNumerator, Complex.star_def, Complex.mul_conj']

/-- The character partition function equals its energy-spin numerator quotient. -/
theorem partitionFunction_eq_numerator (c : ℝ) (s : Spectrum) (τ : ℍ) :
    partitionFunction c s τ =
      (vacuumNumerator c τ +
        ∑' p : s.support, (s.multiplicity p : ℂ) * primaryNumerator c p τ) /
        (‖ModularForm.eta τ‖ : ℂ) ^ 2 := by
  unfold partitionFunction
  rw [vacuumCharacter_product]
  simp_rw [mul_assoc, primaryCharacter_product, ← mul_div_assoc]
  rw [tsum_div_const, ← add_div]

theorem norm_primaryNumerator (c : ℝ) (p : ℝ × ℝ) (τ : ℍ) :
    ‖primaryNumerator c p τ‖ = Real.exp (-2 * Real.pi * τ.im * energy c p) := by
  rw [primaryNumerator, Complex.norm_exp]
  simp

theorem TorusAdmissible.numerator_norm_summable {c : ℝ} {s : Spectrum}
    (h : TorusAdmissible c s) (τ : ℍ) :
    Summable (fun p : s.support => ‖(s.multiplicity p : ℂ) * primaryNumerator c p τ‖) := by
  have he (p : ℝ × ℝ) :
      Real.exp (-2 * Real.pi * τ.im * energy c p) =
        Real.exp (-2 * Real.pi * τ.im * dimension p) *
          Real.exp (2 * Real.pi * τ.im * shift c) := by
    rw [← Real.exp_add]
    congr 1
    dsimp [energy]
    ring
  simp_rw [norm_mul, norm_natCast, norm_primaryNumerator, he, ← mul_assoc]
  exact (h.thermal_summable τ.im τ.im_pos).mul_right _

end GapFamily
