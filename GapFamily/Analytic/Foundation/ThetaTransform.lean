import GapFamily.Analytic.Foundation.LatticeTheta
import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# The determinant-one lattice theta transformation

Shifted one-dimensional Gaussian Poisson summation rewrites the actual theta
series as an absolutely convergent rectangular Gaussian with a symmetric
bilinear phase. Interchanging the coordinates proves theta inversion for
all positive times.
-/

noncomputable section

namespace GapFamily.Analytic

open Complex
open scoped Real

/-- Poisson summation for a real translate of a positive Gaussian. -/
theorem shifted_gaussian_poisson {a : ℝ} (ha : 0 < a) (u : ℝ) :
    (∑' n : ℤ, Complex.exp (-Real.pi * (a : ℂ) * ((n : ℂ) + (u : ℂ)) ^ 2)) =
      (1 / (a : ℂ) ^ (1 / 2 : ℂ)) *
        ∑' k : ℤ, Complex.exp (-Real.pi / (a : ℂ) * (k : ℂ) ^ 2 +
          2 * Real.pi * Complex.I * (u : ℂ) * (k : ℂ)) := by
  have haC : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha.ne'
  have hleft (n : ℤ) :
      Complex.exp (-Real.pi * (a : ℂ) * ((n : ℂ) + (u : ℂ)) ^ 2) =
      Complex.exp (-Real.pi * (a : ℂ) * (u : ℂ) ^ 2) *
        Complex.exp (-Real.pi * (a : ℂ) * (n : ℂ) ^ 2 +
          2 * Real.pi * (-(a : ℂ) * (u : ℂ)) * (n : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  have hright (n : ℤ) :
      Complex.exp (-Real.pi * (a : ℂ) * (u : ℂ) ^ 2) *
        Complex.exp (-Real.pi / (a : ℂ) *
          ((n : ℂ) + Complex.I * (-(a : ℂ) * (u : ℂ))) ^ 2) =
      Complex.exp (-Real.pi / (a : ℂ) * (n : ℂ) ^ 2 +
        2 * Real.pi * Complex.I * (u : ℂ) * (n : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    field_simp
    ring_nf
    simp [Complex.I_sq]
  simp_rw [hleft]
  rw [tsum_mul_left, Complex.tsum_exp_neg_quadratic (by simpa using ha)]
  rw [← mul_assoc, mul_comm (Complex.exp _), mul_assoc, ← tsum_mul_left]
  congr 1
  exact tsum_congr hright

/-- The real-square-root normalization of shifted Gaussian Poisson summation. -/
theorem shifted_gaussian_poisson_sqrt {a : ℝ} (ha : 0 < a) (u : ℝ) :
    (∑' n : ℤ, Complex.exp (-Real.pi * (a : ℂ) * ((n : ℂ) + (u : ℂ)) ^ 2)) =
      ((1 / Real.sqrt a : ℝ) : ℂ) *
        ∑' k : ℤ, Complex.exp (-Real.pi / (a : ℂ) * (k : ℂ) ^ 2 +
          2 * Real.pi * Complex.I * (u : ℂ) * (k : ℂ)) := by
  rw [shifted_gaussian_poisson ha]
  congr 1
  rw [Real.sqrt_eq_rpow, Complex.ofReal_div, Complex.ofReal_one,
    Complex.ofReal_cpow ha.le]
  norm_num

/-- The two-coordinate lattice sum as an iterated sum, with absolute convergence. -/
theorem tsum_finTwo_eq_tsum_tsum {f : (Fin 2 → ℤ) → ℂ} (hf : Summable f) :
    (∑' v, f v) = ∑' m : ℤ, ∑' n : ℤ, f ![m, n] := by
  have hp : Summable (fun p : ℤ × ℤ => f ![p.1, p.2]) :=
    (finTwoArrowEquiv ℤ).symm.summable_iff.mpr hf
  calc
    (∑' v, f v) = ∑' p : ℤ × ℤ, f ![p.1, p.2] :=
      ((finTwoArrowEquiv ℤ).symm.tsum_eq f).symm
    _ = _ := hp.tsum_prod

/-- The completed-square expression of the lattice quadratic form. -/
theorem latticeEnergy_finTwo (z : UpperHalfPlane) (m n : ℤ) :
    latticeEnergy z ![m, n] =
      z.im * (m : ℝ) ^ 2 + ((n : ℝ) + z.re * (m : ℝ)) ^ 2 / z.im := by
  simp only [latticeEnergy, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, Complex.normSq_apply, Complex.add_re, Complex.mul_re,
    Complex.intCast_re, Complex.intCast_im, zero_mul, sub_zero, add_zero,
    Complex.add_im, Complex.mul_im, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
  field_simp
  ring

/-- The rectangular Gaussian with a symmetric bilinear unit-modulus phase. -/
def twistedGaussian (a b x : ℝ) (m n : ℤ) : ℂ :=
  Complex.exp (-Real.pi * (a : ℂ) * (m : ℂ) ^ 2 -
    Real.pi * (b : ℂ) * (n : ℂ) ^ 2 +
      2 * Real.pi * Complex.I * (x : ℂ) * (m : ℂ) * (n : ℂ))

lemma norm_twistedGaussian (a b x : ℝ) (m n : ℤ) :
    ‖twistedGaussian a b x m n‖ =
      Real.exp (-Real.pi * a * (m : ℝ)^2) *
        Real.exp (-Real.pi * b * (n : ℝ)^2) := by
  rw [twistedGaussian, Complex.norm_exp, ← Real.exp_add]
  congr 1
  simp [Complex.mul_re, Complex.mul_im, pow_two, sub_eq_add_neg]

lemma summable_twistedGaussian {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (x : ℝ) :
    Summable (fun p : ℤ × ℤ => twistedGaussian a b x p.1 p.2) := by
  have hga : Summable (fun n : ℤ => Real.exp (-Real.pi * a * (n : ℝ)^2)) := by
    simpa [mul_assoc] using summable_pow_mul_jacobiTheta₂_term_bound 0 ha 0
  have hgb : Summable (fun n : ℤ => Real.exp (-Real.pi * b * (n : ℝ)^2)) := by
    simpa [mul_assoc] using summable_pow_mul_jacobiTheta₂_term_bound 0 hb 0
  apply summable_norm_iff.mp
  simpa only [norm_twistedGaussian] using
    hga.mul_of_nonneg hgb (fun _ => (Real.exp_pos _).le) (fun _ => (Real.exp_pos _).le)

lemma twistedGaussian_swap (a b x : ℝ) (m n : ℤ) :
    twistedGaussian a b x m n = twistedGaussian b a x n m := by
  unfold twistedGaussian
  congr 1
  ring

lemma tsum_twistedGaussian_swap {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (x : ℝ) :
    (∑' m : ℤ, ∑' n : ℤ, twistedGaussian a b x m n) =
      ∑' m : ℤ, ∑' n : ℤ, twistedGaussian b a x m n := by
  rw [← (summable_twistedGaussian ha hb x).tsum_comm]
  apply tsum_congr
  intro n
  apply tsum_congr
  intro m
  exact twistedGaussian_swap a b x m n

/-- The lattice theta function written in real coordinates and summed by rows. -/
def coordinateTheta (x y t : ℝ) : ℂ :=
  ∑' m : ℤ, ∑' n : ℤ, Complex.exp
    (-Real.pi * ((t * y : ℝ) : ℂ) * (m : ℂ)^2 -
      Real.pi * ((t / y : ℝ) : ℂ) * ((n : ℂ) + (x : ℂ) * (m : ℂ))^2)

lemma coordinateTheta_poisson (x : ℝ) {y t : ℝ} (hy : 0 < y) (ht : 0 < t) :
    coordinateTheta x y t = ((1 / Real.sqrt (t / y) : ℝ) : ℂ) *
      ∑' m : ℤ, ∑' n : ℤ, twistedGaussian (t * y) (y / t) x m n := by
  unfold coordinateTheta
  have htC : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  have hyC : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy.ne'
  have hrow (m : ℤ) :
      (∑' n : ℤ, Complex.exp
        (-Real.pi * ((t * y : ℝ) : ℂ) * (m : ℂ)^2 -
          Real.pi * ((t / y : ℝ) : ℂ) * ((n : ℂ) + (x : ℂ) * (m : ℂ))^2)) =
      ((1 / Real.sqrt (t / y) : ℝ) : ℂ) *
        ∑' n : ℤ, twistedGaussian (t * y) (y / t) x m n := by
    simp_rw [sub_eq_add_neg, Complex.exp_add, tsum_mul_left]
    have hp := shifted_gaussian_poisson_sqrt (div_pos ht hy) (x * (m : ℝ))
    push_cast at hp
    simp_rw [neg_mul] at hp
    push_cast
    rw [hp]
    rw [← mul_assoc, mul_comm (Complex.exp _), mul_assoc, ← tsum_mul_left]
    congr 1
    apply tsum_congr
    intro n
    rw [← Complex.exp_add, twistedGaussian]
    congr 1
    push_cast
    field_simp
    ring
  simp_rw [hrow]
  rw [tsum_mul_left]

lemma coordinateTheta_functional_equation (x : ℝ) {y t : ℝ}
    (hy : 0 < y) (ht : 0 < t) :
    coordinateTheta x y (1 / t) = (t : ℂ) * coordinateTheta x y t := by
  rw [coordinateTheta_poisson x hy (one_div_pos.mpr ht), coordinateTheta_poisson x hy ht]
  have h1 : (1 / t) * y = y / t := by ring
  have h2 : y / (1 / t) = t * y := by field_simp
  rw [h1, h2, tsum_twistedGaussian_swap (div_pos hy ht) (mul_pos ht hy)]
  rw [← mul_assoc]
  congr 1
  have hs : 1 / Real.sqrt (1 / t / y) = t * (1 / Real.sqrt (t / y)) := by
    rw [Real.sqrt_div (one_div_nonneg.mpr ht.le), Real.sqrt_div ht.le,
      Real.sqrt_div (by norm_num : (0:ℝ) ≤ 1), Real.sqrt_one]
    have hyt : Real.sqrt y ≠ 0 := (Real.sqrt_pos.mpr hy).ne'
    have htt : Real.sqrt t ≠ 0 := (Real.sqrt_pos.mpr ht).ne'
    field_simp
    nlinarith [Real.sq_sqrt ht.le]
  exact_mod_cast hs

/-- The positive-time actual lattice theta series in coordinates. -/
lemma latticeTheta_eq_coordinateTheta (z : UpperHalfPlane) {t : ℝ} (ht : 0 < t) :
    (latticeTheta z t : ℂ) = coordinateTheta z.re z.im t := by
  unfold latticeTheta
  rw [Complex.ofReal_tsum,
    tsum_finTwo_eq_tsum_tsum (Complex.summable_ofReal.mpr (summable_latticeThetaTerm z ht))]
  unfold coordinateTheta
  apply tsum_congr
  intro m
  apply tsum_congr
  intro n
  rw [latticeThetaTerm, latticeEnergy_finTwo, Complex.ofReal_exp]
  congr 1
  push_cast
  ring

/-- The determinant-one rank-two theta transformation, proved by shifted Poisson summation. -/
theorem latticeTheta_functional_equation (z : UpperHalfPlane) {t : ℝ} (ht : 0 < t) :
    latticeTheta z (1 / t) = t * latticeTheta z t := by
  apply Complex.ofReal_injective
  rw [Complex.ofReal_mul, latticeTheta_eq_coordinateTheta z (one_div_pos.mpr ht),
    latticeTheta_eq_coordinateTheta z ht]
  exact coordinateTheta_functional_equation z.re z.im_pos ht

end GapFamily.Analytic
