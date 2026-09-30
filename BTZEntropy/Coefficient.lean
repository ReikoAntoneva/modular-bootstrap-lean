import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Algebra.Polynomial.Coeff

/-!
# Coefficient of the perturbative BTZ saddle

The transform, determinant, saddle, constant term and explicit first correction
follow Section 6.1--6.2 of the fixed paper source. Higher coefficients are given
by finite Taylor expansion of that phase and amplitude, Gaussian moments along
the imaginary saddle direction, and the formal logarithm. This specifies a
coefficient at every order without any free coefficient sequence.

The analytic modules prove convergence and smoothness of the determinant and
amplitude, then identify this finite algorithm with the all-order asymptotic
expansion of the BTZ inverse Laplace integral. The phase and amplitude are
those in Section 6 and Appendix F of the paper.
-/

noncomputable section

open MeasureTheory Polynomial
open scoped BigOperators

namespace BTZEntropy

/-- The smoothing kernel transform on the positive real inverse-temperature axis. -/
def kernelTransform (φ : ℝ → ℝ) (β : ℝ) : ℝ :=
  ∫ u : ℝ, φ u * Real.exp (β * u)

/-- The boundary-graviton product starts at level two because of the vacuum null state.
Its analytic use requires a separate multipliability proof for positive `u`. -/
def boundaryGravitonFactor (u : ℝ) : ℝ :=
  ∏' m : ℕ, ((1 - Real.exp (-((m + 2 : ℕ) : ℝ) * u)) ^ 2)⁻¹

/-- The kernel and one-loop determinant in the inverse Laplace integrand. -/
def amplitude (φ : ℝ → ℝ) (β : ℝ) : ℝ :=
  kernelTransform φ β * boundaryGravitonFactor (4 * Real.pi ^ 2 / β)

def saddleRadius (energyRatio : ℝ) : ℝ := Real.sqrt (12 * energyRatio)

def saddleBeta (energyRatio : ℝ) : ℝ := 2 * Real.pi / saddleRadius energyRatio

def dualSaddleBeta (energyRatio : ℝ) : ℝ := 4 * Real.pi ^ 2 / saddleBeta energyRatio

def phaseConstant : ℝ := Real.pi ^ 2 / 3

/-- The phase before multiplication by the central charge. -/
def saddlePhase (energyRatio β : ℝ) : ℝ := energyRatio * β + phaseConstant / β

/-- The leading entropy at cylinder energy exactly `energyRatio * c`. -/
def leadingAction (energyRatio c : ℝ) : ℝ := Real.pi * c * saddleRadius energyRatio / 3

/-- The Gaussian Hessian `f''(β*)`, with `f(β) = energyRatio β + b / β`. -/
def saddleHessian (energyRatio : ℝ) : ℝ := 2 * phaseConstant / saddleBeta energyRatio ^ 3

/-- The constant entropy coefficient displayed in the paper. -/
def constantCoefficient (φ : ℝ → ℝ) (energyRatio : ℝ) : ℝ :=
  (1 / 2 : ℝ) * Real.log 6 - (3 / 2 : ℝ) * Real.log (saddleRadius energyRatio) +
    Real.log (kernelTransform φ (saddleBeta energyRatio)) +
    Real.log (boundaryGravitonFactor (dualSaddleBeta energyRatio))

/-- The explicit first entropy correction displayed in Section 6.2.
The relation to `entropyCoefficient φ energyRatio 1` is a separate algebraic lemma. -/
def firstEntropyCoefficient (φ : ℝ → ℝ) (energyRatio : ℝ) : ℝ :=
  -(saddleBeta energyRatio / (16 * phaseConstant)) *
    (3 + 12 * saddleBeta energyRatio * deriv (amplitude φ) (saddleBeta energyRatio) /
      amplitude φ (saddleBeta energyRatio) +
      4 * saddleBeta energyRatio ^ 2 * iteratedDeriv 2 (amplitude φ) (saddleBeta energyRatio) /
        amplitude φ (saddleBeta energyRatio))

/-- A normalized real Gaussian moment with the factor `i^n` from the imaginary
saddle direction included. Odd moments vanish. -/
def imaginaryGaussianMoment (h : ℝ) (n : ℕ) : ℝ :=
  if Even n then
    (-1 : ℝ) ^ (n / 2) * (n.factorial : ℝ) /
      (2 ^ (n / 2) * ((n / 2).factorial : ℝ) * h ^ (n / 2))
  else 0

/-- Apply the normalized Gaussian moment functional to a polynomial. -/
def gaussianEvaluation (h : ℝ) (p : Polynomial ℝ) : ℝ :=
  p.sum fun n a => a * imaginaryGaussianMoment h n

/-- The phase terms beyond the quadratic term, through formal order `N` in
`ε = c^(-1/2)`. The inner polynomial variable is the saddle displacement.
The coefficient at order `j` is `(-1)^(j+2) b x^(j+2) / β*^(j+3)`. -/
def phaseDeviation (energyRatio : ℝ) (N : ℕ) : Polynomial (Polynomial ℝ) :=
  ∑ j ∈ Finset.range N,
    monomial (j + 1)
      (monomial (j + 3)
        ((-1 : ℝ) ^ (j + 3) * phaseConstant / saddleBeta energyRatio ^ (j + 4)))

/-- The amplitude Taylor polynomial, with the same outer and inner variables. -/
def amplitudeTaylor (φ : ℝ → ℝ) (energyRatio : ℝ) (N : ℕ) :
    Polynomial (Polynomial ℝ) :=
  ∑ j ∈ Finset.range (N + 1),
    monomial j
      (monomial j (iteratedDeriv j (amplitude φ) (saddleBeta energyRatio) / (j.factorial : ℝ)))

/-- Only powers through `N` are needed because `phaseDeviation` has no constant term. -/
def phaseExponential (energyRatio : ℝ) (N : ℕ) : Polynomial (Polynomial ℝ) :=
  ∑ j ∈ Finset.range (N + 1),
    C (C ((j.factorial : ℝ)⁻¹)) * phaseDeviation energyRatio N ^ j

/-- A specified finite Taylor--Gaussian algorithm for the normalized count coefficient.
Proving that it is the asymptotic coefficient of the BTZ inverse transform is
not part of this definition. -/
def saddleCountCoefficient (φ : ℝ → ℝ) (energyRatio : ℝ) (m : ℕ) : ℝ :=
  gaussianEvaluation (saddleHessian energyRatio)
      ((amplitudeTaylor φ energyRatio (2 * m) * phaseExponential energyRatio (2 * m)).coeff (2 * m)) /
    amplitude φ (saddleBeta energyRatio)

/-- The nonconstant part of the normalized count series, truncated at order `N`. -/
def countCorrectionPolynomial (φ : ℝ → ℝ) (energyRatio : ℝ) (N : ℕ) : Polynomial ℝ :=
  ∑ j ∈ Finset.range N, monomial (j + 1) (saddleCountCoefficient φ energyRatio (j + 1))

/-- The coefficient of the formal logarithm, which is a finite polynomial calculation. -/
def logarithmicCoefficient (φ : ℝ → ℝ) (energyRatio : ℝ) (n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range n,
    ((-1 : ℝ) ^ j / (j + 1 : ℕ)) *
      (countCorrectionPolynomial φ energyRatio n ^ (j + 1)).coeff n

/-- The complete designated coefficient sequence: the paper's constant term,
followed by finite Taylor--Gaussian and logarithm coefficients. -/
def entropyCoefficient (φ : ℝ → ℝ) (energyRatio : ℝ) : ℕ → ℝ
  | 0 => constantCoefficient φ energyRatio
  | n + 1 => logarithmicCoefficient φ energyRatio (n + 1)

@[simp] theorem entropyCoefficient_zero (φ : ℝ → ℝ) (energyRatio : ℝ) :
    entropyCoefficient φ energyRatio 0 = constantCoefficient φ energyRatio := rfl

@[simp] theorem kernelTransform_zero (φ : ℝ → ℝ) :
    kernelTransform φ 0 = ∫ u : ℝ, φ u := by
  simp [kernelTransform]

theorem phaseConstant_pos : 0 < phaseConstant := by
  exact div_pos (sq_pos_of_pos Real.pi_pos) (by norm_num)

theorem saddleRadius_pos {energyRatio : ℝ} (h : 0 < energyRatio) :
    0 < saddleRadius energyRatio := by
  exact Real.sqrt_pos.2 (mul_pos (by norm_num) h)

theorem saddleBeta_pos {energyRatio : ℝ} (h : 0 < energyRatio) :
    0 < saddleBeta energyRatio := by
  exact div_pos (mul_pos (by norm_num) Real.pi_pos) (saddleRadius_pos h)

@[simp] theorem imaginaryGaussianMoment_zero (h : ℝ) :
    imaginaryGaussianMoment h 0 = 1 := by
  simp [imaginaryGaussianMoment]

@[simp] theorem gaussianEvaluation_monomial (h a : ℝ) (n : ℕ) :
    gaussianEvaluation h (monomial n a) = a * imaginaryGaussianMoment h n := by
  exact Polynomial.sum_monomial_index _ _ (by simp)

@[simp] theorem gaussianEvaluation_zero (h : ℝ) :
    gaussianEvaluation h 0 = 0 := by
  simp [gaussianEvaluation]

theorem gaussianEvaluation_add (h : ℝ) (p q : Polynomial ℝ) :
    gaussianEvaluation h (p + q) = gaussianEvaluation h p + gaussianEvaluation h q := by
  exact Polynomial.sum_add_index _ _ _ (by simp) (by intros; ring)

@[simp] theorem gaussianEvaluation_C (h a : ℝ) :
    gaussianEvaluation h (C a) = a := by
  simp [gaussianEvaluation, Polynomial.sum_C_index]

@[simp] theorem saddleCountCoefficient_zero (φ : ℝ → ℝ) (energyRatio : ℝ)
    (hA : amplitude φ (saddleBeta energyRatio) ≠ 0) :
    saddleCountCoefficient φ energyRatio 0 = 1 := by
  simp [saddleCountCoefficient, amplitudeTaylor, phaseExponential,
    phaseDeviation, iteratedDeriv_zero, hA]

theorem entropyCoefficient_one_eq_count (φ : ℝ → ℝ) (energyRatio : ℝ) :
    entropyCoefficient φ energyRatio 1 = saddleCountCoefficient φ energyRatio 1 := by
  simp [entropyCoefficient, logarithmicCoefficient, countCorrectionPolynomial]

/-- The formal logarithm reproduces the second-order relation stated in Section 6.2. -/
theorem entropyCoefficient_two_eq_count (φ : ℝ → ℝ) (energyRatio : ℝ) :
    entropyCoefficient φ energyRatio 2 = saddleCountCoefficient φ energyRatio 2 -
      saddleCountCoefficient φ energyRatio 1 ^ 2 / 2 := by
  norm_num [entropyCoefficient, logarithmicCoefficient, countCorrectionPolynomial,
    Finset.sum_range_succ, pow_two, mul_add, add_mul,
    Polynomial.monomial_mul_monomial, Polynomial.coeff_monomial]
  ring

theorem entropyCoefficient_one (φ : ℝ → ℝ) {energyRatio : ℝ}
    (h : 0 < energyRatio) (hA : amplitude φ (saddleBeta energyRatio) ≠ 0) :
    entropyCoefficient φ energyRatio 1 = firstEntropyCoefficient φ energyRatio := by
  rw [entropyCoefficient_one_eq_count]
  norm_num [saddleCountCoefficient, amplitudeTaylor, phaseExponential, phaseDeviation,
    Finset.sum_range_succ, pow_two, mul_add, add_mul,
    Polynomial.C_mul_monomial, Polynomial.monomial_mul_C,
    Polynomial.monomial_mul_monomial, Polynomial.coeff_monomial,
    gaussianEvaluation_add,
    iteratedDeriv_zero, iteratedDeriv_one, imaginaryGaussianMoment,
    firstEntropyCoefficient, saddleHessian, Nat.even_iff]
  field_simp [ne_of_gt (saddleBeta_pos h), ne_of_gt phaseConstant_pos, hA]
  ring

end BTZEntropy
