import BTZEntropy.Comparison.UniformPolynomialApproximation
import BTZEntropy.Comparison.CellTestGeometry

/-! Uniform rapid polynomial approximation of the actual descendant cell tests. -/

noncomputable section

open Set Polynomial
open scoped ContDiff
open GapFamily.Construction

namespace BTZEntropy.Comparison

/-- The approximation constant depends only on the kernel and requested order.
It is independent of the spin, charge, cell opening, descendant level, translated
observation energy, and polynomial degree. -/
theorem exists_uniform_cellTest_polynomial_approximation (φ : SmoothKernel) (P : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (r L V t : ℝ), r ≤ L → L ≤ V → V - L ≤ 1 →
      ∀ k : ℕ, ∃ p : ℝ[X], p.degree ≤ k ∧ ∀ z ∈ Icc (0 : ℝ) 1,
        |φ (t + normalizedCellEnergy r L V z) - p.eval z| ≤ C / ((k : ℝ) + 1) ^ P := by
  obtain ⟨C, hC, hbound⟩ := exists_uniform_cellTest_derivative_bound_up_to φ (P + 2)
  refine ⟨polynomialApproximationConstant P C,
    polynomialApproximationConstant_nonneg P hC, ?_⟩
  intro r L V t hr hLV hwidth k
  have hs : ContDiff ℝ ∞ (fun x => φ (t + normalizedCellEnergy r L V x)) := by
    apply φ.smooth.comp
    unfold normalizedCellEnergy energyCoord
    fun_prop
  exact polynomial_approximation_of_derivative_bound hs P
    (fun i hi z hz => by
      simpa only [Real.norm_eq_abs] using hbound i hi r L V t z hr hLV hwidth hz) k

end BTZEntropy.Comparison
