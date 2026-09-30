import GapFamily.Analytic.Poincare.PoincarePositiveCoset
import GapFamily.Analytic.Poincare.Fourier.PoincareFourierNonidentity
import GapFamily.Analytic.Poincare.Fourier.PoincareFourierUnfold

/-! Literal transport of the convergent nonidentity Fourier sum to its arithmetic indices. -/
noncomputable section
namespace GapFamily.Analytic.PoincareFourierRegroup
open Set MeasureTheory PoincareFourier PoincareFourierUnfold
open scoped Topology MatrixGroups

/-- The actual inverse quotient parametrization preserves the literal Fourier integrand. -/
theorem fourierTerm_nonidentityResidueEquiv_symm (j J : ℤ) (s : ℂ) (y : ℝ)
    (hy : 0 < y) (n : ℕ) (u : (ZMod (n + 1))ˣ) (k : ℤ) (x : ℝ) :
    fourierTerm j J s y hy
      (nonidentityResidueEquiv.symm ⟨n, (u, k)⟩).val x =
        primitiveFourierTerm j J s y hy (residueRow n u k) x := by
  rw [nonidentityResidueEquiv_symm_apply_val]
  rfl

/-- Absolute integrated-norm convergence is transported from the original cusp quotient. -/
theorem summable_integral_norm_indexed_fourier (j J : ℤ) {s : ℂ} (hs : 1 < s.re)
    (y : ℝ) (hy : 0 < y) :
    Summable (fun p : (Σ n : ℕ, (ZMod (n + 1))ˣ × ℤ) =>
      ∫ x in (0 : ℝ)..1,
        ‖primitiveFourierTerm j J s y hy (residueRow p.1 p.2.1 p.2.2) x‖) := by
  have h := nonidentityResidueEquiv.symm.summable_iff.mpr
    (summable_integral_norm_nonidentity j J hs y hy)
  convert h using 1
  funext p
  obtain ⟨n, u, k⟩ := p
  simp only [Function.comp_def, fourierTerm_nonidentityResidueEquiv_symm]

/-- The actual indexed sum has the original coefficient minus its diagonal contribution. -/
theorem hasSum_indexed_fourier_integral (j J : ℤ) {s : ℂ} (hs : 1 < s.re)
    (y : ℝ) (hy : 0 < y) :
    HasSum (fun p : (Σ n : ℕ, (ZMod (n + 1))ˣ × ℤ) =>
      ∫ x in (0 : ℝ)..1,
        primitiveFourierTerm j J s y hy (residueRow p.1 p.2.1 p.2.2) x)
      ((∫ x in (0 : ℝ)..1, fourierSeries j J s y hy x) -
        (if j = J then (y : ℂ) ^ s else 0)) := by
  have h := nonidentityResidueEquiv.symm.hasSum_iff.mpr
    (hasSum_integral_nonidentity j J hs y hy)
  convert h using 1
  funext p
  obtain ⟨n, u, k⟩ := p
  simp only [Function.comp_def, fourierTerm_nonidentityResidueEquiv_symm]

end GapFamily.Analytic.PoincareFourierRegroup
