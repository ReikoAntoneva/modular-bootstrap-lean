import GapFamily.Analytic.Geometry.LaplacianMobiusCovariance
import GapFamily.Analytic.Elliptic.WeakLaplacianMollifier

noncomputable section
namespace GapFamily.Analytic.PoincareWeak
open Set Filter UpperHalfPlane
open LaplacianCovariance
open scoped ContDiff Topology

/-- Directional differentiation preserves smoothness for the actual complex test. -/
theorem testDerivative_contDiff {ψ : ℂ → ℂ} (hψ : ContDiff ℝ ∞ ψ) (v : ℂ) :
    ContDiff ℝ ∞ (fun z => fderiv ℝ ψ z v) :=
  (hψ.fderiv_right (by simp)).clm_apply contDiff_const

/-- The actual ordinary complex-valued Euclidean Laplacian is smooth. -/
theorem euclideanLaplacian_contDiff {ψ : ℂ → ℂ} (hψ : ContDiff ℝ ∞ ψ) :
    ContDiff ℝ ∞ (euclideanLaplacian ψ) :=
  (testDerivative_contDiff (testDerivative_contDiff hψ 1) 1).add
    (testDerivative_contDiff (testDerivative_contDiff hψ Complex.I) Complex.I)

/-- Differentiation does not enlarge the topological support. -/
theorem euclideanLaplacian_tsupport_subset (ψ : ℂ → ℂ) :
    tsupport (euclideanLaplacian ψ) ⊆ tsupport ψ := by
  apply (tsupport_add _ _).trans
  exact union_subset
    ((tsupport_fderiv_apply_subset ℝ 1).trans (tsupport_fderiv_apply_subset ℝ 1))
    ((tsupport_fderiv_apply_subset ℝ Complex.I).trans
      (tsupport_fderiv_apply_subset ℝ Complex.I))

/-- The actual negative hyperbolic Laplacian is smooth on the ambient plane. -/
theorem ordinaryHyperbolicLaplacian_contDiff {ψ : ℂ → ℂ}
    (hψ : ContDiff ℝ ∞ ψ) :
    ContDiff ℝ ∞ (ordinaryHyperbolicLaplacian ψ) :=
  ((Complex.imCLM.contDiff.pow 2).neg).smul (euclideanLaplacian_contDiff hψ)

theorem ordinaryHyperbolicLaplacian_continuous {ψ : ℂ → ℂ}
    (hψ : ContDiff ℝ ∞ ψ) :
    Continuous (ordinaryHyperbolicLaplacian ψ) :=
  (ordinaryHyperbolicLaplacian_contDiff hψ).continuous

theorem ordinaryHyperbolicLaplacian_tsupport_subset (ψ : ℂ → ℂ) :
    tsupport (ordinaryHyperbolicLaplacian ψ) ⊆ tsupport ψ :=
  (tsupport_smul_subset_right _ _).trans (euclideanLaplacian_tsupport_subset ψ)

theorem ordinaryHyperbolicLaplacian_hasCompactSupport {ψ : ℂ → ℂ}
    (hc : HasCompactSupport ψ) :
    HasCompactSupport (ordinaryHyperbolicLaplacian ψ) :=
  hc.of_isClosed_subset (isClosed_tsupport _)
    (ordinaryHyperbolicLaplacian_tsupport_subset ψ)

/-- The literal height denominator cannot enlarge the test support. -/
theorem testDivideHeightSquare_tsupport_subset (ψ : ℂ → ℂ) :
    tsupport (fun z => ψ z / (z.im : ℂ) ^ 2) ⊆ tsupport ψ := by
  simpa only [div_eq_mul_inv] using
    (tsupport_mul_subset_left (f := ψ) (g := fun z : ℂ => ((z.im : ℂ) ^ 2)⁻¹))

/-- The literal quotient is globally continuous when the test is supported in the upper plane. -/
theorem testDivideHeightSquare_continuous {ψ : ℂ → ℂ} (hψ : Continuous ψ)
    (hs : tsupport ψ ⊆ upperHalfPlaneSet) :
    Continuous (fun z => ψ z / (z.im : ℂ) ^ 2) := by
  apply continuous_of_tsupport
  intro z hz
  have hy : 0 < z.im := hs (testDivideHeightSquare_tsupport_subset ψ hz)
  exact hψ.continuousAt.div₀
    (((Complex.continuous_ofReal.comp Complex.continuous_im).pow 2).continuousAt)
    (pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr (ne_of_gt hy)))

/-- The actual height-divided test remains compactly supported. -/
theorem testDivideHeightSquare_hasCompactSupport {ψ : ℂ → ℂ}
    (hc : HasCompactSupport ψ) :
    HasCompactSupport (fun z => ψ z / (z.im : ℂ) ^ 2) :=
  hc.of_isClosed_subset (isClosed_tsupport _) (testDivideHeightSquare_tsupport_subset ψ)

end GapFamily.Analytic.PoincareWeak
