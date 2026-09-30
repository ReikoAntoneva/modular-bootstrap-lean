import Homogenization.Sobolev.Foundations.CubeNeumannW22CZ.WeakInteriorDQ.LimitHessianPointwise
import GapFamily.Analytic.Modular.Elliptic.ModularEllipticCubeSelection

/-!
# Fixed cube geometry for local weak Hessian regularity

The two cutoffs and the intermediate domain are constructed at fixed rational
scales, so applications supply only an actual weak Poisson equation and its
square-integrable source.
-/

noncomputable section

namespace GapFamily.Analytic.ModularElliptic

open Set Homogenization

theorem scaledOpenCubeSet_eq_metricBall {d : ℕ} (Q : TriadicCube d)
    {ρ : ℝ} (hρ : 0 < ρ) :
    scaledOpenCubeSet Q ρ = Metric.ball (cubeCenter Q) (ρ * cubeRadius Q) := by
  ext x
  simp only [scaledOpenCubeSet, mem_ofPred_eq, Metric.mem_ball,
    dist_pi_lt_iff (mul_pos hρ (cubeRadius_pos Q)), Real.dist_eq]

theorem scaledOpenCubeSet_isOpenBoundedConvexDomain {d : ℕ} (Q : TriadicCube d)
    {ρ : ℝ} (hρ : 0 < ρ) :
    IsOpenBoundedConvexDomain (scaledOpenCubeSet Q ρ) := by
  rw [scaledOpenCubeSet_eq_metricBall Q hρ]
  exact isOpenBoundedConvexDomain_ball _ (mul_pos hρ (cubeRadius_pos Q))

theorem scaledClosedCubeSet_subset_scaledOpenCubeSet_of_lt {d : ℕ}
    (Q : TriadicCube d) {ρ σ : ℝ} (hρσ : ρ < σ) :
    scaledClosedCubeSet Q ρ ⊆ scaledOpenCubeSet Q σ := by
  intro x hx i
  exact (hx i).trans_lt (mul_lt_mul_of_pos_right hρσ (cubeRadius_pos Q))

/-- The inner cutoff equals one on the half cube and vanishes beyond radius `5/8`. -/
def halfCubeCutoff {d : ℕ} (Q : TriadicCube d) :
    QuantitativeCubeCutoff Q (1 / 2) (5 / 8) :=
  QuantitativeCubeCutoff.canonical Q (1 / 2) (5 / 8) (by norm_num) (by norm_num)

/-- The outer energy cutoff is supported strictly inside the full cube. -/
def outerCubeCutoff {d : ℕ} (Q : TriadicCube d) :
    QuantitativeCubeCutoff Q (7 / 8) (15 / 16) :=
  QuantitativeCubeCutoff.canonical Q (7 / 8) (15 / 16) (by norm_num) (by norm_num)

theorem halfCubeCutoff_tsupport_subset {d : ℕ} (Q : TriadicCube d) :
    tsupport (halfCubeCutoff Q : Vec d → ℝ) ⊆ scaledOpenCubeSet Q (3 / 4) := by
  change tsupport (QuantitativeCubeCutoff.canonicalFun Q (1 / 2) (5 / 8)) ⊆ _
  exact (QuantitativeCubeCutoff.canonicalFun_tsupport_subset_scaledClosedCubeSet
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 5 / 8)).trans
      (scaledClosedCubeSet_subset_scaledOpenCubeSet_of_lt Q (by norm_num))

/-- Fixed cutoffs discharge every geometric premise of the interior Hessian theorem. -/
theorem halfCube_weakHessian_bound {d : ℕ} (Q : TriadicCube d)
    (u : H1Function (openCubeSet Q)) (f : Vec d → ℝ)
    (h : WeakPoissonEquationOn (openCubeSet Q) u f)
    (hf : MemScalarL2 (openCubeSet Q) f) :
    ∃ uS : H1Function (scaledOpenCubeSet Q (1 / 2)),
      uS.toFun = u.toFun ∧ uS.grad = u.grad ∧
        ∃ H : HasWeakHessianOn (scaledOpenCubeSet Q (1 / 2)) uS,
          H.hessianCoordL2NormSum ≤
            ∑ i : Fin d, ∑ _j : Fin d,
              WeakPoissonEquationOn.openCubeInnerQuotientHessianSmoothTestBound
                (ρ₁ := 1 / 2) (ρ₂ := 5 / 8) u f i (outerCubeCutoff Q) := by
  exact WeakPoissonEquationOn.exists_hasWeakHessianOn_restrict_hessianCoordL2NormSum_le_of_strict_inner_margin
    h hf (scaledOpenCubeSet_isOpenBoundedConvexDomain Q (by norm_num : (0 : ℝ) < 3 / 4))
    (halfCubeCutoff Q) (halfCubeCutoff_tsupport_subset Q)
    (scaledClosedCubeSet_subset_scaledOpenCubeSet_of_lt Q (by norm_num : (1 / 2 : ℝ) < 3 / 4))
    (outerCubeCutoff Q) (scaledOpenCubeSet_subset_scaledClosedCubeSet Q (3 / 4))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- Every actual `H¹` weak Poisson solution with an `L²` source has a weak
Hessian on its concentric half cube, with its original values and gradient. -/
theorem halfCube_weakHessian {d : ℕ} (Q : TriadicCube d)
    (u : H1Function (openCubeSet Q)) (f : Vec d → ℝ)
    (h : WeakPoissonEquationOn (openCubeSet Q) u f)
    (hf : MemScalarL2 (openCubeSet Q) f) :
    ∃ uS : H1Function (scaledOpenCubeSet Q (1 / 2)),
      uS.toFun = u.toFun ∧ uS.grad = u.grad ∧
        Nonempty (HasWeakHessianOn (scaledOpenCubeSet Q (1 / 2)) uS) := by
  obtain ⟨uS, huS, hgrad, H, _⟩ := halfCube_weakHessian_bound Q u f h hf
  exact ⟨uS, huS, hgrad, ⟨H⟩⟩

end GapFamily.Analytic.ModularElliptic
