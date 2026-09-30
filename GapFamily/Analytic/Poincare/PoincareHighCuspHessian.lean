import GapFamily.Analytic.Poincare.PoincareHighCuspH1
import Homogenization.Sobolev.Foundations.CubeNeumannW22CZ.WeakInterior

/-!
# Actual weak Hessians for the high-cusp term and sums

The smooth compact high-cusp chart function has its classical weak Hessian.
Weak Hessian witnesses add by the already established H1 addition theorem
applied to their actual gradient coordinates.
-/

noncomputable section

namespace GapFamily.Analytic.PoincareThresholdJet

open Set UpperHalfPlane Homogenization PoincareHighCusp
open scoped ContDiff Topology

/-- The actual high-cusp chart H1 witness carries the classical weak Hessian. -/
def highCuspChartHessian (J : ℤ) (χ : ℂ → ℂ) (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ upperHalfPlaneSet)
    (L : ℂ →L[ℝ] ℝ) (z : ℂ) (S : Set (Fin 2 → ℝ)) (hS : IsOpen S) :
    HasWeakHessianOn S (highCuspChartH1 J χ hχ hc hs L z S hS) :=
  hasWeakHessianOn_ofContDiff hS
    (L.contDiff.comp ((contDiff_highCuspCutoff J χ hχ hs).comp
      (ellipticChart_contDiff z)))
    (((hasCompactSupport_highCuspCutoff J χ hc).comp_homeomorph
      (ellipticChart z)).comp_left (map_zero L))

@[simp] theorem highCuspChartHessian_hess (J : ℤ) (χ : ℂ → ℂ)
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ upperHalfPlaneSet) (L : ℂ →L[ℝ] ℝ) (z : ℂ)
    (S : Set (Fin 2 → ℝ)) (hS : IsOpen S) (i j : Fin 2) :
    (highCuspChartHessian J χ hχ hc hs L z S hS).hess i j =
      euclideanCoordSecondDeriv i j (fun v =>
        L (χ (ellipticChart z v) * continuedHighCusp J 0 (ellipticChart z v))) := rfl

/-- Add genuine weak Hessians, with literal coordinatewise Hessian sum. -/
def addWeakHessian {d : ℕ} {S : Set (Vec d)} {u v : H1Function S}
    (H : HasWeakHessianOn S u) (G : HasWeakHessianOn S v) :
    HasWeakHessianOn S (u + v) where
  hess := fun i j x => H.hess i j x + G.hess i j x
  hess_memL2 := fun i j => (H.hess_memL2 i j).add (G.hess_memL2 i j)
  weak_second := by
    intro i j
    let U : H1Function S :=
      { toFun := fun x => u.grad x i
        grad := fun x k => H.hess i k x
        memL2 := u.gradMemL2 i
        gradMemL2 := fun k => H.hess_memL2 i k
        hasWeakGradient := H.weak_second i }
    let V : H1Function S :=
      { toFun := fun x => v.grad x i
        grad := fun x k => G.hess i k x
        memL2 := v.gradMemL2 i
        gradMemL2 := fun k => G.hess_memL2 i k
        hasWeakGradient := G.weak_second i }
    exact (U + V).hasWeakGradient j

@[simp] theorem addWeakHessian_hess {d : ℕ} {S : Set (Vec d)}
    {u v : H1Function S} (H : HasWeakHessianOn S u) (G : HasWeakHessianOn S v)
    (i j : Fin d) (x : Vec d) :
    (addWeakHessian H G).hess i j x = H.hess i j x + G.hess i j x := rfl

end GapFamily.Analytic.PoincareThresholdJet
