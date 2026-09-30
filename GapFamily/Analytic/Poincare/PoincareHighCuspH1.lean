import GapFamily.Analytic.Poincare.PoincareHighCuspLift
import GapFamily.Analytic.Modular.Elliptic.ModularEllipticChart
import Homogenization.Sobolev.H1.BasicLemmas

/-!
# Actual compact high-cusp H1 witnesses

The literal high-cusp term at threshold becomes globally smooth after
multiplication by a smooth compact upper cutoff. Its real scalar components
in the existing centered chart therefore give actual H1Function witnesses
on every open chart domain, without a Poisson or Sobolev input premise.
-/

noncomputable section

namespace GapFamily.Analytic.PoincareThresholdJet

open Set Filter UpperHalfPlane Homogenization PoincareHighCusp
open scoped ContDiff Topology

def highCuspCutoff (J : ℤ) (χ : ℂ → ℂ) (z : ℂ) : ℂ :=
  χ z * continuedHighCusp J 0 z

/-- Only local smoothness of the actual high-cusp term is used. -/
theorem contDiff_highCuspCutoff (J : ℤ) (χ : ℂ → ℂ)
    (hχ : ContDiff ℝ ∞ χ) (hs : tsupport χ ⊆ upperHalfPlaneSet) :
    ContDiff ℝ ∞ (highCuspCutoff J χ) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z ∈ upperHalfPlaneSet
  · exact hχ.contDiffAt.mul
      ((contDiffOn_continuedHighCusp J 0).contDiffAt
        (isOpen_upperHalfPlaneSet.mem_nhds hz))
  · have hzχ : z ∉ tsupport χ := fun h => hz (hs h)
    have hzero : highCuspCutoff J χ =ᶠ[𝓝 z] (fun _ => 0) := by
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hzχ] with w hw
      simp only [highCuspCutoff, hw, zero_mul, Pi.zero_apply]
    exact contDiffAt_const.congr_of_eventuallyEq hzero

theorem hasCompactSupport_highCuspCutoff (J : ℤ) (χ : ℂ → ℂ)
    (hc : HasCompactSupport χ) : HasCompactSupport (highCuspCutoff J χ) :=
  hc.mul_right

/-- The genuine smooth compact scalar chart function packaged in the vendored H1 interface. -/
def highCuspChartH1 (J : ℤ) (χ : ℂ → ℂ) (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ upperHalfPlaneSet)
    (L : ℂ →L[ℝ] ℝ) (z : ℂ) (S : Set (Fin 2 → ℝ)) (hS : IsOpen S) :
    H1Function S :=
  H1Function.ofContDiff hS
    ((L.contDiff.comp ((contDiff_highCuspCutoff J χ hχ hs).comp
      (ellipticChart_contDiff z))).of_le (by simp))
    (((hasCompactSupport_highCuspCutoff J χ hc).comp_homeomorph
      (ellipticChart z)).comp_left (map_zero L))

/-- The H1 value is the literal cutoff times the actual high-cusp term in centered coordinates. -/
@[simp] theorem highCuspChartH1_toFun (J : ℤ) (χ : ℂ → ℂ) (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ upperHalfPlaneSet)
    (L : ℂ →L[ℝ] ℝ) (z : ℂ) (S : Set (Fin 2 → ℝ)) (hS : IsOpen S) :
    (highCuspChartH1 J χ hχ hc hs L z S hS).toFun =
      fun v => L (χ (ellipticChart z v) * continuedHighCusp J 0 (ellipticChart z v)) := rfl

/-- Its H1 gradient is the actual ordinary derivative of that same chart function. -/
@[simp] theorem highCuspChartH1_grad (J : ℤ) (χ : ℂ → ℂ) (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ upperHalfPlaneSet)
    (L : ℂ →L[ℝ] ℝ) (z : ℂ) (S : Set (Fin 2 → ℝ)) (hS : IsOpen S)
    (v : Fin 2 → ℝ) (i : Fin 2) :
    (highCuspChartH1 J χ hχ hc hs L z S hS).grad v i =
      fderiv ℝ (fun w => L (χ (ellipticChart z w) *
        continuedHighCusp J 0 (ellipticChart z w))) v (basisVec i) := rfl

end GapFamily.Analytic.PoincareThresholdJet
