import GapFamily.Analytic.Modular.ModularGradientCore
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-!
# Finite modular norms of compactly supported smooth tests

A globally smooth compactly supported complex test and every hyperbolic
frame derivative have finite norms in the actual modular measure. No
restriction on the location of the support is required.
-/

noncomputable section

namespace GapFamily.Analytic.ModularGradient

open Set MeasureTheory UpperHalfPlane
open scoped ContDiff

/-- A compactly supported continuous function is in the actual modular L² space. -/
theorem memLp_test_value (φ : ℂ → ℂ) (hφ : Continuous φ)
    (hc : HasCompactSupport φ) :
    MemLp (fun τ : UpperHalfPlane => φ τ) 2 modularMeasure :=
  (memLp_modularCoordinate_iff φ 2).mp (hφ.memLp_of_hasCompactSupport hc)

/-- Global smoothness makes each coordinate derivative continuous. -/
theorem continuous_complexTestDerivative (φ : ℂ → ℂ) (hφ : ContDiff ℝ ∞ φ) (v : ℂ) :
    Continuous (fun z => fderiv ℝ φ z v) :=
  (hφ.continuous_fderiv_apply (by simp)).comp (continuous_id.prodMk continuous_const)

/-- The hyperbolic coordinate factor preserves compact support of the derivative. -/
theorem compactSupport_testDirectional (φ : ℂ → ℂ) (hc : HasCompactSupport φ) (v : ℂ) :
    HasCompactSupport (fun z : ℂ => (z.im : ℂ) * fderiv ℝ φ z v) :=
  (hc.fderiv_apply ℝ v).mul_left

/-- Every hyperbolic directional derivative of a smooth compact test has
finite L² norm in complex coordinates. -/
theorem memLp_testDirectional_coordinate (φ : ℂ → ℂ) (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (v : ℂ) :
    MemLp (fun z : ℂ => (z.im : ℂ) * fderiv ℝ φ z v) 2 modularCoordinateMeasure :=
  ((Complex.continuous_ofReal.comp Complex.continuous_im).mul
    (continuous_complexTestDerivative φ hφ v)).memLp_of_hasCompactSupport
      (compactSupport_testDirectional φ hc v)

/-- The same derivative belongs to the actual fundamental-domain L² space. -/
theorem memLp_test_directional (φ : ℂ → ℂ) (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (v : ℂ) :
    MemLp (directional φ v) 2 modularMeasure :=
  (memLp_modularCoordinate_iff _ 2).mp (memLp_testDirectional_coordinate φ hφ hc v)

end GapFamily.Analytic.ModularGradient
