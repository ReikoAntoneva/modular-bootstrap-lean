import GapFamily.Analytic.Cusp.CuspCoordinate
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module
import Mathlib.Tactic.Ring

/-!
# Differential conjugation in the scalar cusp coordinate

The substitution `f(y) = sqrt(y) • u(log y)` converts the scalar hyperbolic
operator `-y² d²/dy²` into `-d²/dt² + 1/4`. The identities here are derived
from the actual chain and product rules. They hold for functions valued in
any real normed vector space, in particular for complex-valued functions.
-/

open Set Filter
open scoped Topology

namespace GapFamily.Analytic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The first derivative of the actual cusp substitution. -/
theorem hasDerivAt_cuspLift {u : ℝ → E} {u' : E} {y : ℝ}
    (hy : 0 < y) (hu : HasDerivAt u u' (Real.log y)) :
    HasDerivAt (cuspLift u)
      ((Real.sqrt y)⁻¹ • (u' + (1 / 2 : ℝ) • u (Real.log y))) y := by
  change HasDerivAt (fun z => Real.sqrt z • u (Real.log z)) _ y
  have hs : Real.sqrt y ≠ 0 := (Real.sqrt_pos.mpr hy).ne'
  have hcoef : Real.sqrt y * y⁻¹ = (Real.sqrt y)⁻¹ := by
    field_simp
    nlinarith [Real.sq_sqrt hy.le]
  have hhalf : 1 / (2 * Real.sqrt y) = (Real.sqrt y)⁻¹ * (1 / 2 : ℝ) := by ring
  have h := (Real.hasDerivAt_sqrt hy.ne').smul (hu.scomp y (Real.hasDerivAt_log hy.ne'))
  simpa only [Function.comp_def, Pi.smul_def', Pi.smul_def,
    smul_add, smul_smul, hcoef, hhalf] using h

/-- Differentiating the first-derivative formula cancels the first derivative
of `u`, leaving precisely the scalar potential `1/4`. -/
theorem hasDerivAt_cuspLift_deriv_formula {u : ℝ → E} {u' u'' : E} {y : ℝ}
    (hy : 0 < y) (hu : HasDerivAt u u' (Real.log y))
    (hu' : HasDerivAt (deriv u) u'' (Real.log y)) :
    HasDerivAt (fun y => (Real.sqrt y)⁻¹ •
      (deriv u (Real.log y) + (1 / 2 : ℝ) • u (Real.log y)))
      ((y * Real.sqrt y)⁻¹ • (u'' - (1 / 4 : ℝ) • u (Real.log y))) y := by
  have hs : Real.sqrt y ≠ 0 := (Real.sqrt_pos.mpr hy).ne'
  have hinv := (Real.hasDerivAt_sqrt hy.ne').inv hs
  have hinner := (hu'.scomp y (Real.hasDerivAt_log hy.ne')).add
    ((hu.scomp y (Real.hasDerivAt_log hy.ne')).const_smul (1 / 2 : ℝ))
  have hh := hinv.smul hinner
  simp only [Pi.smul_def', Pi.smul_def, Pi.add_def, Pi.inv_def, Function.comp_def] at hh
  rw [hu.deriv] at hh
  convert hh using 1
  have hyinv : y⁻¹ = (Real.sqrt y)⁻¹ ^ 2 := by
    rw [inv_pow, Real.sq_sqrt hy.le]
  simp only [smul_add, smul_sub, smul_smul, mul_inv_rev, hyinv]
  module

theorem deriv_cuspLift {u : ℝ → E} (hu : Differentiable ℝ u)
    {y : ℝ} (hy : 0 < y) :
    deriv (cuspLift u) y =
      (Real.sqrt y)⁻¹ • (deriv u (Real.log y) + (1 / 2 : ℝ) • u (Real.log y)) :=
  (hasDerivAt_cuspLift hy (hu (Real.log y)).hasDerivAt).deriv

/-- The second derivative is obtained from an identity on the open positive
half-line, rather than by differentiating an equality at one isolated point. -/
theorem deriv_deriv_cuspLift {u : ℝ → E} (hu : Differentiable ℝ u)
    {y : ℝ} (hy : 0 < y) (hu' : DifferentiableAt ℝ (deriv u) (Real.log y)) :
    deriv (deriv (cuspLift u)) y =
      (y * Real.sqrt y)⁻¹ •
        (deriv (deriv u) (Real.log y) - (1 / 4 : ℝ) • u (Real.log y)) := by
  have heq : Set.EqOn (deriv (cuspLift u))
      (fun y => (Real.sqrt y)⁻¹ •
        (deriv u (Real.log y) + (1 / 2 : ℝ) • u (Real.log y))) (Ioi 0) :=
    fun z hz => deriv_cuspLift hu hz
  rw [heq.deriv isOpen_Ioi hy]
  exact (hasDerivAt_cuspLift_deriv_formula hy (hu (Real.log y)).hasDerivAt hu'.hasDerivAt).deriv

/-- The actual scalar hyperbolic differential operator conjugates to
`-u'' + u/4` under the cusp coordinate substitution. -/
theorem cuspLift_laplacian {u : ℝ → E} (hu : ContDiff ℝ 2 u)
    {y : ℝ} (hy : 0 < y) :
    -(y ^ 2) • deriv (deriv (cuspLift u)) y =
      Real.sqrt y • (-deriv (deriv u) (Real.log y) + (1 / 4 : ℝ) • u (Real.log y)) := by
  rw [deriv_deriv_cuspLift (hu.differentiable (by norm_num)) hy
    (hu.differentiable_deriv_two (Real.log y)), smul_smul]
  have hs : Real.sqrt y ≠ 0 := (Real.sqrt_pos.mpr hy).ne'
  have hcoef : -(y ^ 2) * (y * Real.sqrt y)⁻¹ = -Real.sqrt y := by
    field_simp
    nlinarith [Real.sq_sqrt hy.le]
  rw [hcoef]
  module

end GapFamily.Analytic
