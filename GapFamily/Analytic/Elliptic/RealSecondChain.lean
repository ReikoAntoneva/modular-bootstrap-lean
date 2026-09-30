import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul

noncomputable section
namespace GapFamily.Analytic.SpatialPoint
open Filter
open scoped Topology

/-- The second real derivative chain rule for a real inner coordinate and
complex-valued outer profile, under only pointwise C² hypotheses. -/
theorem deriv_deriv_comp_real {q : ℝ → ℝ} {g : ℝ → ℂ} {x : ℝ}
    (hq : ContDiffAt ℝ 2 q x) (hg : ContDiffAt ℝ 2 g (q x)) :
    deriv (deriv (fun t => g (q t))) x =
      (deriv q x) ^ 2 • deriv (deriv g) (q x) +
        deriv (deriv q) x • deriv g (q x) := by
  have heq : deriv (fun t => g (q t)) =ᶠ[𝓝 x]
      (fun t => deriv q t • deriv g (q t)) := by
    filter_upwards [hq.eventually (by norm_num),
      hq.continuousAt.eventually (hg.eventually (by norm_num))] with t hqt hgt
    exact deriv.scomp t (hgt.differentiableAt (by norm_num))
      (hqt.differentiableAt (by norm_num))
  have hq' : HasDerivAt (deriv q) (deriv (deriv q) x) x :=
    ((hq.derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasDerivAt
  have hg' : HasDerivAt (deriv g) (deriv (deriv g) (q x)) (q x) :=
    ((hg.derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasDerivAt
  have hcomp := hg'.scomp x (hq.differentiableAt (by norm_num)).hasDerivAt
  have hprod := hq'.fun_smul hcomp
  rw [heq.deriv_eq]
  simpa only [Function.comp_apply, smul_smul, pow_two] using hprod.deriv

end GapFamily.Analytic.SpatialPoint
