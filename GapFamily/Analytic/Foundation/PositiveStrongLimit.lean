import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.Continuous

/-! Positivity is preserved under genuine strong convergence of bounded operators. -/

noncomputable section
namespace GapFamily.Analytic.PositiveStrongLimit
open Filter
open scoped Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- A strong limit of positive operators is positive.  No operator-norm convergence
or positivity of the limit is assumed. -/
theorem isPositive_of_strong_tendsto {ι : Type*} {l : Filter ι} [l.NeBot]
    (A : ι → H →L[ℂ] H) (T : H →L[ℂ] H)
    (hA : ∀ i, (A i).IsPositive)
    (hlim : ∀ x, Tendsto (fun i => A i x) l (𝓝 (T x))) : T.IsPositive := by
  refine ContinuousLinearMap.isPositive_def.mpr ⟨?_, ?_⟩
  · intro x y
    have hleft := (hlim x).inner (𝕜 := ℂ) (tendsto_const_nhds (x := y))
    have hright := (tendsto_const_nhds (x := x)).inner (𝕜 := ℂ) (hlim y)
    exact tendsto_nhds_unique hleft (hright.congr' (Filter.Eventually.of_forall
      (fun i => ((hA i).inner_left_eq_inner_right x y).symm)))
  · intro x
    change 0 ≤ (inner ℂ (T x) x).re
    apply ge_of_tendsto
      (Complex.continuous_re.tendsto _ |>.comp
        ((hlim x).inner (𝕜 := ℂ) (tendsto_const_nhds (x := x))))
    exact Filter.Eventually.of_forall fun i => (hA i).re_inner_nonneg_left x

end GapFamily.Analytic.PositiveStrongLimit
