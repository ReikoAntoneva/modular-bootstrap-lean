import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.Complex.CauchyIntegral

noncomputable section

namespace GapFamily.Analytic.PositiveBCFPower

open Set
open scoped BoundedContinuousFunction

variable {X : Type*} [TopologicalSpace X]

/-- The logarithm of a positive lower clamp, bounded by factoring through its
actual compact interval of values. No lower bound for `p` is required. -/
def logClampBCF (p : X → ℝ) (hp : Continuous p) (M : ℝ)
    (hM : ∀ x, p x ≤ M) (ε : ℝ) (hε : 0 < ε) : X →ᵇ ℂ :=
  let q : C(Icc ε (max ε M), ℂ) :=
    ⟨fun t => (Real.log (t : ℝ) : ℂ),
      Complex.continuous_ofReal.comp
        (continuous_subtype_val.log fun t => (hε.trans_le t.property.1).ne')⟩
  (BoundedContinuousFunction.mkOfCompact q).compContinuous
    ⟨fun x => ⟨max ε (p x), le_max_left _ _, max_le_max le_rfl (hM x)⟩,
      (continuous_const.max hp).subtype_mk _⟩

@[simp] theorem logClampBCF_apply (p : X → ℝ) (hp : Continuous p) (M : ℝ)
    (hM : ∀ x, p x ≤ M) (ε : ℝ) (hε : 0 < ε) (x : X) :
    logClampBCF p hp M hM ε hε x = (Real.log (max ε (p x)) : ℂ) := rfl

/-- The positive-clamped complex power, constructed in the complete normed
algebra of bounded continuous functions. -/
def clampedPower (p : X → ℝ) (hp : Continuous p) (M : ℝ)
    (hM : ∀ x, p x ≤ M) (ε : ℝ) (hε : 0 < ε) (s : ℂ) : X →ᵇ ℂ :=
  NormedSpace.exp (s • logClampBCF p hp M hM ε hε)

@[simp] theorem clampedPower_apply (p : X → ℝ) (hp : Continuous p) (M : ℝ)
    (hM : ∀ x, p x ≤ M) (ε : ℝ) (hε : 0 < ε) (s : ℂ) (x : X) :
    clampedPower p hp M hM ε hε s x = ((max ε (p x) : ℝ) : ℂ) ^ s := by
  let ev : (X →ᵇ ℂ) →ₐ[ℂ] ℂ :=
    (ContinuousMap.evalAlgHom ℂ ℂ x).comp
      (BoundedContinuousFunction.toContinuousMapₐ ℂ)
  have hev : Continuous ev := (BoundedContinuousFunction.evalCLM ℂ x).continuous
  have hpos : 0 < max ε (p x) := hε.trans_le (le_max_left _ _)
  calc
    clampedPower p hp M hM ε hε s x =
        NormedSpace.exp (s * (Real.log (max ε (p x)) : ℂ)) :=
      NormedSpace.map_exp ev hev (s • logClampBCF p hp M hM ε hε)
    _ = Complex.exp ((Real.log (max ε (p x)) : ℂ) * s) := by
      rw [← Complex.exp_eq_exp_ℂ, mul_comm]
    _ = ((max ε (p x) : ℝ) : ℂ) ^ s := by
      rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hpos.ne'),
        ← Complex.ofReal_log hpos.le]

theorem clampedPower_analyticAt (p : X → ℝ) (hp : Continuous p) (M : ℝ)
    (hM : ∀ x, p x ≤ M) (ε : ℝ) (hε : 0 < ε) (s : ℂ) :
    AnalyticAt ℂ (clampedPower p hp M hM ε hε) s :=
  (differentiable_exp_smul_const ℂ (logClampBCF p hp M hM ε hε)).analyticAt s

end GapFamily.Analytic.PositiveBCFPower
