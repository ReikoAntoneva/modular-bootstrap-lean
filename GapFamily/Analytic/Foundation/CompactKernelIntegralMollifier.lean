import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.ContinuousMap.CompactlySupported
import Mathlib.Topology.UniformSpace.HeineCantor

/-! The actual translated normalized bump as a continuous family of bounded kernels. -/

noncomputable section

open MeasureTheory
open scoped CompactlySupported BoundedContinuousFunction

namespace GapFamily.Analytic

/-- Translate and reflect a bounded continuous function in its source variable. -/
def reflectedTranslateKernel (φ : ℂ →ᵇ ℂ) (x : ℂ) : ℂ →ᵇ ℂ :=
  φ.compContinuous ⟨fun y => x - y, by fun_prop⟩

@[simp]
theorem reflectedTranslateKernel_apply (φ : ℂ →ᵇ ℂ) (x y : ℂ) :
    reflectedTranslateKernel φ x y = φ (x - y) := rfl

/-- Uniform continuity of the profile gives uniform continuity in the kernel supremum norm. -/
theorem uniformContinuous_reflectedTranslateKernel (φ : ℂ →ᵇ ℂ)
    (hφ : UniformContinuous φ) : UniformContinuous (reflectedTranslateKernel φ) := by
  apply Metric.uniformContinuous_iff.mpr
  intro ε hε
  obtain ⟨δ, hδ, hclose⟩ := Metric.uniformContinuous_iff.mp hφ (ε / 2) (half_pos hε)
  refine ⟨δ, hδ, fun x x' hxx => ?_⟩
  apply lt_of_le_of_lt ((BoundedContinuousFunction.dist_le (half_pos hε).le).mpr ?_)
    (half_lt_self hε)
  intro y
  apply (hclose (a := x - y) (b := x' - y) ?_).le
  simpa only [dist_eq_norm, sub_sub_sub_cancel_right] using hxx

/-- The normalized real bump, regarded as a complex compactly supported continuous map. -/
def normedMollifierCompactlySupported (ρ : ContDiffBump (0 : ℂ)) : C_c(ℂ, ℂ) where
  toFun x := (ρ.normed volume x : ℂ)
  continuous_toFun := Complex.continuous_ofReal.comp ρ.continuous_normed
  hasCompactSupport' := ρ.hasCompactSupport_normed.comp_left (g := Complex.ofReal) (by simp)

/-- The normalized bump as a bounded continuous complex-valued function. -/
def normedMollifierBCF (ρ : ContDiffBump (0 : ℂ)) : ℂ →ᵇ ℂ :=
  (normedMollifierCompactlySupported ρ).toBoundedContinuousFunction

@[simp]
theorem normedMollifierBCF_apply (ρ : ContDiffBump (0 : ℂ)) (x : ℂ) :
    normedMollifierBCF ρ x = (ρ.normed volume x : ℂ) := rfl

theorem uniformContinuous_normedMollifierBCF (ρ : ContDiffBump (0 : ℂ)) :
    UniformContinuous (normedMollifierBCF ρ) :=
  (normedMollifierCompactlySupported ρ).hasCompactSupport.uniformContinuous_of_continuous
    (normedMollifierCompactlySupported ρ).continuous

/-- The actual fixed mollifier kernel on any target subset, continuous in the supremum norm. -/
def normedMollifierKernelFamily (ρ : ContDiffBump (0 : ℂ)) (T : Set ℂ) :
    C(T, ℂ →ᵇ ℂ) where
  toFun x := reflectedTranslateKernel (normedMollifierBCF ρ) x
  continuous_toFun :=
    (uniformContinuous_reflectedTranslateKernel _ (uniformContinuous_normedMollifierBCF ρ)).continuous.comp
      continuous_subtype_val

@[simp]
theorem normedMollifierKernelFamily_apply (ρ : ContDiffBump (0 : ℂ)) (T : Set ℂ)
    (x : T) (y : ℂ) :
    normedMollifierKernelFamily ρ T x y = (ρ.normed volume ((x : ℂ) - y) : ℂ) := rfl

end GapFamily.Analytic
