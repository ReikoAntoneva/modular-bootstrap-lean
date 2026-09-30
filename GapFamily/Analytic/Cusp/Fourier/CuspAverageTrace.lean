import GapFamily.Analytic.Cusp.Fourier.CuspAverageTraceCore
import Mathlib.Analysis.Normed.Operator.Extend

/-! # The actual cusp-average boundary trace on the completed form domain

The literal smooth-core average at height one extends uniquely using its proved
form-norm bound. This is a constructed continuous functional on the actual
closed modular gradient graph.
-/

noncomputable section
namespace GapFamily.Analytic

open Set MeasureTheory ModularGradient

def cuspAverageTrace : FormDomain →L[ℂ] ℂ :=
  cuspAverageTraceCore.extendOfNorm coreForm

@[simp] theorem cuspAverageTrace_core (F : smoothCore) :
    cuspAverageTrace (coreForm F) = cuspHorizontalAverage F.val 1 :=
  LinearMap.extendOfNorm_eq coreForm_denseRange
    ⟨4, cuspAverageTraceCore_norm_le⟩ F

theorem cuspAverageTrace_norm_le_four : ‖cuspAverageTrace‖ ≤ 4 :=
  LinearMap.opNorm_extendOfNorm_le coreForm_denseRange (by norm_num)
    cuspAverageTraceCore_norm_le

theorem cuspAverageTrace_norm_le (u : FormDomain) :
    ‖cuspAverageTrace u‖ ≤ 4 * ‖u‖ :=
  (cuspAverageTrace.le_opNorm u).trans
    (mul_le_mul_of_nonneg_right cuspAverageTrace_norm_le_four (norm_nonneg u))

@[simp] theorem cuspAverageTrace_constantCore (c : ℂ) :
    cuspAverageTrace (coreForm (constantCore c)) = c := by
  rw [cuspAverageTrace_core]
  simp only [cuspHorizontalAverage, cuspHorizontalSlice, constantCore,
    intervalIntegral.integral_const]
  norm_num

theorem cuspAverageTrace_surjective : Function.Surjective cuspAverageTrace :=
  fun c => ⟨coreForm (constantCore c), cuspAverageTrace_constantCore c⟩

theorem cuspAverageTrace_unique (T : FormDomain →L[ℂ] ℂ)
    (hT : ∀ F : smoothCore, T (coreForm F) = cuspHorizontalAverage F.val 1) :
    T = cuspAverageTrace := by
  apply ContinuousLinearMap.ext
  intro u
  have hc : IsClosed {v : FormDomain | T v = cuspAverageTrace v} :=
    isClosed_eq T.continuous cuspAverageTrace.continuous
  have hs : Set.range coreForm ⊆ {v : FormDomain | T v = cuspAverageTrace v} := by
    rintro _ ⟨F, rfl⟩
    change T (coreForm F) = cuspAverageTrace (coreForm F)
    rw [hT, cuspAverageTrace_core]
  exact closure_minimal hs hc (coreForm_denseRange u)

end GapFamily.Analytic
