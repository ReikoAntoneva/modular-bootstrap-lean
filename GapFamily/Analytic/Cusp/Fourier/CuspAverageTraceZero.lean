import GapFamily.Analytic.Cusp.Fourier.CuspAverageTrace
import GapFamily.Analytic.Cusp.Profile.CuspCollarMean
import GapFamily.Analytic.Cusp.MeanZero.CuspMeanZeroForm
import Mathlib.Analysis.SpecificLimits.Normed

/-! # The boundary trace vanishes on the actual zero-average cusp form

Shrinking ordinary collar means approximate the constructed form trace with a
proved gradient-energy error. Every such mean vanishes on the actual cusp-average
kernel, hence so does its boundary trace. No pointwise representative or trace
condition is added to the definition of the constrained form space.
-/

noncomputable section
namespace GapFamily.Analytic

open Set Filter MeasureTheory ModularGradient
open scoped Topology

def cuspFormCollarMean (ε : ℝ) (hε : 0 < ε) : FormDomain →L[ℂ] ℂ :=
  ((cuspCollarMean ε hε).comp (cuspRestrict 1)).comp formEmbedding

theorem cuspFormCollarMean_core (ε : ℝ) (hε : 0 < ε) (F : smoothCore) :
    cuspFormCollarMean ε hε (coreForm F) =
      ε⁻¹ • (∫ y in (1 : ℝ)..(1 + ε), cuspHorizontalAverage F.val y) :=
  cuspCollarMean_core ε hε F

theorem cuspAverageTrace_mean_error_sq_le (u : FormDomain) {ε : ℝ} (hε : 0 < ε) :
    ‖cuspAverageTrace u - cuspFormCollarMean ε hε u‖ ^ 2 ≤
      ε * ‖formGradient u‖ ^ 2 := by
  have hc : IsClosed {v : FormDomain |
      ‖cuspAverageTrace v - cuspFormCollarMean ε hε v‖ ^ 2 ≤
        ε * ‖formGradient v‖ ^ 2} :=
    isClosed_le ((cuspAverageTrace.continuous.sub
      (cuspFormCollarMean ε hε).continuous).norm.pow 2)
      (continuous_const.mul (formGradient.continuous.norm.pow 2))
  have hs : Set.range coreForm ⊆ {v : FormDomain |
      ‖cuspAverageTrace v - cuspFormCollarMean ε hε v‖ ^ 2 ≤
        ε * ‖formGradient v‖ ^ 2} := by
    rintro _ ⟨F, rfl⟩
    change ‖cuspAverageTrace (coreForm F) - cuspFormCollarMean ε hε (coreForm F)‖ ^ 2 ≤ _
    rw [cuspAverageTrace_core, cuspFormCollarMean_core, formGradient_coreForm]
    exact cuspAverageTraceCore_mean_error_sq_le F hε
  exact closure_minimal hs hc (coreForm_denseRange u)

theorem cuspFormCollarMean_eq_zero (u : cuspMeanZeroForm) {ε : ℝ} (hε : 0 < ε) :
    cuspFormCollarMean ε hε (u : FormDomain) = 0 :=
  cuspCollarMean_zero_on_kernel ε hε (cuspRestrict 1 (meanZeroCuspEmbedding u)) u.property

/-- Vanishing ordinary cusp average forces the actual form boundary trace to vanish. -/
theorem cuspAverageTrace_eq_zero (u : cuspMeanZeroForm) :
    cuspAverageTrace (u : FormDomain) = 0 := by
  have hb (n : ℕ) : ‖cuspAverageTrace (u : FormDomain)‖ ^ 2 ≤
      (1 / ((n : ℝ) + 1)) * ‖formGradient (u : FormDomain)‖ ^ 2 := by
    have hn : 0 < 1 / ((n : ℝ) + 1) := by positivity
    have h := cuspAverageTrace_mean_error_sq_le (u : FormDomain) hn
    rw [cuspFormCollarMean_eq_zero u hn, sub_zero] at h
    exact h
  have ht : Tendsto (fun n : ℕ => (1 / ((n : ℝ) + 1)) *
      ‖formGradient (u : FormDomain)‖ ^ 2) atTop (𝓝 0) := by
    simpa only [zero_mul] using
      tendsto_one_div_add_atTop_nhds_zero_nat.mul_const (‖formGradient (u : FormDomain)‖ ^ 2)
  have hz := ge_of_tendsto ht (Eventually.of_forall hb)
  exact norm_eq_zero.mp (by nlinarith [norm_nonneg (cuspAverageTrace (u : FormDomain))])

theorem cuspMeanZeroForm_le_trace_ker : cuspMeanZeroForm ≤ cuspAverageTrace.ker := by
  intro u hu
  exact cuspAverageTrace_eq_zero ⟨u, hu⟩

end GapFamily.Analytic
