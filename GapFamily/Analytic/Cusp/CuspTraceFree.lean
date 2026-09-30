import GapFamily.Analytic.Cusp.Fourier.CuspAverageTrace

/-!
# Actual removal of the boundary-average constant

Subtracting the literal trace times the genuine constant core vector preserves
energy and gives smooth approximants inside the actual zero-trace form kernel.
This is a trace splitting, without an assertion of mass orthogonality.
-/

noncomputable section
namespace GapFamily.Analytic
open Set Filter ModularGradient
open scoped Topology

def cuspTraceFreeCore : smoothCore →ₗ[ℂ] smoothCore :=
  LinearMap.id - cuspAverageTraceCore.smulRight (constantCore 1)

def cuspTraceFree : FormDomain →L[ℂ] FormDomain :=
  ContinuousLinearMap.id ℂ FormDomain - cuspAverageTrace.smulRight (coreForm (constantCore 1))

@[simp] theorem cuspTraceFreeCore_apply (F : smoothCore) :
    cuspTraceFreeCore F = F - cuspHorizontalAverage F.val 1 • constantCore 1 := rfl

@[simp] theorem cuspTraceFree_apply (u : FormDomain) :
    cuspTraceFree u = u - cuspAverageTrace u • coreForm (constantCore 1) := rfl

@[simp] theorem cuspAverageTrace_cuspTraceFree (u : FormDomain) :
    cuspAverageTrace (cuspTraceFree u) = 0 := by
  simp only [cuspTraceFree_apply, map_sub, map_smul, cuspAverageTrace_constantCore,
    smul_eq_mul, mul_one, sub_self]

@[simp] theorem cuspTraceFree_coreForm (F : smoothCore) :
    cuspTraceFree (coreForm F) = coreForm (cuspTraceFreeCore F) := by
  simp only [cuspTraceFree_apply, cuspTraceFreeCore_apply, map_sub, map_smul,
    cuspAverageTrace_core]

@[simp] theorem cuspTraceFreeCore_trace (F : smoothCore) :
    cuspHorizontalAverage (cuspTraceFreeCore F).val 1 = 0 := by
  rw [← cuspAverageTrace_core, ← cuspTraceFree_coreForm, cuspAverageTrace_cuspTraceFree]

@[simp] theorem formGradient_cuspTraceFree (u : FormDomain) :
    formGradient (cuspTraceFree u) = formGradient u := by
  simp only [cuspTraceFree_apply, map_sub, map_smul, formGradient_coreForm,
    coreGradient_constantCore, smul_zero, sub_zero]

@[simp] theorem coreGradient_cuspTraceFreeCore (F : smoothCore) :
    coreGradient (cuspTraceFreeCore F) = coreGradient F := by
  rw [← formGradient_coreForm, ← cuspTraceFree_coreForm, formGradient_cuspTraceFree,
    formGradient_coreForm]

theorem cuspTraceFree_eq_self {u : FormDomain} (hu : cuspAverageTrace u = 0) :
    cuspTraceFree u = u := by
  simp only [cuspTraceFree_apply, hu, zero_smul, sub_zero]

@[simp] theorem cuspTraceFree_idempotent (u : FormDomain) :
    cuspTraceFree (cuspTraceFree u) = cuspTraceFree u :=
  cuspTraceFree_eq_self (cuspAverageTrace_cuspTraceFree u)

theorem cuspTraceFreeCore_form_norm_le (F : smoothCore) :
    ‖coreForm (cuspTraceFreeCore F)‖ ≤ ‖cuspTraceFree‖ * ‖coreForm F‖ := by
  rw [← cuspTraceFree_coreForm]
  exact cuspTraceFree.le_opNorm (coreForm F)

/-- Every actual zero-trace vector has genuine zero-trace smooth-core
approximants in the full mass-plus-gradient norm. -/
theorem exists_traceFree_coreForm_tendsto (u : FormDomain) (hu : cuspAverageTrace u = 0) :
    ∃ F : ℕ → smoothCore, (∀ n, cuspHorizontalAverage (F n).val 1 = 0) ∧
      Tendsto (fun n => coreForm (F n)) atTop (𝓝 u) := by
  obtain ⟨F, hF⟩ := exists_coreForm_tendsto u
  refine ⟨fun n => cuspTraceFreeCore (F n), fun n => cuspTraceFreeCore_trace (F n), ?_⟩
  have ht := cuspTraceFree.continuous.continuousAt.tendsto.comp hF
  simpa only [Function.comp_def, cuspTraceFree_coreForm, cuspTraceFree_eq_self hu] using ht

end GapFamily.Analytic
