import GapFamily.Analytic.Cusp.Scalar.CuspScalarFormLiftPairing
import GapFamily.Analytic.Cusp.Profile.CuspProfileForm
import GapFamily.Analytic.Cusp.Scalar.CuspScalarForm
import GapFamily.Analytic.Cusp.CuspTraceFree
import GapFamily.Analytic.Cusp.Fourier.CuspAverageScalarNorm
import GapFamily.Analytic.Cusp.Fourier.CuspAverageDerivative

/-!
# Actual scalar lift of the trace-free smooth modular core

The ordinary average of the genuine trace-free core has the proved smoothness,
zero trace, weighted mass, and derivative energy required by the actual scalar
profile constructor. Its ambient representative proves linearity; its exact
profile norm identifies the sharp form and gradient bounds.
-/

noncomputable section

namespace GapFamily.Analytic

open Set Filter MeasureTheory UpperHalfPlane ModularGradient
open scoped Topology ContDiff

/-- The actual profile constructor belongs to the closed scalar form space. -/
theorem cuspProfileForm_mem_cuspScalarForm (b : ℝ → ℂ)
    (hb : ContDiffOn ℝ ∞ b (Ioi 0)) (hb1 : b 1 = 0)
    (hv : IntegrableOn (fun y => ‖b y‖ ^ 2 / y ^ 2) (Ioi 1))
    (hd : IntegrableOn (fun y => ‖deriv b y‖ ^ 2) (Ioi 1)) :
    cuspProfileForm b hb hb1 hv hd ∈ cuspScalarForm := by
  apply cuspScalarForm_mem_of_tendsto _ (cuspProfileForm_core_tendsto b hb hb1 hv hd)
  exact Eventually.of_forall (fun n => cuspProfileCore_mem_cuspScalarForm
    (cuspProfileApproximation b n) (cuspProfileApproximation_contDiff hb n)
    (cuspProfileApproximation_hasCompactSupport b n)
    (cuspProfileApproximation_tsupport_subset b n))

/-- The literal finite-energy profile of the actual trace-free horizontal average. -/
def cuspScalarFormLiftCoreFun (F : smoothCore) : FormDomain :=
  cuspProfileForm (cuspHorizontalAverage (cuspTraceFreeCore F).val)
    (contDiffOn_cuspHorizontalAverage (cuspTraceFreeCore F))
    (cuspTraceFreeCore_trace F)
    (cuspHorizontalAverage_scalar_mass_le (cuspTraceFreeCore F)).1
    (cuspHorizontalAverage_deriv_integrable_and_le (cuspTraceFreeCore F)).1

theorem cuspScalarFormLiftCoreFun_embedding (F : smoothCore) :
    formEmbedding (cuspScalarFormLiftCoreFun F) =
      cuspScalarProjection (value (cuspTraceFreeCore F)) := by
  apply Lp.ext
  exact (cuspProfileForm_embedding_ae _ _ _ _ _).trans
    (cuspScalarProjection_value_ae (cuspTraceFreeCore F)).symm

/-- Linearity follows from the literal projection identity and the actual
injective form embedding, not from arbitrary choices of profile approximants. -/
def cuspScalarFormLiftCore : smoothCore →ₗ[ℂ] FormDomain where
  toFun := cuspScalarFormLiftCoreFun
  map_add' F G := by
    apply formEmbedding_injective
    simp only [map_add, cuspScalarFormLiftCoreFun_embedding]
  map_smul' c F := by
    apply formEmbedding_injective
    simp only [map_smul, cuspScalarFormLiftCoreFun_embedding, RingHom.id_apply]

theorem cuspScalarFormLiftCore_embedding (F : smoothCore) :
    formEmbedding (cuspScalarFormLiftCore F) =
      cuspScalarProjection (value (cuspTraceFreeCore F)) :=
  cuspScalarFormLiftCoreFun_embedding F

theorem cuspScalarFormLiftCore_mem (F : smoothCore) :
    cuspScalarFormLiftCore F ∈ cuspScalarForm :=
  cuspProfileForm_mem_cuspScalarForm
    (cuspHorizontalAverage (cuspTraceFreeCore F).val)
    (contDiffOn_cuspHorizontalAverage (cuspTraceFreeCore F))
    (cuspTraceFreeCore_trace F)
    (cuspHorizontalAverage_scalar_mass_le (cuspTraceFreeCore F)).1
    (cuspHorizontalAverage_deriv_integrable_and_le (cuspTraceFreeCore F)).1

theorem cuspScalarFormLiftCore_trace_eq_zero (F : smoothCore) :
    cuspAverageTrace (cuspScalarFormLiftCore F) = 0 :=
  cuspScalarForm_trace ⟨cuspScalarFormLiftCore F, cuspScalarFormLiftCore_mem F⟩

/-- The exact profile mass and energy do not exceed those of the trace-free core. -/
theorem cuspScalarFormLiftCore_norm_le (F : smoothCore) :
    ‖cuspScalarFormLiftCore F‖ ≤ ‖coreForm (cuspTraceFreeCore F)‖ := by
  have hn := cuspProfileForm_norm_sq
    (cuspHorizontalAverage (cuspTraceFreeCore F).val)
    (contDiffOn_cuspHorizontalAverage (cuspTraceFreeCore F))
    (cuspTraceFreeCore_trace F)
    (cuspHorizontalAverage_scalar_mass_le (cuspTraceFreeCore F)).1
    (cuspHorizontalAverage_deriv_integrable_and_le (cuspTraceFreeCore F)).1
  change ‖cuspScalarFormLiftCore F‖ ^ 2 = _ at hn
  have hv := (cuspHorizontalAverage_scalar_mass_le (cuspTraceFreeCore F)).2
  have hd := (cuspHorizontalAverage_deriv_integrable_and_le (cuspTraceFreeCore F)).2
  have hfull := coreForm_norm_sq (cuspTraceFreeCore F)
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  linarith

/-- The actual lifted scalar gradient is controlled by the original core gradient. -/
theorem cuspScalarFormLiftCore_gradient_norm_le (F : smoothCore) :
    ‖formGradient (cuspScalarFormLiftCore F)‖ ≤ ‖coreGradient F‖ := by
  have hn := cuspProfileForm_gradient_norm_sq
    (cuspHorizontalAverage (cuspTraceFreeCore F).val)
    (contDiffOn_cuspHorizontalAverage (cuspTraceFreeCore F))
    (cuspTraceFreeCore_trace F)
    (cuspHorizontalAverage_scalar_mass_le (cuspTraceFreeCore F)).1
    (cuspHorizontalAverage_deriv_integrable_and_le (cuspTraceFreeCore F)).1
  change ‖formGradient (cuspScalarFormLiftCore F)‖ ^ 2 = _ at hn
  have hd := (cuspHorizontalAverage_deriv_integrable_and_le (cuspTraceFreeCore F)).2
  rw [coreGradient_cuspTraceFreeCore] at hd
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  linarith

end GapFamily.Analytic
