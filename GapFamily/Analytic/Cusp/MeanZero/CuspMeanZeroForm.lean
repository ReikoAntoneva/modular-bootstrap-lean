import GapFamily.Analytic.Cusp.Fourier.CuspHorizontalHilbertHeight

/-!
# The closed form subspace with zero horizontal cusp average

The condition is the kernel of the actual bounded horizontal average at height
one. Height coherence propagates this condition to every higher cusp, where the
full restriction therefore satisfies the previously proved residual estimate.
No projection or range characterization of horizontal averaging is assumed.
-/

noncomputable section

namespace GapFamily.Analytic

open MeasureTheory Set UpperHalfPlane ModularGradient

/-- The actual baseline horizontal average of a completed form-domain value. -/
def cuspFormAverage : FormDomain →L[ℂ] cuspHilbert 1 :=
  ((cuspAverage 1 le_rfl).comp (cuspRestrict 1)).comp formEmbedding

/-- On the actual smooth automorphic core this is the ordinary horizontal integral. -/
theorem cuspFormAverage_core_ae (F : smoothCore) :
    cuspFormAverage (coreForm F) =ᵐ[modularMeasure.restrict {τ | 1 < τ.im}]
      (fun τ : UpperHalfPlane => cuspHorizontalAverage F.val τ.im) :=
  cuspAverage_core_ae 1 le_rfl F

/-- Completed finite-energy functions whose horizontal average vanishes above one. -/
def cuspMeanZeroForm : Submodule ℂ FormDomain := cuspFormAverage.ker

instance cuspMeanZeroForm_normedSpace : NormedSpace ℂ cuspMeanZeroForm :=
  Submodule.normedSpace cuspMeanZeroForm

instance cuspMeanZeroForm_innerProductSpace : InnerProductSpace ℂ cuspMeanZeroForm :=
  Submodule.innerProductSpace (𝕜 := ℂ) (E := FormDomain) cuspMeanZeroForm

theorem cuspMeanZeroForm_isClosed : IsClosed (cuspMeanZeroForm : Set FormDomain) :=
  cuspFormAverage.isClosed_ker

instance cuspMeanZeroForm_completeSpace : CompleteSpace cuspMeanZeroForm :=
  cuspMeanZeroForm_isClosed.completeSpace_coe

theorem mem_cuspMeanZeroForm (u : FormDomain) :
    u ∈ cuspMeanZeroForm ↔ cuspAverage 1 le_rfl (cuspRestrict 1 (formEmbedding u)) = 0 :=
  Iff.rfl

/-- Inclusion of the constrained form space into the actual modular Hilbert space. -/
def meanZeroCuspEmbedding : cuspMeanZeroForm →L[ℂ] ModularHilbert :=
  formEmbedding.comp cuspMeanZeroForm.subtypeL

theorem meanZeroCuspEmbedding_apply (u : cuspMeanZeroForm) :
    meanZeroCuspEmbedding u = formEmbedding (u : FormDomain) := rfl

theorem meanZeroCuspEmbedding_injective : Function.Injective meanZeroCuspEmbedding :=
  formEmbedding_injective.comp Subtype.val_injective

/-- A zero baseline average remains zero on every higher cusp. -/
theorem meanZeroCusp_average_eq_zero (H : ℝ) (hH : 1 ≤ H) (u : cuspMeanZeroForm) :
    cuspAverage H hH (cuspRestrict H (meanZeroCuspEmbedding u)) = 0 := by
  have hu : cuspAverage 1 le_rfl
      (cuspRestrict 1 (meanZeroCuspEmbedding u)) = 0 := u.property
  have h := cuspHeightRestrict_average 1 H le_rfl hH
    (cuspRestrict 1 (meanZeroCuspEmbedding u))
  rw [hu, map_zero, cuspHeightRestrict_cuspRestrict] at h
  exact h.symm

/-- On the constrained form space, the entire cusp restriction is the residual. -/
theorem meanZeroCusp_restrict_eq_formResidual (H : ℝ) (hH : 1 ≤ H)
    (u : cuspMeanZeroForm) :
    cuspRestrict H (meanZeroCuspEmbedding u) = cuspFormResidual H hH (u : FormDomain) := by
  change cuspRestrict H (meanZeroCuspEmbedding u) =
    cuspResidual H hH (cuspRestrict H (meanZeroCuspEmbedding u))
  rw [cuspResidual_apply, meanZeroCusp_average_eq_zero, sub_zero]

/-- The full high-cusp mass is controlled by the actual closed-gradient energy. -/
theorem meanZeroCusp_restrict_energy_bound (H : ℝ) (hH : 1 ≤ H)
    (u : cuspMeanZeroForm) :
    ‖cuspRestrict H (meanZeroCuspEmbedding u)‖ ^ 2 ≤
      (1 / H ^ 2) * ‖formGradient (u : FormDomain)‖ ^ 2 := by
  rw [meanZeroCusp_restrict_eq_formResidual]
  exact cuspFormResidual_energy_bound H hH u

theorem meanZeroCusp_restrict_norm_le (H : ℝ) (hH : 1 ≤ H)
    (u : cuspMeanZeroForm) :
    ‖cuspRestrict H (meanZeroCuspEmbedding u)‖ ≤ (1 / H) * ‖u‖ := by
  rw [meanZeroCusp_restrict_eq_formResidual]
  exact cuspFormResidual_norm_le H hH u

/-- The full high-cusp tail, extended by zero in the ambient modular Hilbert space. -/
def meanZeroCuspTail (H : ℝ) (_hH : 1 ≤ H) : cuspMeanZeroForm →L[ℂ] ModularHilbert :=
  (cuspZeroExtension H).toContinuousLinearMap.comp
    ((cuspRestrict H).comp meanZeroCuspEmbedding)

theorem meanZeroCuspTail_apply (H : ℝ) (hH : 1 ≤ H) (u : cuspMeanZeroForm) :
    meanZeroCuspTail H hH u = cuspZeroExtend H
      (cuspRestrict H (meanZeroCuspEmbedding u)) := rfl

/-- The ambient tail has exactly the norm of the literal cusp restriction. -/
theorem meanZeroCuspTail_norm (H : ℝ) (hH : 1 ≤ H) (u : cuspMeanZeroForm) :
    ‖meanZeroCuspTail H hH u‖ = ‖cuspRestrict H (meanZeroCuspEmbedding u)‖ :=
  cuspZeroExtend_norm H _

theorem meanZeroCuspTail_energy_bound (H : ℝ) (hH : 1 ≤ H) (u : cuspMeanZeroForm) :
    ‖meanZeroCuspTail H hH u‖ ^ 2 ≤
      (1 / H ^ 2) * ‖formGradient (u : FormDomain)‖ ^ 2 := by
  rw [meanZeroCuspTail_norm]
  exact meanZeroCusp_restrict_energy_bound H hH u

theorem meanZeroCuspTail_norm_le (H : ℝ) (hH : 1 ≤ H) (u : cuspMeanZeroForm) :
    ‖meanZeroCuspTail H hH u‖ ≤ (1 / H) * ‖u‖ := by
  rw [meanZeroCuspTail_norm]
  exact meanZeroCusp_restrict_norm_le H hH u

theorem meanZeroCuspTail_opNorm_le (H : ℝ) (hH : 1 ≤ H) :
    ‖meanZeroCuspTail H hH‖ ≤ 1 / H := by
  exact @ContinuousLinearMap.opNorm_le_bound ℂ ℂ cuspMeanZeroForm ModularHilbert
    (inferInstance : SeminormedAddCommGroup cuspMeanZeroForm)
    (inferInstance : SeminormedAddCommGroup ModularHilbert) inferInstance inferInstance
    (inferInstance : NormedSpace ℂ cuspMeanZeroForm)
    (inferInstance : NormedSpace ℂ ModularHilbert) (RingHom.id ℂ)
    (meanZeroCuspTail H hH) (1 / H) (by positivity) (meanZeroCuspTail_norm_le H hH)

end GapFamily.Analytic
