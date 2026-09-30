import GapFamily.Analytic.Cusp.Scalar.CuspConstantResponseEnergy
import GapFamily.Analytic.Cusp.Scalar.CuspScalarFormBasic
import GapFamily.Analytic.Cusp.Scalar.CuspConstantResponseMass
import GapFamily.Analytic.Cusp.Profile.CuspProfileForm

/-! The actual constant-source response as a vector in the closed scalar cusp form space. -/
noncomputable section
namespace GapFamily.Analytic
open Set MeasureTheory Filter ModularGradient
open scoped Topology ContDiff

/-- The actual physical response is smooth on the whole positive height axis. -/
theorem cuspConstantPhysicalResponse_contDiffOn {κ : ℂ} (hκ : κ ≠ -(1 / 2 : ℂ)) :
    ContDiffOn ℝ ∞ (cuspConstantPhysicalResponse κ) (Ioi 0) := by
  have hv : ContDiff ℝ ∞ (cuspConstantLogResponse κ) :=
    (cuspConstantLogResponse_contDiff hκ).of_le le_top
  intro y hy
  exact ((Real.contDiffAt_sqrt (ne_of_gt hy)).smul
    (hv.contDiffAt.comp y (Real.contDiffAt_log.mpr (ne_of_gt hy)))).contDiffWithinAt

/-- The ordinary physical mass density is integrable on the actual cusp half-line. -/
theorem cuspConstantPhysicalResponse_mass_density_integrable {κ : ℂ} (hκ : 0 < κ.re) :
    IntegrableOn (fun y => ‖cuspConstantPhysicalResponse κ y‖ ^ 2 / y ^ 2) (Ioi 1) := by
  have hi : IntegrableOn (fun t => ‖cuspConstantLogResponse κ t‖ ^ 2) (Ici (Real.log 1)) := by
    rw [Real.log_one, integrableOn_Ici_iff_integrableOn_Ioi]
    exact (cuspConstantLogResponse_memLp hκ).norm.integrable_sq
  exact ((integrableOn_cuspLift_norm_sq_iff (cuspConstantLogResponse κ) zero_lt_one).mpr hi).mono_set
    Ioi_subset_Ici_self

/-- The derivative density is integrable on the same open half-line. -/
theorem cuspConstantPhysicalResponse_energy_density_integrable {κ : ℂ} (hκ : 0 < κ.re) :
    IntegrableOn (fun y => ‖deriv (cuspConstantPhysicalResponse κ) y‖ ^ 2) (Ioi 1) :=
  (cuspConstantPhysicalResponse_deriv_sq_integrable hκ).mono_set Ioi_subset_Ici_self

private theorem constant_form_param_ne {κ : ℂ} (hκ : 0 < κ.re) : κ ≠ -(1 / 2 : ℂ) := by
  intro h
  subst κ
  norm_num at hκ

/-- The genuine completed modular form obtained from the literal constant-source profile. -/
def cuspConstantForm {κ : ℂ} (hκ : 0 < κ.re) : FormDomain :=
  cuspProfileForm (cuspConstantPhysicalResponse κ)
    (cuspConstantPhysicalResponse_contDiffOn (constant_form_param_ne hκ))
    (cuspConstantPhysicalResponse_one κ)
    (cuspConstantPhysicalResponse_mass_density_integrable hκ)
    (cuspConstantPhysicalResponse_energy_density_integrable hκ)

/-- The explicit smooth compact cusp approximants converge in the actual form norm. -/
theorem cuspConstantForm_core_tendsto {κ : ℂ} (hκ : 0 < κ.re) :
    Tendsto (cuspProfileFormSequence (cuspConstantPhysicalResponse κ)
      (cuspConstantPhysicalResponse_contDiffOn (constant_form_param_ne hκ))) atTop
      (𝓝 (cuspConstantForm hκ)) :=
  cuspProfileForm_core_tendsto _ _ _ _ _

/-- Membership is obtained by closedness from genuine compact scalar cusp forms. -/
theorem cuspConstantForm_mem_cuspScalarForm {κ : ℂ} (hκ : 0 < κ.re) :
    cuspConstantForm hκ ∈ cuspScalarForm := by
  apply cuspScalarForm_mem_of_tendsto ?_ (cuspConstantForm_core_tendsto hκ)
  exact Eventually.of_forall fun n => cuspProfileCore_mem_cuspScalarForm
    (cuspProfileApproximation (cuspConstantPhysicalResponse κ) n)
    (cuspProfileApproximation_contDiff
      (cuspConstantPhysicalResponse_contDiffOn (constant_form_param_ne hκ)) n)
    (cuspProfileApproximation_hasCompactSupport _ n)
    (cuspProfileApproximation_tsupport_subset _ n)

/-- The actual scalar cusp form vector, with no assumed resolvent or domain interface. -/
def cuspConstantScalarForm {κ : ℂ} (hκ : 0 < κ.re) : cuspScalarForm :=
  ⟨cuspConstantForm hκ, cuspConstantForm_mem_cuspScalarForm hκ⟩

/-- Its actual ambient representative is the response above height one and zero below. -/
theorem cuspConstantForm_embedding_ae {κ : ℂ} (hκ : 0 < κ.re) :
    formEmbedding (cuspConstantForm hκ) =ᵐ[modularMeasure]
      (fun τ : UpperHalfPlane => if 1 < τ.im then cuspConstantPhysicalResponse κ τ.im else 0) :=
  cuspProfileForm_embedding_ae _ _ _ _ _

/-- The actual horizontal gradient component vanishes. -/
theorem cuspConstantForm_gradient_fst_eq_zero {κ : ℂ} (hκ : 0 < κ.re) :
    (formGradient (cuspConstantForm hκ)).ofLp.1 = 0 :=
  cuspProfileForm_gradient_fst_eq_zero _ _ _ _ _

/-- The actual vertical closed-gradient component is the literal physical derivative. -/
theorem cuspConstantForm_gradient_snd_ae {κ : ℂ} (hκ : 0 < κ.re) :
    (formGradient (cuspConstantForm hκ)).ofLp.2 =ᵐ[modularMeasure]
      (fun τ : UpperHalfPlane => if 1 < τ.im then
        (τ.im : ℂ) * deriv (cuspConstantPhysicalResponse κ) τ.im else 0) :=
  cuspProfileForm_gradient_snd_ae _ _ _ _ _

/-- The actual ambient mass is the already integrable logarithmic mass. -/
theorem cuspConstantForm_value_norm_sq {κ : ℂ} (hκ : 0 < κ.re) :
    ‖formEmbedding (cuspConstantForm hκ)‖ ^ 2 =
      ∫ t : ℝ in Ioi 0, ‖cuspConstantLogResponse κ t‖ ^ 2 := by
  change ‖formEmbedding (cuspProfileForm _ _ _ _ _)‖ ^ 2 = _
  rw [cuspProfileForm_value_norm_sq, integral_cuspConstantPhysicalResponse_norm_sq_div,
    integral_cuspConstantPhysicalResponse_norm_sq hκ]

/-- Exact closed-gradient energy of the actual form vector. -/
theorem cuspConstantForm_gradient_norm_sq {κ : ℂ} (hκ : 0 < κ.re) :
    ‖formGradient (cuspConstantForm hκ)‖ ^ 2 =
      1 / (2 * κ.re * ‖κ + 1 / 2‖ ^ 2) := by
  change ‖formGradient (cuspProfileForm _ _ _ _ _)‖ ^ 2 = _
  rw [cuspProfileForm_gradient_norm_sq]
  simpa only [integral_Ici_eq_integral_Ioi] using
    integral_cuspConstantPhysicalResponse_deriv_sq hκ

/-- Exact form norm: finite mass plus the explicitly evaluated finite energy. -/
theorem cuspConstantForm_norm_sq {κ : ℂ} (hκ : 0 < κ.re) :
    ‖cuspConstantForm hκ‖ ^ 2 =
      (∫ t : ℝ in Ioi 0, ‖cuspConstantLogResponse κ t‖ ^ 2) +
        1 / (2 * κ.re * ‖κ + 1 / 2‖ ^ 2) := by
  rw [formDomain_norm_sq, cuspConstantForm_value_norm_sq hκ,
    cuspConstantForm_gradient_norm_sq hκ]

/-- The same exact norm formula in the actual closed scalar form subspace. -/
theorem cuspConstantScalarForm_norm_sq {κ : ℂ} (hκ : 0 < κ.re) :
    ‖cuspConstantScalarForm hκ‖ ^ 2 =
      (∫ t : ℝ in Ioi 0, ‖cuspConstantLogResponse κ t‖ ^ 2) +
        1 / (2 * κ.re * ‖κ + 1 / 2‖ ^ 2) :=
  cuspConstantForm_norm_sq hκ

/-- The genuine scalar form vector satisfies the actual zero-trace condition. -/
@[simp] theorem cuspConstantForm_trace_eq_zero {κ : ℂ} (hκ : 0 < κ.re) :
    cuspAverageTrace (cuspConstantForm hκ) = 0 :=
  cuspProfileForm_trace_eq_zero _ _ _ _ _

/-- At the removable physical parameter this actual form vector has squared norm three. -/
theorem cuspConstantForm_half_norm_sq :
    ‖cuspConstantForm (κ := (1 / 2 : ℂ)) (by norm_num)‖ ^ 2 = 3 := by
  rw [cuspConstantForm_norm_sq, cuspConstantLogResponse_half_mass]
  norm_num

/-- The removable vector has squared norm three in the scalar form space itself. -/
theorem cuspConstantScalarForm_half_norm_sq :
    ‖cuspConstantScalarForm (κ := (1 / 2 : ℂ)) (by norm_num)‖ ^ 2 = 3 :=
  cuspConstantForm_half_norm_sq

/-- In particular the physical logarithm determines a nonzero vector in the actual scalar form space. -/
theorem cuspConstantScalarForm_half_ne_zero :
    cuspConstantScalarForm (κ := (1 / 2 : ℂ)) (by norm_num) ≠ 0 := by
  intro h
  have hc : cuspConstantForm (κ := (1 / 2 : ℂ)) (by norm_num) = 0 := congrArg Subtype.val h
  have hn := cuspConstantForm_half_norm_sq
  rw [hc] at hn
  norm_num at hn

end GapFamily.Analytic
