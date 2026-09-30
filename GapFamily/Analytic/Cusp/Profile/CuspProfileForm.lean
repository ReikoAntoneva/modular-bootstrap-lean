import GapFamily.Analytic.Cusp.Profile.CuspProfileFormCauchy
import GapFamily.Analytic.Cusp.Profile.CuspProfileFormLimit
import GapFamily.Analytic.Cusp.Profile.CuspProfileFormNorm
import GapFamily.Analytic.Cusp.Scalar.CuspScalarFormTrace

/-!
# Actual zero-trace scalar cusp profiles in the closed form domain

The explicit compact smooth profile approximants converge in the actual
modular gradient graph. Their limit has the clipped scalar value and vertical
gradient representatives, exact mass and energy, and zero boundary trace.
-/

noncomputable section
namespace GapFamily.Analytic
open Set Filter MeasureTheory UpperHalfPlane ModularGradient
open scoped Topology ContDiff

variable (b : ℝ → ℂ) (hb : ContDiffOn ℝ ∞ b (Ioi 0)) (hb1 : b 1 = 0)
  (hv : IntegrableOn (fun y => ‖b y‖ ^ 2 / y ^ 2) (Ioi 1))
  (hd : IntegrableOn (fun y => ‖deriv b y‖ ^ 2) (Ioi 1))

/-- The genuine graph-closure lift of a finite-energy zero-trace profile. -/
def cuspProfileForm : FormDomain :=
  (exists_cuspProfileFormSequence_tendsto b hb hb1 hv hd).choose

theorem cuspProfileForm_core_tendsto :
    Tendsto (cuspProfileFormSequence b hb) atTop (𝓝 (cuspProfileForm b hb hb1 hv hd)) :=
  (exists_cuspProfileFormSequence_tendsto b hb hb1 hv hd).choose_spec

theorem cuspProfileForm_embedding_ae :
    formEmbedding (cuspProfileForm b hb hb1 hv hd) =ᵐ[modularMeasure]
      (fun τ : UpperHalfPlane => if 1 < τ.im then b τ.im else 0) := by
  apply cuspProfile_Lp_limit_ae
    (f := fun n => formEmbedding (cuspProfileFormSequence b hb n))
    (g := fun n τ => cuspProfileApproximation b n τ.im)
  · exact formEmbedding.continuous.continuousAt.tendsto.comp
      (cuspProfileForm_core_tendsto b hb hb1 hv hd)
  · intro n
    exact cuspProfileCore_value_ae _ _ _ _
  · intro τ
    exact cuspProfileApproximation_value_tendsto b τ.im

theorem cuspProfileForm_gradient_fst_eq_zero :
    (formGradient (cuspProfileForm b hb hb1 hv hd)).ofLp.1 = 0 := by
  have hc : Continuous (fun u : FormDomain => (formGradient u).ofLp.1) :=
    (WithLp.fstL 2 ℂ ModularHilbert ModularHilbert).continuous.comp formGradient.continuous
  have ht := hc.continuousAt.tendsto.comp (cuspProfileForm_core_tendsto b hb hb1 hv hd)
  have heq (n : ℕ) : (formGradient (cuspProfileFormSequence b hb n)).ofLp.1 = 0 := by
    simp only [cuspProfileFormSequence, formGradient_coreForm, coreGradient_fst]
    exact cuspProfileCore_xComponent_eq_zero _ _ _ _
  have ht0 : Tendsto (fun n => (formGradient (cuspProfileFormSequence b hb n)).ofLp.1)
      atTop (𝓝 (0 : ModularHilbert)) := by simpa only [heq] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ModularHilbert)) atTop (𝓝 0))
  exact tendsto_nhds_unique ht ht0

theorem cuspProfileForm_gradient_snd_ae :
    (formGradient (cuspProfileForm b hb hb1 hv hd)).ofLp.2 =ᵐ[modularMeasure]
      (fun τ : UpperHalfPlane => if 1 < τ.im then (τ.im : ℂ) * deriv b τ.im else 0) := by
  have hc : Continuous (fun u : FormDomain => (formGradient u).ofLp.2) :=
    (WithLp.sndL 2 ℂ ModularHilbert ModularHilbert).continuous.comp formGradient.continuous
  apply cuspProfile_Lp_limit_ae
    (f := fun n => (formGradient (cuspProfileFormSequence b hb n)).ofLp.2)
    (g := fun n τ => (τ.im : ℂ) * deriv (cuspProfileApproximation b n) τ.im)
  · exact hc.continuousAt.tendsto.comp (cuspProfileForm_core_tendsto b hb hb1 hv hd)
  · intro n
    simpa only [cuspProfileFormSequence, formGradient_coreForm, coreGradient_snd] using
      cuspProfileCore_yComponent_ae (cuspProfileApproximation b n)
        (cuspProfileApproximation_contDiff hb n)
        (cuspProfileApproximation_hasCompactSupport b n)
        (cuspProfileApproximation_tsupport_subset b n)
  · intro τ
    convert (cuspProfileApproximation_deriv_tendsto b τ.im).const_mul (τ.im : ℂ) using 1
    split_ifs <;> simp

theorem cuspProfileForm_value_norm_sq :
    ‖formEmbedding (cuspProfileForm b hb hb1 hv hd)‖ ^ 2 =
      ∫ y : ℝ in Ioi 1, ‖b y‖ ^ 2 / y ^ 2 :=
  (cuspProfile_form_value_norm_sq_of_ae _ b
    (cuspProfileForm_embedding_ae b hb hb1 hv hd)).2

theorem cuspProfileForm_gradient_norm_sq :
    ‖formGradient (cuspProfileForm b hb hb1 hv hd)‖ ^ 2 =
      ∫ y : ℝ in Ioi 1, ‖deriv b y‖ ^ 2 :=
  (cuspProfile_form_gradient_norm_sq_of_ae _ b
    (cuspProfileForm_gradient_fst_eq_zero b hb hb1 hv hd)
    (cuspProfileForm_gradient_snd_ae b hb hb1 hv hd)).2

theorem cuspProfileForm_norm_sq :
    ‖cuspProfileForm b hb hb1 hv hd‖ ^ 2 =
      (∫ y : ℝ in Ioi 1, ‖b y‖ ^ 2 / y ^ 2) +
        ∫ y : ℝ in Ioi 1, ‖deriv b y‖ ^ 2 := by
  rw [formDomain_norm_sq, cuspProfileForm_value_norm_sq, cuspProfileForm_gradient_norm_sq]

@[simp] theorem cuspProfileForm_trace_eq_zero :
    cuspAverageTrace (cuspProfileForm b hb hb1 hv hd) = 0 := by
  have ht := cuspAverageTrace.continuous.continuousAt.tendsto.comp
    (cuspProfileForm_core_tendsto b hb hb1 hv hd)
  have heq (n : ℕ) : cuspAverageTrace (cuspProfileFormSequence b hb n) = 0 :=
    cuspAverageTrace_cuspProfileCore _ _ _ _
  have ht0 : Tendsto (fun n => cuspAverageTrace (cuspProfileFormSequence b hb n)) atTop
      (𝓝 (0 : ℂ)) := by simpa only [heq] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℂ)) atTop (𝓝 0))
  exact tendsto_nhds_unique ht ht0

end GapFamily.Analytic
