import GapFamily.Analytic.Bessel.BesselCoshMajorant
import GapFamily.Analytic.Eisenstein.EisensteinNonconstantBesselCosh
import GapFamily.Analytic.Foundation.AnalyticDominatedIntegral
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Analysis.SpecialFunctions.Exponential

/-! The actual complex-order cosh integral, in scalar and compact-argument norm. -/
noncomputable section
namespace GapFamily.Analytic.BesselCoshOrder
open Set Filter MeasureTheory
open scoped Topology

/-- The literal cosh-integral kernel, with the source's order-zero normalization. -/
def integrand (κ : ℂ) (t u : ℝ) : ℂ :=
  Complex.exp (-(t : ℂ) * (Real.cosh u : ℂ)) * Complex.cosh (κ * (u : ℂ))

/-- The actual complex-order Bessel cosh integral on the positive half-line. -/
def besselK (κ : ℂ) (t : ℝ) : ℂ := ∫ u : ℝ in Ioi 0, integrand κ t u

/-- The ordinary real argument coordinate on the compact observation interval. -/
def argumentOn (a b : ℝ) : C(Icc a b, ℂ) :=
  ⟨fun t => (t.val : ℂ), Complex.continuous_ofReal.comp continuous_subtype_val⟩

/-- The actual decaying exponential, as a compact continuous function of its argument. -/
def amplitudeOn (a b u : ℝ) : C(Icc a b, ℂ) :=
  NormedSpace.exp (-(Real.cosh u : ℂ) • argumentOn a b)

/-- The exact complex-order integrand in the compact supremum-norm Banach space. -/
def integrandOn (a b : ℝ) (κ : ℂ) (u : ℝ) : C(Icc a b, ℂ) :=
  Complex.cosh (κ * (u : ℂ)) • amplitudeOn a b u

/-- Evaluation of the compact exponential is its literal scalar exponential. -/
theorem amplitudeOn_apply (a b u : ℝ) (t : Icc a b) :
    amplitudeOn a b u t = Complex.exp (-(t.val : ℂ) * (Real.cosh u : ℂ)) := by
  have h := NormedSpace.map_exp (ContinuousMap.evalAlgHom ℂ ℂ t)
    (ContinuousMap.evalCLM ℂ t).continuous (-(Real.cosh u : ℂ) • argumentOn a b)
  simpa only [amplitudeOn, Complex.exp_eq_exp_ℂ, ContinuousMap.evalAlgHom_apply,
    ContinuousMap.smul_apply, smul_eq_mul, argumentOn, ContinuousMap.coe_mk,
    neg_mul, mul_neg, mul_comm] using h

/-- The compact integrand is exactly the scalar cosh kernel at every observation. -/
theorem integrandOn_apply (a b : ℝ) (κ : ℂ) (u : ℝ) (t : Icc a b) :
    integrandOn a b κ u t = integrand κ t.val u := by
  simp only [integrandOn, ContinuousMap.smul_apply, smul_eq_mul, amplitudeOn_apply,
    integrand, mul_comm]

/-- The actual compact integrand is norm continuous in the integration variable. -/
theorem integrandOn_continuous (a b : ℝ) (κ : ℂ) :
    Continuous (integrandOn a b κ) := by
  have hA : Continuous (amplitudeOn a b) :=
    NormedSpace.exp_continuous.comp
      (((Complex.continuous_ofReal.comp Real.continuous_cosh).neg).smul continuous_const)
  exact (Complex.continuous_cosh.comp
    (continuous_const.mul Complex.continuous_ofReal)).smul hA

/-- Each genuine compact integrand slice is entire in the complex order. -/
theorem integrandOn_analyticAt (a b u : ℝ) (κ : ℂ) :
    AnalyticAt ℂ (fun w => integrandOn a b w u) κ := by
  exact (Complex.analyticAt_cosh.comp (analyticAt_id.mul analyticAt_const)).smul analyticAt_const

/-- The explicit scalar Gaussian majorant bounds the actual compact norm. -/
theorem norm_integrandOn_le_majorant (a b : ℝ) (ha : 0 < a)
    {κ : ℂ} {R u : ℝ} (hκ : ‖κ‖ ≤ R) (hu : 0 ≤ u) :
    ‖integrandOn a b κ u‖ ≤ majorant a R u := by
  apply (ContinuousMap.norm_le _ (by unfold majorant; positivity)).mpr
  intro t
  rw [integrandOn_apply]
  exact norm_integrand_le_majorant ha t.property.1 hκ hu

/-- Ordinary Bochner convergence of the actual compact-argument kernel. -/
theorem integrandOn_integrable (a b : ℝ) (ha : 0 < a) (κ : ℂ) :
    IntegrableOn (integrandOn a b κ) (Ioi 0) := by
  apply (majorant_integrable (R := ‖κ‖) ha).mono'
    (integrandOn_continuous a b κ).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  exact norm_integrandOn_le_majorant a b ha le_rfl hu.le

/-- Ordinary scalar convergence at every positive real argument and complex order. -/
theorem integrand_integrable (κ : ℂ) {t : ℝ} (ht : 0 < t) :
    IntegrableOn (integrand κ t) (Ioi 0) := by
  let p : Icc t t := ⟨t, le_rfl, le_rfl⟩
  have h := (ContinuousMap.evalCLM ℂ p).integrable_comp (integrandOn_integrable t t ht κ)
  change Integrable (fun u : ℝ => integrand κ t u) (volume.restrict (Ioi 0))
  simpa only [ContinuousMap.evalCLM_apply, integrandOn_apply, p] using h

/-- The actual cosh integral with values in the argument-interval supremum norm. -/
def besselKOn (a b : ℝ) (κ : ℂ) : C(Icc a b, ℂ) :=
  ∫ u : ℝ in Ioi 0, integrandOn a b κ u

/-- Evaluation commutes with the genuinely integrable compact-argument cosh integral. -/
theorem besselKOn_apply (a b : ℝ) (ha : 0 < a) (κ : ℂ) (t : Icc a b) :
    besselKOn a b κ t = besselK κ t.val := by
  rw [besselKOn, ContinuousMap.integral_apply (integrandOn_integrable a b ha κ)]
  simp only [integrandOn_apply, besselK]

/-- Entire order dependence in the actual C([a,b]) norm, with a positive lower argument. -/
theorem besselKOn_analyticAt (a b : ℝ) (ha : 0 < a) (κ0 : ℂ) :
    AnalyticAt ℂ (besselKOn a b) κ0 := by
  apply DominatedAnalytic.analyticAt_integral_of_dominated (r := 1)
    (bound := majorant a (‖κ0‖ + 1)) (by norm_num)
  · intro κ _
    exact (integrandOn_continuous a b κ).aestronglyMeasurable
  · exact Eventually.of_forall fun u κ _ => integrandOn_analyticAt a b u κ
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    intro κ hκ
    apply norm_integrandOn_le_majorant a b ha _ hu.le
    have hd : ‖κ - κ0‖ < 1 := by simpa only [Metric.mem_ball, dist_eq_norm] using hκ
    exact (norm_le_norm_sub_add κ κ0).trans (by linarith)
  · exact majorant_integrable ha

/-- Order zero is exactly the source's original ordinary K0 integral. -/
theorem besselK_zero (t : ℝ) : besselK 0 t = (GapFamily.Analytic.besselK0 t : ℂ) := by
  rw [besselK, GapFamily.Analytic.besselK0_eq_coshIntegral]
  simp only [integrand, zero_mul, Complex.cosh_zero, mul_one]
  have hf : (fun u : ℝ => Complex.exp (-(t : ℂ) * (Real.cosh u : ℂ))) =
      (fun u : ℝ => (Real.exp (-t * Real.cosh u) : ℂ)) := by
    funext u
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    rfl
  rw [hf, integral_complex_ofReal]

end GapFamily.Analytic.BesselCoshOrder
