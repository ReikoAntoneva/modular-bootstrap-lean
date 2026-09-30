import GapFamily.Analytic.Cusp.Green.CuspGreenSmoothEnergy
import GapFamily.Analytic.Cusp.Green.CuspGreenSolutionRepresentation
import GapFamily.Analytic.Cusp.Profile.CuspLogCoordinateEnergy
import GapFamily.Analytic.Cusp.Profile.CuspProfileForm
import GapFamily.Analytic.Cusp.Scalar.CuspScalarFormBasic

/-!
# The actual smooth-source Green response in the scalar cusp form space

The logarithmic response becomes a smooth finite-energy physical profile with
zero boundary value. Its completed form vector has the literal Green integral
as its almost-everywhere representative on the whole cusp half-line.
-/

noncomputable section

namespace GapFamily.Analytic
open Set Filter MeasureTheory ModularGradient
open scoped ContDiff Topology

private theorem cuspGreenSmoothOutgoing_eq_integral (T : ℝ) (κ : ℂ) {f : ℝ → ℂ}
    (hf : Continuous f) :
    cuspGreenSmoothOutgoing T κ f = ∫ u in (0 : ℝ)..T,
      ((Complex.exp (κ * (u : ℂ)) - Complex.exp (-κ * ((u : ℂ) - 2 * (0 : ℂ)))) /
        (2 * κ)) * f u := by
  have hp : Continuous (fun u : ℝ => Complex.exp (κ * (u : ℂ)) * f u) := by fun_prop
  have hm : Continuous (fun u : ℝ => Complex.exp (-κ * (u : ℂ)) * f u) := by fun_prop
  rw [cuspGreenSmoothOutgoing,
    ← intervalIntegral.integral_sub (hp.intervalIntegrable 0 T) (hm.intervalIntegrable 0 T),
    ← intervalIntegral.integral_div]
  apply intervalIntegral.integral_congr
  intro u _
  simp only [mul_zero, sub_zero]
  ring

/-- On the whole positive half-line the finite formula is the literal Green integral. -/
theorem cuspGreenSolutionFormula_eq_solution_of_support {T : ℝ} (hT : 0 ≤ T)
    {κ : ℂ} (hκ : κ ≠ 0) {f : ℝ → ℂ} (hf : Continuous f)
    (hs : tsupport f ⊆ Ioo 0 T) {t : ℝ} (ht : 0 ≤ t) :
    cuspGreenSolutionFormula 0 T κ f t = cuspGreenSolution 0 κ f t := by
  have hfT : ∀ u, T < u → f u = 0 :=
    fun u hu => cuspGreenSmoothSource_zero_above hs hu.le
  by_cases htT : t ≤ T
  · exact (cuspGreenSolution_eq_formula 0 T t ht htT hκ hf hfT).symm
  · have hTt : T ≤ t := (lt_of_not_ge htT).le
    rw [cuspGreenSolutionFormula_outgoing_of_support hTt κ hf hs,
      cuspGreenSolution_eq_outgoing 0 T t hT hTt hκ hfT,
      cuspGreenSmoothOutgoing_eq_integral T κ hf]
    simp only [Complex.ofReal_zero]

/-- The actual physical cusp profile of the smooth compact-source Green response. -/
def cuspGreenSmoothPhysical (T : ℝ) (κ : ℂ) (f : ℝ → ℂ) : ℝ → ℂ :=
  cuspLift (cuspGreenSolutionFormula 0 T κ f)

theorem cuspGreenSmoothPhysical_contDiffOn (T : ℝ) {κ : ℂ} (hκ : κ ≠ 0)
    {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) :
    ContDiffOn ℝ ∞ (cuspGreenSmoothPhysical T κ f) (Ioi 0) := by
  have hv := contDiff_cuspGreenSolutionFormula 0 T hκ hf
  intro y hy
  exact ((Real.contDiffAt_sqrt (ne_of_gt hy)).smul
    (hv.contDiffAt.comp y (Real.contDiffAt_log.mpr (ne_of_gt hy)))).contDiffWithinAt

@[simp] theorem cuspGreenSmoothPhysical_one (T : ℝ) (κ : ℂ) (f : ℝ → ℂ) :
    cuspGreenSmoothPhysical T κ f 1 = 0 := by
  simp [cuspGreenSmoothPhysical, cuspLift, cuspGreenSolutionFormula_boundary]

theorem cuspGreenSmoothPhysical_mass_integrable {T : ℝ} (hT : 0 ≤ T)
    {κ : ℂ} (hκ : 0 < κ.re) {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f)
    (hs : tsupport f ⊆ Ioo 0 T) :
    IntegrableOn (fun y => ‖cuspGreenSmoothPhysical T κ f y‖ ^ 2 / y ^ 2) (Ioi 1) := by
  have hi : IntegrableOn (fun t => ‖cuspGreenSolutionFormula 0 T κ f t‖ ^ 2)
      (Ici (Real.log 1)) := by
    rw [Real.log_one, integrableOn_Ici_iff_integrableOn_Ioi]
    exact cuspGreenSolutionFormula_mass_integrable hT hκ hf hs
  exact ((integrableOn_cuspLift_norm_sq_iff _ zero_lt_one).mpr hi).mono_set
    Ioi_subset_Ici_self

theorem cuspGreenSmoothPhysical_energy_integrable {T : ℝ} (hT : 0 ≤ T)
    {κ : ℂ} (hκ : 0 < κ.re) {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f)
    (hs : tsupport f ⊆ Ioo 0 T) :
    IntegrableOn (fun y => ‖deriv (cuspGreenSmoothPhysical T κ f) y‖ ^ 2) (Ioi 1) := by
  have hk : κ ≠ 0 := by intro h; simp [h] at hκ
  have hv : Differentiable ℝ (cuspGreenSolutionFormula 0 T κ f) :=
    (contDiff_cuspGreenSolutionFormula 0 T hk hf).differentiable (by simp)
  exact (integrableOn_deriv_cuspLift_norm_sq_iff hv).mpr
    (cuspGreenSolutionFormula_shifted_energy_integrable hT hκ hf hs)

/-- The actual response defines a completed form vector, with all constructor hypotheses proved. -/
def cuspGreenSmoothForm {T : ℝ} (hT : 0 ≤ T) {κ : ℂ} (hκ : 0 < κ.re)
    {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) (hs : tsupport f ⊆ Ioo 0 T) : FormDomain :=
  cuspProfileForm (cuspGreenSmoothPhysical T κ f)
    (cuspGreenSmoothPhysical_contDiffOn T (by intro h; simp [h] at hκ) hf)
    (cuspGreenSmoothPhysical_one T κ f)
    (cuspGreenSmoothPhysical_mass_integrable hT hκ hf hs)
    (cuspGreenSmoothPhysical_energy_integrable hT hκ hf hs)

/-- Membership in the actual closed scalar cusp form space follows from its compact core sequence. -/
theorem cuspGreenSmoothForm_mem_cuspScalarForm {T : ℝ} (hT : 0 ≤ T)
    {κ : ℂ} (hκ : 0 < κ.re) {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f)
    (hs : tsupport f ⊆ Ioo 0 T) : cuspGreenSmoothForm hT hκ hf hs ∈ cuspScalarForm := by
  have hk : κ ≠ 0 := by intro h; simp [h] at hκ
  have hb := cuspGreenSmoothPhysical_contDiffOn T hk hf
  apply cuspScalarForm_mem_of_tendsto ?_
    (cuspProfileForm_core_tendsto (cuspGreenSmoothPhysical T κ f) hb
      (cuspGreenSmoothPhysical_one T κ f)
      (cuspGreenSmoothPhysical_mass_integrable hT hκ hf hs)
      (cuspGreenSmoothPhysical_energy_integrable hT hκ hf hs))
  exact Eventually.of_forall fun n => cuspProfileCore_mem_cuspScalarForm
    (cuspProfileApproximation (cuspGreenSmoothPhysical T κ f) n)
    (cuspProfileApproximation_contDiff hb n)
    (cuspProfileApproximation_hasCompactSupport _ n)
    (cuspProfileApproximation_tsupport_subset _ n)

/-- Its physical representative is the same literal Green integral transported by the cusp lift. -/
theorem cuspGreenSmoothForm_embedding_ae {T : ℝ} (hT : 0 ≤ T)
    {κ : ℂ} (hκ : 0 < κ.re) {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f)
    (hs : tsupport f ⊆ Ioo 0 T) :
    formEmbedding (cuspGreenSmoothForm hT hκ hf hs) =ᵐ[modularMeasure]
      (fun z : UpperHalfPlane => if 1 < z.im then
        Real.sqrt z.im • cuspGreenSolution 0 κ f (Real.log z.im) else 0) := by
  have hk : κ ≠ 0 := by intro h; simp [h] at hκ
  have he := cuspProfileForm_embedding_ae (cuspGreenSmoothPhysical T κ f)
    (cuspGreenSmoothPhysical_contDiffOn T hk hf)
    (cuspGreenSmoothPhysical_one T κ f)
    (cuspGreenSmoothPhysical_mass_integrable hT hκ hf hs)
    (cuspGreenSmoothPhysical_energy_integrable hT hκ hf hs)
  filter_upwards [he] with z hz
  unfold cuspGreenSmoothForm
  rw [hz]
  split_ifs with hy
  · unfold cuspGreenSmoothPhysical cuspLift
    rw [cuspGreenSolutionFormula_eq_solution_of_support hT hk hf.continuous hs
      (Real.log_nonneg hy.le)]
  · rfl

end GapFamily.Analytic
