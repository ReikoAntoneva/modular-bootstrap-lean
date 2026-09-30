import GapFamily.Analytic.Cusp.CuspFormDecomposition
import GapFamily.Analytic.Cusp.Profile.CuspLogCoordinate

/-!
# The actual scalar cusp quarter-energy bound

The logarithmic energy identity gives the precise quarter lower bound on compact
profiles. Actual form convergence and the bounded scalar lift extend it to the
whole closed scalar form space.
-/

noncomputable section

namespace GapFamily.Analytic

open Set Filter MeasureTheory ModularGradient
open scoped Topology ContDiff

/-- The quarter potential in the actual logarithmic energy identity. -/
theorem cuspProfileCore_quarter_mass_le_energy (b : ℝ → ℂ)
    (hb : ContDiff ℝ ∞ b) (hc : HasCompactSupport b) (hs : tsupport b ⊆ Ioi 1) :
    (1 / 4 : ℝ) * ‖value (cuspProfileCore b hb hc hs)‖ ^ 2 ≤
      ‖coreGradient (cuspProfileCore b hb hc hs)‖ ^ 2 := by
  rw [(cuspProfileCore_value_norm_sq b hb hc hs).2,
    (cuspProfileCore_gradient_norm_sq b hb hc hs).2,
    integral_cuspLogCoordinate_mass hb.continuous hc hs,
    integral_cuspLogCoordinate_energy hb hc hs]
  have hm := (cuspLogCoordinate_mass hb.continuous hc hs).2.1
  have he := (integrableOn_cuspLogCoordinate_energy hb hc hs).2
  calc
    _ = ∫ t in Ioi (0 : ℝ), ‖cuspLogCoordinate b t‖ ^ 2 / 4 := by
      rw [integral_div]
      ring
    _ ≤ _ := integral_mono (hm.div_const 4) he
      (fun t => le_add_of_nonneg_left (sq_nonneg _))

/-- The quarter bound survives the actual graph-norm profile construction. -/
theorem cuspProfileForm_quarter_mass_le_energy (b : ℝ → ℂ)
    (hb : ContDiffOn ℝ ∞ b (Ioi 0)) (hb1 : b 1 = 0)
    (hv : IntegrableOn (fun y => ‖b y‖ ^ 2 / y ^ 2) (Ioi 1))
    (hd : IntegrableOn (fun y => ‖deriv b y‖ ^ 2) (Ioi 1)) :
    (1 / 4 : ℝ) * ‖formEmbedding (cuspProfileForm b hb hb1 hv hd)‖ ^ 2 ≤
      ‖formGradient (cuspProfileForm b hb hb1 hv hd)‖ ^ 2 := by
  have hc : IsClosed {u : FormDomain | (1 / 4 : ℝ) * ‖formEmbedding u‖ ^ 2 ≤
      ‖formGradient u‖ ^ 2} := isClosed_le (by fun_prop) (by fun_prop)
  apply hc.mem_of_tendsto (cuspProfileForm_core_tendsto b hb hb1 hv hd)
  apply Eventually.of_forall
  intro n
  change (1 / 4 : ℝ) * ‖formEmbedding (cuspProfileFormSequence b hb n)‖ ^ 2 ≤ _
  simp only [cuspProfileFormSequence, formEmbedding_coreForm, formGradient_coreForm]
  exact cuspProfileCore_quarter_mass_le_energy _ _ _ _

/-- The completed scalar lift obeys the quarter mass bound without any extra premise. -/
theorem cuspScalarFormLift_quarter_mass_le_energy (u : FormDomain) :
    (1 / 4 : ℝ) * ‖formEmbedding (cuspScalarFormLift u)‖ ^ 2 ≤
      ‖formGradient (cuspScalarFormLift u)‖ ^ 2 := by
  refine coreForm_denseRange.induction_on (p := fun u : FormDomain =>
    (1 / 4 : ℝ) * ‖formEmbedding (cuspScalarFormLift u)‖ ^ 2 ≤
      ‖formGradient (cuspScalarFormLift u)‖ ^ 2) u ?_ ?_
  · exact isClosed_le (by fun_prop) (by fun_prop)
  · intro F
    rw [cuspScalarFormLift_coreForm]
    exact cuspProfileForm_quarter_mass_le_energy
      (cuspHorizontalAverage (cuspTraceFreeCore F).val)
      (contDiffOn_cuspHorizontalAverage (cuspTraceFreeCore F))
      (cuspTraceFreeCore_trace F)
      (cuspHorizontalAverage_scalar_mass_le (cuspTraceFreeCore F)).1
      (cuspHorizontalAverage_deriv_integrable_and_le (cuspTraceFreeCore F)).1

/-- The actual scalar form space has the precise free half-line threshold lower bound. -/
theorem cuspScalarForm_quarter_mass_le_energy (w : cuspScalarForm) :
    (1 / 4 : ℝ) * ‖scalarCuspEmbedding w‖ ^ 2 ≤
      ‖formGradient (w : FormDomain)‖ ^ 2 := by
  simpa only [cuspScalarFormLift_scalar, scalarCuspEmbedding_apply] using
    cuspScalarFormLift_quarter_mass_le_energy (w : FormDomain)

/-- A concrete energy bound in the complete scalar form norm. -/
theorem cuspScalarForm_energy_coercive (w : cuspScalarForm) :
    (1 / 5 : ℝ) * ‖w‖ ^ 2 ≤ ‖formGradient (w : FormDomain)‖ ^ 2 := by
  have he := cuspScalarForm_quarter_mass_le_energy w
  have hn := formDomain_norm_sq (w : FormDomain)
  change ‖w‖ ^ 2 = ‖scalarCuspEmbedding w‖ ^ 2 +
    ‖formGradient (w : FormDomain)‖ ^ 2 at hn
  linarith

/-- The precise mass fraction controls the embedding into the actual modular Hilbert space. -/
theorem scalarCuspEmbedding_norm_sq_le (w : cuspScalarForm) :
    ‖scalarCuspEmbedding w‖ ^ 2 ≤ (4 / 5 : ℝ) * ‖w‖ ^ 2 := by
  have he := cuspScalarForm_quarter_mass_le_energy w
  have hn := formDomain_norm_sq (w : FormDomain)
  change ‖w‖ ^ 2 = ‖scalarCuspEmbedding w‖ ^ 2 +
    ‖formGradient (w : FormDomain)‖ ^ 2 at hn
  linarith

end GapFamily.Analytic
