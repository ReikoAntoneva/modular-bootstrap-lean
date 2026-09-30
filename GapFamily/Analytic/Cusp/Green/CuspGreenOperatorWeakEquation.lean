import GapFamily.Analytic.Cusp.Green.CuspGreenOperatorWeakKernel
import GapFamily.Analytic.Cusp.Green.CuspGreenOperatorWeakPairing
import Mathlib.Analysis.Calculus.Deriv.Support

/-! The actual finite-collar L² Green response solves the forced equation weakly. -/
noncomputable section
namespace GapFamily.Analytic
open MeasureTheory Set Filter

/-- The literal differential expression on a twice continuously differentiable test. -/
def cuspGreenCollarTestSource (a b : ℝ) (κ : ℂ) (ψ : ℝ → ℂ) (hψ : ContDiff ℝ 2 ψ) :
    C(CuspGreenCollar a b, ℂ) where
  toFun t := -deriv (deriv ψ) t + κ ^ 2 * ψ t
  continuous_toFun := by
    have hψ' : ContDiff ℝ 1 (deriv ψ) := hψ.deriv'
    exact (hψ'.continuous_deriv_one.neg.add (continuous_const.mul hψ.continuous)).comp
      continuous_subtype_val

/-- The genuine right branch is outgoing at the upper source cutoff. -/
theorem cuspGreenRightSlope_eq_neg_mul (a b u : ℝ) (hu : u ≤ b) (κ : ℂ) :
    cuspGreenRightSlope a b u κ = -κ * cuspGreen a b u κ := by
  by_cases hκ : κ = 0
  · subst κ
    simp [cuspGreenRightSlope]
  · rw [cuspGreen_eq_quotient a b u hκ, abs_of_nonneg (sub_nonneg.mpr hu)]
    unfold cuspGreenRightSlope
    field_simp
    ring

/-- The lower left branch gives exactly the genuine derivative-trace kernel. -/
theorem cuspGreenLeftSlope_boundary (a u : ℝ) (κ : ℂ) :
    cuspGreenLeftSlope a a u κ = Complex.exp (-κ * ((u - a : ℝ) : ℂ)) := by
  unfold cuspGreenLeftSlope
  rw [show a + u - 2 * a = u - a by ring]
  ring

/-- Applying the actual Green operator to the test differential leaves its exact boundary terms. -/
theorem cuspGreenCollarOperator_testSource (a b : ℝ) (hba : a ≤ b) (κ : ℂ)
    {ψ : ℝ → ℂ} (hψ : ContDiff ℝ 2 ψ) (u : CuspGreenCollar a b) :
    cuspGreenCollarOperator a b κ
        (ContinuousMap.toLp 2 (cuspGreenCollarMeasure a b) ℂ
          (cuspGreenCollarTestSource a b κ ψ hψ)) u =
      ψ u - cuspGreen a b u κ * (κ * ψ b + deriv ψ b) -
        Complex.exp (-κ * (((u : ℝ) - a : ℝ) : ℂ)) * ψ a := by
  rw [cuspGreenCollarOperator_apply_continuous]
  change (∫ t : CuspGreenCollar a b,
    cuspGreen a u t κ * (-deriv (deriv ψ) t + κ ^ 2 * ψ t) ∂cuspGreenCollarMeasure a b) = _
  simp_rw [cuspGreen_symm a u]
  rw [show (∫ t : CuspGreenCollar a b,
      cuspGreen a t u κ * (-deriv (deriv ψ) t + κ ^ 2 * ψ t) ∂cuspGreenCollarMeasure a b) =
      ∫ t : ℝ in Icc a b, cuspGreen a t u κ * (-deriv (deriv ψ) t + κ ^ 2 * ψ t) from
    integral_subtype_comap measurableSet_Icc
      (fun t : ℝ => cuspGreen a t u κ * (-deriv (deriv ψ) t + κ ^ 2 * ψ t))]
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hba,
    cuspGreen_test_integral_boundary a b u u.property κ hψ,
    cuspGreenRightSlope_eq_neg_mul a b u u.property.2 κ,
    cuspGreenLeftSlope_boundary]
  ring

/-- Continuous scalar tests against every source class are ordinarily integrable. -/
theorem cuspGreenCollar_sourceTest_integrable (a b : ℝ)
    (f : Lp ℂ 2 (cuspGreenCollarMeasure a b)) (g : C(CuspGreenCollar a b, ℂ)) :
    Integrable (fun u => g u * f u) (cuspGreenCollarMeasure a b) :=
  (cuspGreenCollarSource_integrable a b f).bdd_mul g.continuous.aestronglyMeasurable
    (Eventually.of_forall g.norm_coe_le_norm)

/-- The full ordinary Green identity holds for every actual collar L² source.
The top endpoint retains its outgoing Robin term, not an imposed Dirichlet value. -/
theorem cuspGreenCollarResponse_weak_boundary (a b : ℝ) (hba : a ≤ b) (κ : ℂ)
    (f : Lp ℂ 2 (cuspGreenCollarMeasure a b)) {ψ : ℝ → ℂ} (hψ : ContDiff ℝ 2 ψ) :
    (∫ t : CuspGreenCollar a b,
      cuspGreenCollarResponse a b κ f t * (-deriv (deriv ψ) t + κ ^ 2 * ψ t)
      ∂cuspGreenCollarMeasure a b) =
      (∫ u : CuspGreenCollar a b, ψ u * f u ∂cuspGreenCollarMeasure a b) -
        cuspGreenCollarResponse a b κ f b * (κ * ψ b + deriv ψ b) -
        cuspGreenCollarTraceOperator a b κ f * ψ a := by
  let g := cuspGreenCollarTestSource a b κ ψ hψ
  have hpair := cuspGreenCollar_pairing a b κ f g
  change (∫ t : CuspGreenCollar a b, cuspGreenCollarResponse a b κ f t * g t
    ∂cuspGreenCollarMeasure a b) = _
  have hleft : (∫ t : CuspGreenCollar a b, cuspGreenCollarResponse a b κ f t * g t
      ∂cuspGreenCollarMeasure a b) =
      ∫ t : CuspGreenCollar a b, cuspGreenCollarOperator a b κ f t * g t
        ∂cuspGreenCollarMeasure a b := by
    apply integral_congr_ae
    filter_upwards [] with t
    rw [cuspGreenCollarResponse_eq_operator]
  rw [hleft, hpair]
  dsimp only [g]
  simp_rw [cuspGreenCollarOperator_testSource a b hba κ hψ]
  have hψf : Integrable (fun u : CuspGreenCollar a b => ψ u * f u)
      (cuspGreenCollarMeasure a b) :=
    cuspGreenCollar_sourceTest_integrable a b f ⟨fun u => ψ u, hψ.continuous.comp continuous_subtype_val⟩
  have hGf := (cuspGreenCollarResponse_integrable a b b κ f).mul_const (κ * ψ b + deriv ψ b)
  have hTf := (cuspGreenCollarTrace_integrable a b κ f).mul_const (ψ a)
  have hsub : Integrable (fun u : CuspGreenCollar a b =>
      ψ u * f u - (cuspGreen a b u κ * f u) * (κ * ψ b + deriv ψ b))
      (cuspGreenCollarMeasure a b) := hψf.sub hGf
  calc
    _ = ∫ u : CuspGreenCollar a b,
        (ψ u * f u - (cuspGreen a b u κ * f u) * (κ * ψ b + deriv ψ b)) -
          (Complex.exp (-κ * (((u : ℝ) - a : ℝ) : ℂ)) * f u) * ψ a
        ∂cuspGreenCollarMeasure a b := by
      apply integral_congr_ae
      filter_upwards [] with u
      ring
    _ = _ := by
      rw [integral_sub hsub hTf, integral_sub hψf hGf,
        integral_mul_const, integral_mul_const, ← cuspGreenCollarTraceOperator_apply]
      rfl

/-- The forced ODE in the distributional test pairing, for every finite-collar L² source. -/
theorem cuspGreenCollarResponse_weakODE (a b : ℝ) (hba : a ≤ b) (κ : ℂ)
    (f : Lp ℂ 2 (cuspGreenCollarMeasure a b)) {ψ : ℝ → ℂ} (hψ : ContDiff ℝ 2 ψ)
    (hs : tsupport ψ ⊆ Ioo a b) :
    (∫ t : CuspGreenCollar a b,
      cuspGreenCollarResponse a b κ f t * (-deriv (deriv ψ) t + κ ^ 2 * ψ t)
      ∂cuspGreenCollarMeasure a b) =
      ∫ u : CuspGreenCollar a b, ψ u * f u ∂cuspGreenCollarMeasure a b := by
  have ha : a ∉ tsupport ψ := by intro h; exact lt_irrefl a (hs h).1
  have hb : b ∉ tsupport ψ := by intro h; exact lt_irrefl b (hs h).2
  rw [cuspGreenCollarResponse_weak_boundary a b hba κ f hψ,
    image_eq_zero_of_notMem_tsupport ha, image_eq_zero_of_notMem_tsupport hb,
    deriv_of_notMem_tsupport hb]
  ring

/-- The same distributional identity in the ordinary real-coordinate interval integral. -/
theorem cuspGreenCollarResponse_weakODE_interval (a b : ℝ) (hba : a ≤ b) (κ : ℂ)
    (f : Lp ℂ 2 (cuspGreenCollarMeasure a b)) {ψ : ℝ → ℂ} (hψ : ContDiff ℝ 2 ψ)
    (hs : tsupport ψ ⊆ Ioo a b) :
    (∫ t : ℝ in a..b,
      cuspGreenCollarResponse a b κ f t * (-deriv (deriv ψ) t + κ ^ 2 * ψ t)) =
      ∫ u : CuspGreenCollar a b, ψ u * f u ∂cuspGreenCollarMeasure a b := by
  rw [intervalIntegral.integral_of_le hba, ← integral_Icc_eq_integral_Ioc,
    ← integral_subtype_comap measurableSet_Icc
      (fun t : ℝ => cuspGreenCollarResponse a b κ f t *
        (-deriv (deriv ψ) t + κ ^ 2 * ψ t))]
  exact cuspGreenCollarResponse_weakODE a b hba κ f hψ hs

end GapFamily.Analytic
