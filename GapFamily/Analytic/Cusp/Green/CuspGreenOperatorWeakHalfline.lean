import GapFamily.Analytic.Cusp.Green.CuspGreenOperatorWeakEquation
import GapFamily.Analytic.Cusp.Green.CuspGreenOperatorWeakExterior

/-!
# The Green test equation across the source cutoff

The actual collar response solves the source equation against tests extending
beyond the collar. Its genuine outgoing boundary term cancels at the source
cutoff. All integrals are ordinary convergent integrals and all parameters,
including zero, are covered.
-/

noncomputable section
namespace GapFamily.Analytic
open MeasureTheory Set Filter

/-- The actual response is continuous on its closed source collar. -/
theorem continuousOn_cuspGreenCollarResponse_collar (a b : ℝ) (κ : ℂ)
    (f : Lp ℂ 2 (cuspGreenCollarMeasure a b)) :
    ContinuousOn (cuspGreenCollarResponse a b κ f) (Icc a b) := by
  apply continuousOn_iff_continuous_domRestrict.mpr
  change Continuous (fun t : CuspGreenCollar a b => cuspGreenCollarResponse a b κ f t)
  simpa only [cuspGreenCollarResponse_eq_operator] using
    (cuspGreenCollarOperator a b κ f).continuous

/-- Its closed exterior restriction is the continuous outgoing mode. -/
theorem continuousOn_cuspGreenCollarResponse_exterior (a b : ℝ) (κ : ℂ)
    (f : Lp ℂ 2 (cuspGreenCollarMeasure a b)) :
    ContinuousOn (cuspGreenCollarResponse a b κ f) (Ici b) := by
  apply (cuspBoundaryMode_continuous b κ
    (cuspGreenCollarResponse a b κ f b)).continuousOn.congr
  intro t ht
  exact cuspGreenCollarResponse_eq_boundaryMode a b t ht κ f

private theorem continuous_cuspTestSource {ψ : ℝ → ℂ} (hψ : ContDiff ℝ 2 ψ) (κ : ℂ) :
    Continuous (fun t : ℝ => -deriv (deriv ψ) t + κ ^ 2 * ψ t) := by
  have hψ' : ContDiff ℝ 1 (deriv ψ) := hψ.deriv'
  exact hψ'.continuous_deriv_one.neg.add (continuous_const.mul hψ.continuous)

/-- Test pairings across the cutoff are genuinely interval-integrable. -/
theorem cuspGreenCollarResponse_test_intervalIntegrable (a b D : ℝ)
    (hab : a ≤ b) (hbD : b ≤ D) (κ : ℂ)
    (f : Lp ℂ 2 (cuspGreenCollarMeasure a b)) {ψ : ℝ → ℂ} (hψ : ContDiff ℝ 2 ψ) :
    IntervalIntegrable (fun t : ℝ =>
      cuspGreenCollarResponse a b κ f t * (-deriv (deriv ψ) t + κ ^ 2 * ψ t)) volume a D := by
  have hc := continuous_cuspTestSource hψ κ
  have hleft := ((continuousOn_cuspGreenCollarResponse_collar a b κ f).mul
    hc.continuousOn).intervalIntegrable_of_Icc (μ := volume) hab
  have hright := (((continuousOn_cuspGreenCollarResponse_exterior a b κ f).mono
    (show Icc b D ⊆ Ici b from fun _ ht => ht.1)).mul
      hc.continuousOn).intervalIntegrable_of_Icc (μ := volume) hbD
  exact hleft.trans hright

/-- Ordinary exterior integration by parts retains its exact endpoint traces. -/
theorem cuspGreenCollarResponse_weak_exterior_boundary (a b D : ℝ) (hbD : b ≤ D)
    (κ : ℂ) (f : Lp ℂ 2 (cuspGreenCollarMeasure a b))
    {ψ : ℝ → ℂ} (hψ : ContDiff ℝ 2 ψ) :
    (∫ t : ℝ in b..D,
      cuspGreenCollarResponse a b κ f t * (-deriv (deriv ψ) t + κ ^ 2 * ψ t)) =
      -cuspGreenCollarResponse a b κ f D * (κ * ψ D + deriv ψ D) +
        cuspGreenCollarResponse a b κ f b * (κ * ψ b + deriv ψ b) := by
  let M := cuspBoundaryMode b κ (cuspGreenCollarResponse a b κ f b)
  have hM : Continuous M := cuspBoundaryMode_continuous b κ _
  have hc := hM.mul (continuous_cuspTestSource hψ κ)
  have hMderiv (t : ℝ) : HasDerivAt M (-κ * M t) t :=
    hasDerivAt_cuspBoundaryMode b κ _ t
  have hd (t : ℝ) : HasDerivAt
      (fun v : ℝ => (-κ * M v) * ψ v - M v * deriv ψ v)
      (M t * (-deriv (deriv ψ) t + κ ^ 2 * ψ t)) t := by
    apply (((hMderiv t).const_mul (-κ)).mul
      (hψ.differentiable (by norm_num) t).hasDerivAt |>.sub
        ((hMderiv t).mul (hψ.differentiable_deriv_two t).hasDerivAt)).congr_deriv
    ring
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => hd t) (hc.intervalIntegrable b D)
  have heq (t : ℝ) (ht : b ≤ t) : M t = cuspGreenCollarResponse a b κ f t :=
    (cuspGreenCollarResponse_eq_boundaryMode a b t ht κ f).symm
  calc
    _ = ∫ t : ℝ in b..D, M t * (-deriv (deriv ψ) t + κ ^ 2 * ψ t) := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le hbD] at ht
      dsimp only
      rw [heq t ht.1]
    _ = _ := by
      rw [hftc, heq D hbD, heq b le_rfl]
      ring

/-- The exact boundary formula for tests whose interval extends beyond the source collar. -/
theorem cuspGreenCollarResponse_weak_halfline_boundary (a b D : ℝ)
    (hab : a ≤ b) (hbD : b ≤ D) (κ : ℂ)
    (f : Lp ℂ 2 (cuspGreenCollarMeasure a b)) {ψ : ℝ → ℂ} (hψ : ContDiff ℝ 2 ψ) :
    (∫ t : ℝ in a..D,
      cuspGreenCollarResponse a b κ f t * (-deriv (deriv ψ) t + κ ^ 2 * ψ t)) =
      (∫ u : CuspGreenCollar a b, ψ u * f u ∂cuspGreenCollarMeasure a b) -
        cuspGreenCollarResponse a b κ f D * (κ * ψ D + deriv ψ D) -
        cuspGreenCollarTraceOperator a b κ f * ψ a := by
  have hleft : (∫ t : ℝ in a..b,
      cuspGreenCollarResponse a b κ f t * (-deriv (deriv ψ) t + κ ^ 2 * ψ t)) =
      (∫ u : CuspGreenCollar a b, ψ u * f u ∂cuspGreenCollarMeasure a b) -
        cuspGreenCollarResponse a b κ f b * (κ * ψ b + deriv ψ b) -
        cuspGreenCollarTraceOperator a b κ f * ψ a := by
    rw [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc,
      ← integral_subtype_comap measurableSet_Icc
        (fun t : ℝ => cuspGreenCollarResponse a b κ f t *
          (-deriv (deriv ψ) t + κ ^ 2 * ψ t))]
    exact cuspGreenCollarResponse_weak_boundary a b hab κ f hψ
  have hc := continuous_cuspTestSource hψ κ
  have hil := ((continuousOn_cuspGreenCollarResponse_collar a b κ f).mul
    hc.continuousOn).intervalIntegrable_of_Icc (μ := volume) hab
  have hir := (((continuousOn_cuspGreenCollarResponse_exterior a b κ f).mono
    (show Icc b D ⊆ Ici b from fun _ ht => ht.1)).mul
      hc.continuousOn).intervalIntegrable_of_Icc (μ := volume) hbD
  have hsplit := intervalIntegral.integral_add_adjacent_intervals hil hir
  simp only [Pi.mul_apply] at hsplit
  rw [← hsplit, hleft,
    cuspGreenCollarResponse_weak_exterior_boundary a b D hbD κ f hψ]
  ring

/-- Actual source reproduction for tests extending across the source cutoff. -/
theorem cuspGreenCollarResponse_weak_halfline_test (a b D : ℝ)
    (hab : a ≤ b) (hbD : b ≤ D) (κ : ℂ)
    (f : Lp ℂ 2 (cuspGreenCollarMeasure a b)) {ψ : ℝ → ℂ} (hψ : ContDiff ℝ 2 ψ)
    (hψa : ψ a = 0) (hψD : ψ D = 0) (hψ'D : deriv ψ D = 0) :
    (∫ t : ℝ in a..D,
      cuspGreenCollarResponse a b κ f t * (-deriv (deriv ψ) t + κ ^ 2 * ψ t)) =
      ∫ u : CuspGreenCollar a b, ψ u * f u ∂cuspGreenCollarMeasure a b := by
  rw [cuspGreenCollarResponse_weak_halfline_boundary a b D hab hbD κ f hψ,
    hψa, hψD, hψ'D]
  ring

/-- Compactly supported interior tests may cross the source cutoff freely. -/
theorem cuspGreenCollarResponse_weak_halflineODE (a b D : ℝ)
    (hab : a ≤ b) (hbD : b ≤ D) (κ : ℂ)
    (f : Lp ℂ 2 (cuspGreenCollarMeasure a b)) {ψ : ℝ → ℂ} (hψ : ContDiff ℝ 2 ψ)
    (hs : tsupport ψ ⊆ Ioo a D) :
    (∫ t : ℝ in a..D,
      cuspGreenCollarResponse a b κ f t * (-deriv (deriv ψ) t + κ ^ 2 * ψ t)) =
      ∫ u : CuspGreenCollar a b, ψ u * f u ∂cuspGreenCollarMeasure a b := by
  have ha : a ∉ tsupport ψ := by intro h; exact lt_irrefl a (hs h).1
  have hD : D ∉ tsupport ψ := by intro h; exact lt_irrefl D (hs h).2
  exact cuspGreenCollarResponse_weak_halfline_test a b D hab hbD κ f hψ
    (image_eq_zero_of_notMem_tsupport ha) (image_eq_zero_of_notMem_tsupport hD)
    (deriv_of_notMem_tsupport hD)

end GapFamily.Analytic
