import GapFamily.Analytic.Modular.Periodization.ModularPeriodizationPairing

/-! Ordinary compact-test unfolding for continuous modular representatives of
arbitrary actual modular L² vectors. No smooth-core membership is assumed. -/

noncomputable section
namespace GapFamily.Analytic.ModularContinuousTestPairing
open Set Filter MeasureTheory UpperHalfPlane ModularGradient
open scoped ContDiff MatrixGroups Topology

theorem continuous_conj_mul_upperSeed (f : ℂ → ℂ)
    (hf : ContinuousOn f upperHalfPlaneSet) {ψ : ℂ → ℂ}
    (hψ : Continuous ψ) (hs : tsupport ψ ⊆ upperHalfPlaneSet) :
    Continuous (fun z => star (f z) * ψ z) := by
  rw [continuous_iff_continuousAt]
  intro z
  by_cases hz : z ∈ tsupport ψ
  · exact (hf.continuousAt (isOpen_upperHalfPlaneSet.mem_nhds (hs hz))).star.mul
      hψ.continuousAt
  · apply (continuousAt_const (y := (0 : ℂ))).congr_of_eventuallyEq
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hz] with w hw
    simp [hw]

theorem modularPeriodization_conj_mul (f ψ : ℂ → ℂ)
    (hmod : ∀ γ : SL(2, ℤ), ∀ τ : UpperHalfPlane, f (γ • τ : UpperHalfPlane) = f τ)
    (τ : UpperHalfPlane) :
    modularPeriodization (fun z => star (f z) * ψ z) τ =
      star (f τ) * modularPeriodization ψ τ := by
  simp only [modularPeriodization_coe, hmod]
  rw [tsum_mul_left]
  ring

/-- Both the compact ordinary hyperbolic test and the Hilbert pairing use the
literal representative, including across every fundamental-domain seam. -/
theorem inner_value_periodizedUpperCore (G : ModularHilbert) (f : ℂ → ℂ)
    (hf : ContinuousOn f upperHalfPlaneSet)
    (hmod : ∀ γ : SL(2, ℤ), ∀ τ : UpperHalfPlane, f (γ • τ : UpperHalfPlane) = f τ)
    (hG : G =ᵐ[modularMeasure] (fun τ : UpperHalfPlane => f τ))
    (ψ : ℂ → ℂ) (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    (hs : tsupport ψ ⊆ upperHalfPlaneSet) :
    inner ℂ G (value (periodizedUpperCore ψ hψ hc hs)) =
      ∫ τ : UpperHalfPlane, star (f τ) * ψ τ ∂volume := by
  have hi : Integrable (fun τ : UpperHalfPlane => star (f τ) * ψ τ) volume :=
    upperSeed_integrable (ψ := fun z => star (f z) * ψ z)
      (continuous_conj_mul_upperSeed f hf hψ.continuous hs)
      hc.mul_left (tsupport_mul_subset_right.trans hs)
  rw [L2.inner_def]
  calc
    _ = ∫ τ : UpperHalfPlane, star (f τ) * modularPeriodization ψ τ ∂modularMeasure := by
      apply integral_congr_ae
      filter_upwards [hG, value_ae (periodizedUpperCore ψ hψ hc hs)] with τ hF hP
      rw [hF, hP]
      simp [RCLike.inner_apply, periodizedUpperCore, mul_comm]
    _ = ∫ τ : UpperHalfPlane, modularPeriodization (fun z => star (f z) * ψ z) τ
        ∂modularMeasure := by
      apply integral_congr_ae
      filter_upwards [] with τ
      exact (modularPeriodization_conj_mul f ψ hmod τ).symm
    _ = _ := by
      simp_rw [modularPeriodization_coe]
      rw [integral_const_mul, integral_modularAction_tsum_eq_two_mul hi]
      ring

theorem test_mul_representative_integrable (f : ℂ → ℂ)
    (hf : ContinuousOn f upperHalfPlaneSet) (ψ : ℂ → ℂ)
    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    (hs : tsupport ψ ⊆ upperHalfPlaneSet) :
    Integrable (fun τ : UpperHalfPlane => star (ψ τ) * f τ) volume := by
  have hi : Integrable (fun τ : UpperHalfPlane => star (f τ) * ψ τ) volume :=
    upperSeed_integrable (ψ := fun z => star (f z) * ψ z)
      (continuous_conj_mul_upperSeed f hf hψ.continuous hs)
      hc.mul_left (tsupport_mul_subset_right.trans hs)
  have hstar := Complex.conjCLE.toContinuousLinearMap.integrable_comp hi
  simpa only [ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply, map_mul,
    ← Complex.star_def, star_star, mul_comm] using hstar

/-- Test-first value pairing for an arbitrary Hilbert vector with its genuine
continuous invariant representative, as an ordinary whole-upper-plane integral. -/
theorem inner_periodizedUpperCore_value (G : ModularHilbert) (f : ℂ → ℂ)
    (hf : ContinuousOn f upperHalfPlaneSet)
    (hmod : ∀ γ : SL(2, ℤ), ∀ τ : UpperHalfPlane, f (γ • τ : UpperHalfPlane) = f τ)
    (hG : G =ᵐ[modularMeasure] (fun τ : UpperHalfPlane => f τ))
    (ψ : ℂ → ℂ) (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    (hs : tsupport ψ ⊆ upperHalfPlaneSet) :
    inner ℂ (value (periodizedUpperCore ψ hψ hc hs)) G =
      ∫ τ : UpperHalfPlane, star (ψ τ) * f τ ∂volume := by
  calc
    _ = star (inner ℂ G (value (periodizedUpperCore ψ hψ hc hs))) :=
      (inner_conj_symm _ _).symm
    _ = _ := by
      rw [inner_value_periodizedUpperCore G f hf hmod hG ψ hψ hc hs]
      change (starRingEnd ℂ) (∫ τ : UpperHalfPlane, star (f τ) * ψ τ ∂volume) = _
      rw [← integral_conj]
      apply integral_congr_ae
      filter_upwards [] with τ
      simp only [map_mul, ← Complex.star_def, star_star, mul_comm]

end GapFamily.Analytic.ModularContinuousTestPairing
