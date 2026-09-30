import GapFamily.Analytic.Poincare.Arithmetic.PoincareCentralHeightCoherence

/-! Actual analytic local quotients and their height-independent threshold values. -/
noncomputable section
namespace GapFamily.Analytic.PoincareCentralZeta
open Set Filter CuspFourierCutoff PoincareFourierContinuation
open PoincareCanonical PoincareCentralFactor PoincareFourierRemainder
open scoped Topology

/-- The concrete local central-zeta quotient at a positive observation height.
Only the proved local neighborhood is asserted to be analytic. -/
def centralQuotient (y : ℝ) (hy : 0 < y) (j J : ℤ) (κ : ℂ) : ℂ :=
  centralNumerator y hy j J κ / centralFourierFactor y j κ

/-- Reference height one fixes an actual scalar family, without a supplied continuation. -/
def centralZeta (j J : ℤ) (κ : ℂ) : ℂ :=
  centralQuotient 1 zero_lt_one j J κ

/-- Nonvanishing is used only near the threshold, where the actual K0 value is nonzero. -/
theorem centralFourierFactor_eventually_ne_zero (y : ℝ) (hy : 0 < y)
    (j : ℤ) (hj : j ≠ 0) :
    ∀ᶠ κ : ℂ in 𝓝 0, centralFourierFactor y j κ ≠ 0 :=
  (centralFourierFactor_analyticAt hy hj 0).continuousAt.eventually_ne
    (centralFourierFactor_zero_ne_zero hy hj)

theorem analyticAt_centralQuotient_zero (y : ℝ) (hy : 0 < y)
    (j J : ℤ) (hj : j ≠ 0) : AnalyticAt ℂ (centralQuotient y hy j J) 0 :=
  (analyticAt_centralNumerator_zero y hy j J).div
    (centralFourierFactor_analyticAt hy hj 0) (centralFourierFactor_zero_ne_zero hy hj)

/-- One positive disk works for all input spins at each fixed output spin and height. -/
theorem exists_radius_centralQuotient_analytic (y : ℝ) (hy : 0 < y)
    (j : ℤ) (hj : j ≠ 0) :
    ∃ r : ℝ, 0 < r ∧ (∀ κ ∈ Metric.ball (0 : ℂ) r, centralFourierFactor y j κ ≠ 0) ∧
      ∀ J : ℤ, AnalyticOnNhd ℂ (centralQuotient y hy j J) (Metric.ball 0 r) := by
  obtain ⟨r, hr, hrd⟩ := Metric.mem_nhds_iff.mp
    (centralFourierFactor_eventually_ne_zero y hy j hj)
  refine ⟨min r (horizontalContinuation y hy).radius,
    lt_min hr (horizontalContinuation y hy).radius_pos, ?_, ?_⟩
  · intro κ hκ
    exact hrd (Metric.ball_subset_ball (min_le_left _ _) hκ)
  · intro J κ hκ
    have hd := hrd (Metric.ball_subset_ball (min_le_left _ _) hκ)
    have hΩ : κ ∈ horizontalFourierDomain y hy :=
      Or.inl (Metric.ball_subset_ball (min_le_right _ _) hκ)
    exact ((analyticOnNhd_centralNumerator y hy j J) κ hΩ).div
      (centralFourierFactor_analyticAt hy hj κ) hd

/-- Height coherence holds in one actual neighborhood simultaneously for all input spins. -/
theorem centralQuotient_height_eventuallyEq_all_inputs
    (y v : ℝ) (hy : 0 < y) (hv : 0 < v) (j : ℤ) (hj : j ≠ 0) :
    ∀ᶠ κ : ℂ in 𝓝 0, ∀ J : ℤ,
      centralQuotient y hy j J κ = centralQuotient v hv j J κ := by
  have hz : (0 : ℂ) ∈ continuationRegion (min (horizontalContinuation y hy).radius
      (horizontalContinuation v hv).radius) := by
    left
    simpa only [Metric.mem_ball, dist_self] using
      lt_min (horizontalContinuation y hy).radius_pos (horizontalContinuation v hv).radius_pos
  filter_upwards [(isOpen_continuationRegion _).mem_nhds hz,
    centralFourierFactor_eventually_ne_zero y hy j hj,
    centralFourierFactor_eventually_ne_zero v hv j hj] with κ hκ hdy hdv J
  exact (div_eq_div_iff hdy hdv).mpr (centralNumerator_cross_eqOn y v hy hv j J hj hκ)

theorem centralQuotient_height_eventuallyEq
    (y v : ℝ) (hy : 0 < y) (hv : 0 < v) (j J : ℤ) (hj : j ≠ 0) :
    centralQuotient y hy j J =ᶠ[𝓝 (0 : ℂ)] centralQuotient v hv j J :=
  (centralQuotient_height_eventuallyEq_all_inputs y v hy hv j hj).mono (fun _ h => h J)

theorem centralQuotient_height_zero
    (y v : ℝ) (hy : 0 < y) (hv : 0 < v) (j J : ℤ) (hj : j ≠ 0) :
    centralQuotient y hy j J 0 = centralQuotient v hv j J 0 :=
  (centralQuotient_height_eventuallyEq y v hy hv j J hj).eq_of_nhds

theorem analyticAt_centralZeta_zero (j J : ℤ) (hj : j ≠ 0) :
    AnalyticAt ℂ (centralZeta j J) 0 :=
  analyticAt_centralQuotient_zero 1 zero_lt_one j J hj

/-- The canonical local disk is independent of the input spin. -/
theorem exists_radius_centralZeta_analytic (j : ℤ) (hj : j ≠ 0) :
    ∃ r : ℝ, 0 < r ∧ ∀ J : ℤ, AnalyticOnNhd ℂ (centralZeta j J) (Metric.ball 0 r) := by
  obtain ⟨r, hr, _, ha⟩ := exists_radius_centralQuotient_analytic 1 zero_lt_one j hj
  exact ⟨r, hr, ha⟩

theorem centralZeta_eq_height_eventuallyEq (y : ℝ) (hy : 0 < y)
    (j J : ℤ) (hj : j ≠ 0) :
    centralZeta j J =ᶠ[𝓝 (0 : ℂ)] centralQuotient y hy j J :=
  centralQuotient_height_eventuallyEq 1 y zero_lt_one hy j J hj

theorem centralZeta_zero_eq_height (y : ℝ) (hy : 0 < y)
    (j J : ℤ) (hj : j ≠ 0) :
    centralZeta j J 0 = centralNumerator y hy j J 0 / centralFourierFactor y j 0 :=
  (centralZeta_eq_height_eventuallyEq y hy j J hj).eq_of_nhds

/-- The canonical threshold value has an exact formula at every positive height. -/
theorem centralZeta_zero_eq_thresholdQuotient (y : ℝ) (hy : 0 < y)
    (j J : ℤ) (hj : j ≠ 0) :
    centralZeta j J 0 =
      (thresholdFourierCoefficient y hy j J -
        (if j = J then (y : ℂ) ^ (1 / 2 : ℂ) else 0) -
          fourierRemainder y j J (1 / 2 : ℂ)) / centralFourierFactor y j 0 := by
  rw [centralZeta_zero_eq_height y hy j J hj, centralNumerator_zero]

/-- The actual threshold numerator factors through the height-independent local zeta value. -/
theorem centralZeta_zero_mul_factor (y : ℝ) (hy : 0 < y)
    (j J : ℤ) (hj : j ≠ 0) :
    centralZeta j J 0 * centralFourierFactor y j 0 = centralNumerator y hy j J 0 := by
  rw [centralZeta_zero_eq_height y hy j J hj,
    div_mul_cancel₀ _ (centralFourierFactor_zero_ne_zero hy hj)]

/-- The canonical threshold Fourier coefficient has the central-zeta factorization
at every positive height, without an ordinary divergent central integral. -/
theorem thresholdFourierCoefficient_eq_centralZeta (y : ℝ) (hy : 0 < y)
    (j J : ℤ) (hj : j ≠ 0) :
    thresholdFourierCoefficient y hy j J =
      (if j = J then (y : ℂ) ^ (1 / 2 : ℂ) else 0) +
        centralFourierFactor y j 0 * centralZeta j J 0 +
          fourierRemainder y j J (1 / 2 : ℂ) := by
  have h := centralZeta_zero_mul_factor y hy j J hj
  rw [centralNumerator_zero] at h
  linear_combination -h

/-- On the original convergence half-plane the concrete quotient agrees with
the literal Dirichlet series wherever the actual factor is nonzero. -/
theorem centralQuotient_eq_dirichlet_common (y : ℝ) (hy : 0 < y)
    (j J : ℤ) (hj : j ≠ 0) {κ : ℂ} (hκ : (1 / 2 : ℝ) < κ.re)
    (hd : centralFourierFactor y j κ ≠ 0) :
    centralQuotient y hy j J κ = kloostermanDirichlet j J (exponent κ) := by
  unfold centralQuotient
  rw [centralNumerator_eq_factor_mul_dirichlet y hy j J hj hκ, mul_div_cancel_left₀ _ hd]

end GapFamily.Analytic.PoincareCentralZeta
