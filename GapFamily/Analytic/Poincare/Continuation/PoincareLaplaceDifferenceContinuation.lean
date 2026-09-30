import GapFamily.Analytic.Poincare.Continuation.PoincarePhysicalEnergyGrowth
import GapFamily.Analytic.Poincare.Continuation.PoincareCompactSuperposition
import GapFamily.Analytic.Transform.LaplaceConeWeight

/-!
# Same-parameter Laplace differences of the actual seed

Every integer input spin has an ordinary energy integral of the actual
compact-valued continued seed after a finite input height difference.
The integral is analytic throughout the genuine connected continuation
region. Endpoint domination and linear physical-energy growth are proved
for this actual family, including its scalar endpoint.
-/

noncomputable section
namespace GapFamily.Analytic.PoincareEnergyContinuation
open Set Filter MeasureTheory UpperHalfPlane CuspFourierCutoff PoincareCanonical
open DominatedAnalytic
open scoped Topology

/-- The literal same-parameter cone integral after the input height difference. -/
def seedLaplaceDifferenceOn (K : Set ℂ) [CompactSpace K]
    (hKH : K ⊆ upperHalfPlaneSet) (J : ℤ) (t d : ℝ) (κ : ℂ) : C(K, ℂ) :=
  ∫ E : ℝ in Ioi |(J : ℝ)|,
    coneLaplaceDifferenceWeight (exponent κ) J t d E • continuedSeedOn K hKH E J κ

private theorem cone_weight_analytic {J E : ℝ} (hE : |J| < E)
    (t d : ℝ) (κ : ℂ) :
    AnalyticAt ℂ (fun ξ => coneLaplaceDifferenceWeight (exponent ξ) J t d E) κ := by
  exact ((differentiable_coneLaplaceDifferenceWeight J t d hE).analyticAt
    (exponent κ)).comp (by unfold exponent; fun_prop)

private theorem cone_integrand_measurable (K : Set ℂ) [CompactSpace K]
    (hKH : K ⊆ upperHalfPlaneSet) (J : ℤ) (t d : ℝ) {κ : ℂ}
    (hκ : κ ∈ continuationRegion (chosenContinuation K hKH).radius) :
    AEStronglyMeasurable
      (fun E : ℝ => coneLaplaceDifferenceWeight (exponent κ) J t d E •
        continuedSeedOn K hKH E J κ) (volume.restrict (Ioi |(J : ℝ)|)) := by
  exact ((continuousOn_coneLaplaceDifferenceWeight (exponent κ) J t d).smul
    (continuous_continuedSeedOn_realEnergy K hKH J
      (re_gt_neg_half_of_mem_continuation (chosenContinuation K hKH) hκ)).continuousOn).aestronglyMeasurable
        measurableSet_Ioi

/-- The actual seed's same-parameter height difference is ordinarily
absolutely integrable on each physical cone slice. -/
theorem integrableOn_seedLaplaceDifferenceOn (K : Set ℂ) [CompactSpace K]
    (hKH : K ⊆ upperHalfPlaneSet) (J : ℤ) {t d : ℝ} (ht : 0 < t) (hd : 0 ≤ d) {κ : ℂ}
    (hκ : κ ∈ continuationRegion (chosenContinuation K hKH).radius) :
    IntegrableOn
      (fun E : ℝ => coneLaplaceDifferenceWeight (exponent κ) J t d E •
        continuedSeedOn K hKH E J κ) (Ioi |(J : ℝ)|) := by
  have hs : 0 < (exponent κ).re := by
    have h := re_gt_neg_half_of_mem_continuation (chosenContinuation K hKH) hκ
    norm_num [exponent, Complex.add_re]
    linarith
  obtain ⟨C, hC, hb⟩ := exists_continuedSeedOn_physical_compact_norm_bound K hKH J
    (isCompact_singleton : IsCompact ({κ} : Set ℂ)) (singleton_subset_iff.mpr hκ)
  obtain ⟨g, hg, hbound⟩ := coneLaplaceDifferenceWeight_majorant hs le_rfl ht hd (J : ℝ)
  apply (hg.const_mul C).mono'
  · exact cone_integrand_measurable K hKH J t d hκ
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with E hE
    have hE0 : 0 ≤ E := (abs_nonneg (J : ℝ)).trans (le_of_lt hE)
    rw [norm_smul]
    calc
      _ ≤ ‖coneLaplaceDifferenceWeight (exponent κ) J t d E‖ * (C * (1 + E)) :=
        mul_le_mul_of_nonneg_left (hb E hE0 κ (mem_singleton κ)) (norm_nonneg _)
      _ = C * (‖coneLaplaceDifferenceWeight (exponent κ) J t d E‖ * (1 + E)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hbound (exponent κ) le_rfl le_rfl E hE) hC.le

/-- The actual energy integral is norm analytic through threshold, for every
integer spin, with no domination assumptions left to the caller. -/
theorem analyticOnNhd_seedLaplaceDifferenceOn (K : Set ℂ) [CompactSpace K]
    (hKH : K ⊆ upperHalfPlaneSet) (J : ℤ) {t d : ℝ} (ht : 0 < t) (hd : 0 ≤ d) :
    AnalyticOnNhd ℂ (seedLaplaceDifferenceOn K hKH J t d)
      (continuationRegion (chosenContinuation K hKH).radius) := by
  intro κ₀ hκ₀
  obtain ⟨r₀, C, hr₀, hC, hsub₀, hb⟩ :=
    exists_continuedSeedOn_physical_local_norm_bound K hKH J hκ₀
  have hs : 0 < (exponent κ₀).re := by
    have h := re_gt_neg_half_of_mem_continuation (chosenContinuation K hKH) hκ₀
    norm_num [exponent, Complex.add_re]
    linarith
  let a : ℝ := (exponent κ₀).re / 2
  let b : ℝ := (exponent κ₀).re + 1
  have ha : 0 < a := half_pos hs
  have hab : a ≤ b := by dsimp [a, b]; linarith
  have hc : Continuous (fun κ : ℂ => (exponent κ).re) :=
    Complex.continuous_re.comp (continuous_const.add continuous_id)
  have hstrip : ∀ᶠ κ in 𝓝 κ₀, a < (exponent κ).re ∧ (exponent κ).re < b :=
    ((isOpen_lt continuous_const hc).inter (isOpen_lt hc continuous_const)).mem_nhds
      (show a < (exponent κ₀).re ∧ (exponent κ₀).re < b from
        ⟨half_lt_self hs, lt_add_one _⟩)
  obtain ⟨r₁, hr₁, hstrip⟩ := Metric.eventually_nhds_iff_ball.mp hstrip
  let r : ℝ := min r₀ r₁
  have hr : 0 < r := lt_min hr₀ hr₁
  have hball₀ : Metric.ball κ₀ r ⊆ Metric.ball κ₀ r₀ :=
    Metric.ball_subset_ball (min_le_left _ _)
  have hball₁ : Metric.ball κ₀ r ⊆ Metric.ball κ₀ r₁ :=
    Metric.ball_subset_ball (min_le_right _ _)
  obtain ⟨g, hg, hbound⟩ := coneLaplaceDifferenceWeight_majorant ha hab ht hd (J : ℝ)
  apply analyticAt_integral_of_dominated (r := r) (bound := fun E => C * g E) hr
  · intro κ hκ
    exact cone_integrand_measurable K hKH J t d (hsub₀ (hball₀ hκ))
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with E hE
    intro κ hκ
    exact (cone_weight_analytic hE t d κ).smul
      (analyticOnNhd_continuedSeedOn K hKH E J κ (hsub₀ (hball₀ hκ)))
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with E hE
    intro κ hκ
    have hE0 : 0 ≤ E := (abs_nonneg (J : ℝ)).trans (le_of_lt hE)
    obtain ⟨hka, hkb⟩ := hstrip κ (hball₁ hκ)
    rw [norm_smul]
    calc
      _ ≤ ‖coneLaplaceDifferenceWeight (exponent κ) J t d E‖ * (C * (1 + E)) :=
        mul_le_mul_of_nonneg_left (hb E hE0 κ (hball₀ hκ)) (norm_nonneg _)
      _ = C * (‖coneLaplaceDifferenceWeight (exponent κ) J t d E‖ * (1 + E)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hbound (exponent κ) hka.le hkb.le E hE) hC.le
  · exact hg.const_mul C

/-- Compact evaluation commutes with this ordinary energy integral. -/
theorem seedLaplaceDifferenceOn_apply (K : Set ℂ) [CompactSpace K]
    (hKH : K ⊆ upperHalfPlaneSet) (J : ℤ) {t d : ℝ} (ht : 0 < t) (hd : 0 ≤ d) {κ : ℂ}
    (hκ : κ ∈ continuationRegion (chosenContinuation K hKH).radius) (z : K) :
    seedLaplaceDifferenceOn K hKH J t d κ z =
      ∫ E : ℝ in Ioi |(J : ℝ)|,
        coneLaplaceDifferenceWeight (exponent κ) J t d E * continuedSeedOn K hKH E J κ z := by
  exact ((ContinuousMap.evalCLM ℂ z).integral_comp_comm
    (integrableOn_seedLaplaceDifferenceOn K hKH J ht hd hκ)).symm

end GapFamily.Analytic.PoincareEnergyContinuation
