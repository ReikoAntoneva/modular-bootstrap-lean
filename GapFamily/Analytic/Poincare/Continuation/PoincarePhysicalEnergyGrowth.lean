import GapFamily.Analytic.Poincare.Continuation.PoincareCompactSeedLocalBound

/-!
# Physical energy growth of the actual continued seed

For nonnegative real input energy, `|exp(-2πEy)-1| ≤ 2πEy`. The gained orbit-height
power therefore gives a compact normal majorant linear in energy on the whole
physical half-line, without an energy-dependent exponential constant.
-/

noncomputable section
namespace GapFamily.Analytic.PoincareEnergyContinuation
open Set Filter UpperHalfPlane CuspFourierCutoff PoincareCanonical
open PoincareEnergyConvergentAnalytic
open scoped Topology

/-- The real physical exponential subtraction has a global linear bound. -/
theorem norm_physical_exp_sub_one_le {E y : ℝ} (hE : 0 ≤ E) (hy : 0 ≤ y) :
    ‖Complex.exp (-2 * (Real.pi : ℂ) * E * y) - 1‖ ≤ 2 * Real.pi * E * y := by
  have ht : 0 ≤ 2 * Real.pi * E * y := by positivity
  have he : Complex.exp (-2 * (Real.pi : ℂ) * E * y) - 1 =
      ((Real.exp (-2 * Real.pi * E * y) - 1 : ℝ) : ℂ) := by
    push_cast
    ring_nf
  rw [he, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonpos (sub_nonpos.mpr (Real.exp_le_one_iff.mpr (by nlinarith)))]
  have h := Real.add_one_le_exp (-2 * Real.pi * E * y)
  linarith

/-- Physical nonnegative input energy improves the individual seed difference bound. -/
theorem norm_complexPointSeed_sub_zero_physical_le {E : ℝ} (hE : 0 ≤ E)
    (J : ℤ) (s : ℂ) (z : UpperHalfPlane) :
    ‖complexPointSeed E J s z - complexPointSeed 0 J s z‖ ≤
      (2 * Real.pi * E) * z.im ^ (s.re + 1) := by
  rw [complexPointSeed_sub_zero_energy, norm_mul, norm_mul]
  have hphase : ‖Complex.exp (((2 * Real.pi * (J : ℝ) * z.re : ℝ) : ℂ) * Complex.I)‖ = 1 := by
    simp [Complex.norm_exp]
  rw [hphase, mul_one, Complex.norm_cpow_eq_rpow_re_of_pos z.im_pos]
  calc
    _ ≤ z.im ^ s.re * (2 * Real.pi * E * z.im) :=
      mul_le_mul_of_nonneg_left (norm_physical_exp_sub_one_le hE z.im_pos.le)
        (Real.rpow_nonneg z.im_pos.le _)
    _ = _ := by rw [Real.rpow_add_one z.im_pos.ne']; ring

/-- One summable majorant controls the entire physical energy half-line, uniformly
in integer spin and in a closed positive strip of exponents. -/
theorem compactEnergyTerm_physical_normal_on_strip (K : Set ℂ) [CompactSpace K]
    (hKH : K ⊆ upperHalfPlaneSet) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∃ u : CuspCoset → ℝ, Summable u ∧ (∀ q, 0 ≤ u q) ∧
      ∀ (E : ℝ), 0 ≤ E → ∀ (J : ℤ) (q : CuspCoset) (s : ℂ),
        a ≤ s.re → s.re ≤ b → ‖compactEnergyTerm K hKH E J s q‖ ≤ E * u q := by
  let i : K → UpperHalfPlane := fun z => ⟨z, hKH z.property⟩
  have hi : Continuous i := continuous_subtype_val.upperHalfPlaneMk (fun z => hKH z.property)
  have hKi : IsCompact (range i) := isCompact_range hi
  obtain ⟨_, _, ua, hua, hua0, hba⟩ :=
    exists_cusp_height_compact_majorant hKi (t := a + 1) (by linarith)
  obtain ⟨_, _, ub, hub, hub0, hbb⟩ :=
    exists_cusp_height_compact_majorant hKi (t := b + 1) (by linarith)
  refine ⟨fun q => (2 * Real.pi) * (ua q + ub q), (hua.add hub).mul_left _,
    fun q => mul_nonneg (by positivity) (add_nonneg (hua0 q) (hub0 q)), ?_⟩
  intro E hE J q s has hsb
  apply (ContinuousMap.norm_le _
    (mul_nonneg hE (mul_nonneg (by positivity) (add_nonneg (hua0 q) (hub0 q))))).mpr
  intro z
  rw [compactEnergyTerm_apply, ofComplex_apply_of_im_pos (hKH z.property)]
  change ‖complexPoincareDifferenceTerm E J s (i z) q‖ ≤ _
  simp only [complexPoincareDifferenceTerm, complexPoincareTerm_out]
  have hp : (q.out • i z).im ^ (s.re + 1) ≤ ua q + ub q :=
    (rpow_le_add_endpoint (q.out • i z).im_pos
      (show a + 1 ≤ s.re + 1 by linarith) (show s.re + 1 ≤ b + 1 by linarith)).trans
      (add_le_add (hba q (i z) (mem_range_self z)).2 (hbb q (i z) (mem_range_self z)).2)
  calc
    _ ≤ (2 * Real.pi * E) * (q.out • i z).im ^ (s.re + 1) :=
      norm_complexPointSeed_sub_zero_physical_le hE J s (q.out • i z)
    _ ≤ (2 * Real.pi * E) * (ua q + ub q) :=
      mul_le_mul_of_nonneg_left hp (by positivity)
    _ = _ := by ring

/-- Linear energy growth in actual compact spatial norm for every nonnegative energy. -/
theorem exists_compactEnergySeries_physical_strip_norm_bound (K : Set ℂ) [CompactSpace K]
    (hKH : K ⊆ upperHalfPlaneSet) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∃ C : ℝ, 0 < C ∧ ∀ (E : ℝ), 0 ≤ E → ∀ (J : ℤ) (s : ℂ),
      a ≤ s.re → s.re ≤ b → ‖compactEnergySeries K hKH E J s‖ ≤ C * E := by
  obtain ⟨u, hu, hu0, hbound⟩ := compactEnergyTerm_physical_normal_on_strip K hKH ha hb
  have hsum0 : 0 ≤ ∑' q, u q := tsum_nonneg hu0
  refine ⟨(∑' q, u q) + 1, by linarith, ?_⟩
  intro E hE J s has hsb
  have hsum := compactEnergyTerm_summable_norm K hKH E J (ha.trans_le has)
  calc
    _ ≤ ∑' q : CuspCoset, ‖compactEnergyTerm K hKH E J s q‖ := norm_tsum_le_tsum_norm hsum
    _ ≤ ∑' q : CuspCoset, E * u q :=
      Summable.tsum_le_tsum (fun q => hbound E hE J q s has hsb) hsum (hu.mul_left E)
    _ = E * ∑' q, u q := tsum_mul_left
    _ ≤ _ := by nlinarith

/-- The threshold disk has a uniform polynomial spin and linear physical-energy bound,
with no upper cutoff on physical input energy. -/
theorem exists_continuedSeedOn_physical_norm_bound (K : Set ℂ) [CompactSpace K]
    (hKH : K ⊆ upperHalfPlaneSet) :
    ∃ C : ℝ, 0 < C ∧ ∀ (E : ℝ), 0 ≤ E → ∀ (J : ℤ) (κ : ℂ),
      ‖κ‖ ≤ (chosenContinuation K hKH).radius →
      ‖continuedSeedOn K hKH E J κ‖ ≤ C * (1 + (J : ℝ) ^ 2 + E) := by
  obtain ⟨C, hC, hb⟩ := exists_compactEnergySeries_physical_strip_norm_bound K hKH
    (a := 3 / 8) (b := 5 / 8) (by norm_num) (by norm_num)
  let D := chosenContinuation K hKH
  refine ⟨D.bound + C, add_pos D.bound_pos hC, ?_⟩
  intro E hE J κ hκ
  have hre : |κ.re| ≤ 1 / 8 :=
    (Complex.abs_re_le_norm κ).trans (hκ.trans D.radius_le_eighth)
  have hlow : (3 / 8 : ℝ) ≤ (exponent κ).re := by
    have := (abs_le.mp hre).1
    norm_num [exponent, Complex.add_re]
    linarith
  have hupp : (exponent κ).re ≤ (5 / 8 : ℝ) := by
    have := (abs_le.mp hre).2
    norm_num [exponent, Complex.add_re]
    linarith
  calc
    _ ≤ ‖D.family J κ‖ + ‖compactEnergySeries K hKH E J (exponent κ)‖ := norm_add_le _ _
    _ ≤ D.bound * (1 + (J : ℝ) ^ 2) + C * E :=
      add_le_add (D.uniform_bound J κ hκ) (hb E hE J (exponent κ) hlow hupp)
    _ ≤ _ := by
      nlinarith [mul_nonneg D.bound_pos.le hE, mul_nonneg hC.le (sq_nonneg (J : ℝ))]

/-- Every compact parameter set in the genuine connected continuation region has
one linear physical-energy bound for a fixed integer spin. -/
theorem exists_continuedSeedOn_physical_compact_norm_bound (K : Set ℂ) [CompactSpace K]
    (hKH : K ⊆ upperHalfPlaneSet) (J : ℤ) {L : Set ℂ} (hL : IsCompact L)
    (hLΩ : L ⊆ continuationRegion (chosenContinuation K hKH).radius) :
    ∃ C : ℝ, 0 < C ∧ ∀ (E : ℝ), 0 ≤ E → ∀ κ ∈ L,
      ‖continuedSeedOn K hKH E J κ‖ ≤ C * (1 + E) := by
  let D := chosenContinuation K hKH
  have hre : Continuous (fun κ : ℂ => (exponent κ).re) :=
    Complex.continuous_re.comp (continuous_const.add continuous_id)
  obtain ⟨a, ha, hlow⟩ := hL.exists_forall_le' hre.continuousOn
    (fun κ hκ => by
      have ht := re_gt_neg_half_of_mem_continuation D (hLΩ hκ)
      norm_num [exponent, Complex.add_re]
      linarith : ∀ κ ∈ L, 0 < (exponent κ).re)
  obtain ⟨B, hB, hbound⟩ := hL.isBounded.exists_pos_norm_le
  have hfamily : ContinuousOn (D.family J) L :=
    fun κ hκ => (D.analytic_family J κ (hLΩ hκ)).continuousAt.continuousWithinAt
  obtain ⟨C₀, hC₀⟩ := hL.exists_bound_of_continuousOn hfamily
  obtain ⟨C₁, hC₁, hcorr⟩ := exists_compactEnergySeries_physical_strip_norm_bound K hKH ha
    (b := B + 1) (by linarith)
  refine ⟨|C₀| + C₁ + 1, by positivity, ?_⟩
  intro E hE κ hκ
  have hupp : (exponent κ).re ≤ B + 1 := by
    have hh := (Complex.re_le_norm κ).trans (hbound κ hκ)
    norm_num [exponent, Complex.add_re]
    linarith
  calc
    _ ≤ ‖D.family J κ‖ + ‖compactEnergySeries K hKH E J (exponent κ)‖ := norm_add_le _ _
    _ ≤ C₀ + C₁ * E :=
      add_le_add (hC₀ κ hκ) (hcorr E hE J (exponent κ) (hlow κ hκ) hupp)
    _ ≤ _ := by nlinarith [le_abs_self C₀, abs_nonneg C₀]

/-- The local bound needed for dominated analytic integration is uniform on the
entire physical energy half-line, and its neighborhood lies in the actual continuation region. -/
theorem exists_continuedSeedOn_physical_local_norm_bound (K : Set ℂ) [CompactSpace K]
    (hKH : K ⊆ upperHalfPlaneSet) (J : ℤ) {κ₀ : ℂ}
    (hκ₀ : κ₀ ∈ continuationRegion (chosenContinuation K hKH).radius) :
    ∃ r C : ℝ, 0 < r ∧ 0 < C ∧
      Metric.ball κ₀ r ⊆ continuationRegion (chosenContinuation K hKH).radius ∧
      ∀ (E : ℝ), 0 ≤ E → ∀ κ ∈ Metric.ball κ₀ r,
        ‖continuedSeedOn K hKH E J κ‖ ≤ C * (1 + E) := by
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.mp
    ((isOpen_continuationRegion (chosenContinuation K hKH).radius).mem_nhds hκ₀)
  have hsub : Metric.closedBall κ₀ (ε / 2) ⊆
      continuationRegion (chosenContinuation K hKH).radius := by
    intro κ hκ
    apply hball κ
    exact (Metric.closedBall_subset_ball (by linarith : ε / 2 < ε)) hκ
  obtain ⟨C, hC, hb⟩ := exists_continuedSeedOn_physical_compact_norm_bound K hKH J
    (isCompact_closedBall κ₀ (ε / 2)) hsub
  exact ⟨ε / 2, C, half_pos hε, hC, Metric.ball_subset_closedBall.trans hsub,
    fun E hE κ hκ => hb E hE κ (Metric.ball_subset_closedBall hκ)⟩

end GapFamily.Analytic.PoincareEnergyContinuation
