import GapFamily.Analytic.Poincare.Seed.PoincareEnergyContinuation

noncomputable section
namespace GapFamily.Analytic.PoincareEnergyContinuation
open Set Filter UpperHalfPlane CuspFourierCutoff PoincareCanonical
open PoincareEnergyConvergentAnalytic
open scoped Topology

/-- A positive exponent strip gives a genuine compact norm bound, uniform in
spin and bounded energy, retaining the linear energy factor. -/
theorem exists_compactEnergySeries_strip_norm_bound (K : Set ℂ) [CompactSpace K]
    (hKH : K ⊆ upperHalfPlaneSet) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (B : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (E : ℂ), ‖E‖ ≤ B → ∀ (J : ℤ) (s : ℂ),
      a ≤ s.re → s.re ≤ b → ‖compactEnergySeries K hKH E J s‖ ≤ C * ‖E‖ := by
  obtain ⟨u, hu, hu0, hbound⟩ := compactEnergyTerm_normal_on_strip K hKH ha hb B
  have hsum0 : 0 ≤ ∑' q, u q := tsum_nonneg hu0
  refine ⟨(∑' q, u q) + 1, by linarith, ?_⟩
  intro E hE J s has hsb
  have hsum := compactEnergyTerm_summable_norm K hKH E J (ha.trans_le has)
  calc
    _ ≤ ∑' q : CuspCoset, ‖compactEnergyTerm K hKH E J s q‖ :=
      norm_tsum_le_tsum_norm hsum
    _ ≤ ∑' q : CuspCoset, ‖E‖ * u q :=
      Summable.tsum_le_tsum (fun q => hbound E hE J q s has hsb) hsum (hu.mul_left ‖E‖)
    _ = ‖E‖ * ∑' q, u q := tsum_mul_left
    _ ≤ _ := by nlinarith [norm_nonneg E]

/-- Near each actual continuation point, one compact norm bound controls every
energy in the prescribed ball. Only the spin is fixed; no joint regularity premise is used. -/
theorem exists_continuedSeedOn_local_norm_bound (K : Set ℂ) [CompactSpace K]
    (hKH : K ⊆ upperHalfPlaneSet) (B : ℝ) (J : ℤ) {κ₀ : ℂ}
    (hκ₀ : κ₀ ∈ continuationRegion (chosenContinuation K hKH).radius) :
    ∃ r C : ℝ, 0 < r ∧ 0 < C ∧
      Metric.ball κ₀ r ⊆ continuationRegion (chosenContinuation K hKH).radius ∧
      ∀ (E : ℂ), ‖E‖ ≤ B → ∀ κ ∈ Metric.ball κ₀ r,
        ‖continuedSeedOn K hKH E J κ‖ ≤ C := by
  let D := chosenContinuation K hKH
  have hs : 0 < (exponent κ₀).re := by
    have h := re_gt_neg_half_of_mem_continuation D hκ₀
    norm_num [exponent, Complex.add_re]
    linarith
  let a : ℝ := (exponent κ₀).re / 2
  let b : ℝ := (exponent κ₀).re + 1
  have ha : 0 < a := half_pos hs
  have hb : 0 < b := by dsimp [b]; linarith
  have hap : a < (exponent κ₀).re := by dsimp [a]; linarith
  have hbp : (exponent κ₀).re < b := by dsimp [b]; linarith
  have hc : Continuous (fun κ : ℂ => (exponent κ).re) :=
    Complex.continuous_re.comp (continuous_const.add continuous_id)
  have hstrip : ∀ᶠ κ in 𝓝 κ₀, a < (exponent κ).re ∧ (exponent κ).re < b :=
    ((isOpen_lt continuous_const hc).inter (isOpen_lt hc continuous_const)).mem_nhds ⟨hap, hbp⟩
  have hnorm : ∀ᶠ κ in 𝓝 κ₀, ‖D.family J κ‖ < ‖D.family J κ₀‖ + 1 :=
    (D.analytic_family J κ₀ hκ₀).continuousAt.norm.eventually
      (Iio_mem_nhds (lt_add_one _))
  have hnear : ∀ᶠ κ in 𝓝 κ₀,
      κ ∈ continuationRegion D.radius ∧ a < (exponent κ).re ∧
        (exponent κ).re < b ∧ ‖D.family J κ‖ < ‖D.family J κ₀‖ + 1 := by
    filter_upwards [(isOpen_continuationRegion D.radius).mem_nhds hκ₀, hstrip, hnorm]
      with κ hΩ hstrip hnorm
    exact ⟨hΩ, hstrip.1, hstrip.2, hnorm⟩
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.mp hnear
  obtain ⟨C₁, hC₁, hbound⟩ := exists_compactEnergySeries_strip_norm_bound K hKH ha hb B
  refine ⟨r, ‖D.family J κ₀‖ + 1 + C₁ * |B|, hr, ?_, ?_, ?_⟩
  · positivity
  · intro κ hκ
    exact (hball κ hκ).1
  · intro E hE κ hκ
    obtain ⟨_, hka, hkb, hnorm⟩ := hball κ hκ
    calc
      _ ≤ ‖D.family J κ‖ + ‖compactEnergySeries K hKH E J (exponent κ)‖ :=
        norm_add_le _ _
      _ ≤ (‖D.family J κ₀‖ + 1) + C₁ * ‖E‖ :=
        add_le_add hnorm.le (hbound E hE J (exponent κ) hka.le hkb.le)
      _ ≤ _ := add_le_add le_rfl
        (mul_le_mul_of_nonneg_left (hE.trans (le_abs_self B)) hC₁.le)

end GapFamily.Analytic.PoincareEnergyContinuation
