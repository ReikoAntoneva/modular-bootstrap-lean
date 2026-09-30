import GapFamily.Analytic.Poincare.Continuation.PoincareCompactEnergyTerm
import GapFamily.Analytic.Cusp.Fourier.CuspFourierCutoffProfile
import Mathlib.Analysis.Complex.LocallyUniformLimit

/-! Actual C(K)-valued energy correction, using the extra orbit-height gain. -/
noncomputable section
namespace GapFamily.Analytic.PoincareEnergyConvergentAnalytic
open Set Filter MeasureTheory UpperHalfPlane
open scoped Topology

/-- The actual energy-difference terms have one summable compact norm majorant
on every positive exponent strip and bounded complex-energy range. The spin is
arbitrary and the bound retains the linear factor in the energy norm. -/
theorem compactEnergyTerm_normal_on_strip (K : Set ℂ) [CompactSpace K]
    (hKH : K ⊆ upperHalfPlaneSet) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (B : ℝ) :
    ∃ u : CuspCoset → ℝ, Summable u ∧ (∀ q, 0 ≤ u q) ∧
      ∀ (E : ℂ), ‖E‖ ≤ B → ∀ (J : ℤ) (q : CuspCoset) (s : ℂ),
        a ≤ s.re → s.re ≤ b → ‖compactEnergyTerm K hKH E J s q‖ ≤ ‖E‖ * u q := by
  let i : K → UpperHalfPlane := fun z => ⟨z, hKH z.property⟩
  have hi : Continuous i := continuous_subtype_val.upperHalfPlaneMk (fun z => hKH z.property)
  have hKi : IsCompact (range i) := isCompact_range hi
  obtain ⟨M, hM, ua, hua, hua0, hba⟩ :=
    exists_cusp_height_compact_majorant hKi (t := a + 1) (by linarith)
  obtain ⟨_, _, ub, hub, hub0, hbb⟩ :=
    exists_cusp_height_compact_majorant hKi (t := b + 1) (by linarith)
  let c : ℝ := 2 * Real.pi * Real.exp (2 * Real.pi * B * M)
  have hc : 0 ≤ c := by dsimp [c]; positivity
  refine ⟨fun q => c * (ua q + ub q), (hua.add hub).mul_left c,
    fun q => mul_nonneg hc (add_nonneg (hua0 q) (hub0 q)), ?_⟩
  intro E hE J q s has hsb
  apply (ContinuousMap.norm_le _
    (mul_nonneg (norm_nonneg E) (mul_nonneg hc (add_nonneg (hua0 q) (hub0 q))))).mpr
  intro z
  rw [compactEnergyTerm_apply, ofComplex_apply_of_im_pos (hKH z.property)]
  change ‖complexPoincareDifferenceTerm E J s (i z) q‖ ≤ _
  simp only [complexPoincareDifferenceTerm, complexPoincareTerm_out]
  have he : Real.exp (2 * Real.pi * ‖E‖ * M) ≤ Real.exp (2 * Real.pi * B * M) := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hE (by positivity)) hM.le
  have hp : (q.out • i z).im ^ (s.re + 1) ≤ ua q + ub q :=
    (rpow_le_add_endpoint (q.out • i z).im_pos
      (show a + 1 ≤ s.re + 1 by linarith) (show s.re + 1 ≤ b + 1 by linarith)).trans
      (add_le_add (hba q (i z) (mem_range_self z)).2 (hbb q (i z) (mem_range_self z)).2)
  calc
    _ ≤ (2 * Real.pi * ‖E‖ * Real.exp (2 * Real.pi * ‖E‖ * M)) *
        (q.out • i z).im ^ (s.re + 1) :=
      norm_complexPointSeed_sub_zero_energy_le E J s (q.out • i z)
        (hba q (i z) (mem_range_self z)).1
    _ ≤ (2 * Real.pi * ‖E‖ * Real.exp (2 * Real.pi * B * M)) * (ua q + ub q) :=
      mul_le_mul (mul_le_mul_of_nonneg_left he (by positivity)) hp
        (Real.rpow_nonneg (q.out • i z).im_pos.le _) (by positivity)
    _ = _ := by dsimp [c]; ring

/-- Absolute summability holds in the actual compact supremum norm for Re s>0. -/
theorem compactEnergyTerm_summable_norm (K : Set ℂ) [CompactSpace K]
    (hKH : K ⊆ upperHalfPlaneSet) (E : ℂ) (J : ℤ) {s : ℂ} (hs : 0 < s.re) :
    Summable (fun q : CuspCoset => ‖compactEnergyTerm K hKH E J s q‖) := by
  obtain ⟨u, hu, _, hbound⟩ := compactEnergyTerm_normal_on_strip K hKH hs hs ‖E‖
  exact (hu.mul_left ‖E‖).of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun q => hbound E le_rfl J q s le_rfl le_rfl)

/-- The literal sum of energy-difference terms, never a subtraction of divergent series. -/
def compactEnergySeries (K : Set ℂ) [CompactSpace K]
    (hKH : K ⊆ upperHalfPlaneSet) (E : ℂ) (J : ℤ) (s : ℂ) : C(K, ℂ) :=
  ∑' q : CuspCoset, compactEnergyTerm K hKH E J s q

/-- Evaluation is exactly the existing actual complex Poincaré energy correction. -/
theorem compactEnergySeries_apply (K : Set ℂ) [CompactSpace K]
    (hKH : K ⊆ upperHalfPlaneSet) (E : ℂ) (J : ℤ) {s : ℂ} (hs : 0 < s.re) (z : K) :
    compactEnergySeries K hKH E J s z = complexPoincareEnergyDifference E J s (ofComplex z.val) := by
  let ev : C(K, ℂ) →L[ℂ] ℂ := ContinuousMap.evalCLM ℂ z
  have h := (compactEnergyTerm_summable_norm K hKH E J hs).of_norm.hasSum.map
    ev.toAddMonoidHom ev.continuous
  change HasSum (fun q : CuspCoset => compactEnergyTerm K hKH E J s q z)
    (compactEnergySeries K hKH E J s z) at h
  simp only [compactEnergyTerm_apply] at h
  exact h.unique (hasSum_complexPoincareEnergyDifference E J hs (ofComplex z.val))

/-- Norm analyticity of the actual correction on its improved convergence half-plane. -/
theorem compactEnergySeries_analyticAt_exponent (K : Set ℂ) [CompactSpace K]
    (hKH : K ⊆ upperHalfPlaneSet) (E : ℂ) (J : ℤ) {s : ℂ} (hs : 0 < s.re) :
    AnalyticAt ℂ (compactEnergySeries K hKH E J) s := by
  let a : ℝ := s.re / 2
  let b : ℝ := s.re + 1
  have ha : 0 < a := half_pos hs
  have hb : 0 < b := by dsimp [b]; linarith
  let U : Set ℂ := {w : ℂ | a < w.re ∧ w.re < b}
  have hU : IsOpen U :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)
  have hsU : s ∈ U := by dsimp [U, a, b]; constructor <;> linarith
  obtain ⟨u, hu, _, hbound⟩ := compactEnergyTerm_normal_on_strip K hKH ha hb ‖E‖
  have hd : DifferentiableOn ℂ (compactEnergySeries K hKH E J) U := by
    apply Complex.differentiableOn_tsum_of_summable_norm (hu.mul_left ‖E‖)
    · intro q w _
      exact (compactEnergyTerm_analyticAt_exponent K hKH E J q w).differentiableAt.differentiableWithinAt
    · exact hU
    · intro q w hw
      exact hbound E le_rfl J q w hw.1.le hw.2.le
  exact hd.analyticAt (hU.mem_nhds hsU)

/-- The actual correction is norm analytic at every point of Re s>0. -/
theorem compactEnergySeries_analyticOnNhd_exponent (K : Set ℂ) [CompactSpace K]
    (hKH : K ⊆ upperHalfPlaneSet) (E : ℂ) (J : ℤ) :
    AnalyticOnNhd ℂ (compactEnergySeries K hKH E J) {s : ℂ | 0 < s.re} :=
  fun _ hs => compactEnergySeries_analyticAt_exponent K hKH E J hs

/-- In κ coordinates the actual correction is norm analytic through zero. -/
theorem compactEnergySeries_analyticAt_parameter (K : Set ℂ) [CompactSpace K]
    (hKH : K ⊆ upperHalfPlaneSet) (E : ℂ) (J : ℤ) {κ : ℂ}
    (hκ : (-1 / 2 : ℝ) < κ.re) :
    AnalyticAt ℂ (fun w => compactEnergySeries K hKH E J (CuspFourierCutoff.exponent w)) κ := by
  have hs : 0 < (CuspFourierCutoff.exponent κ).re := by
    norm_num [CuspFourierCutoff.exponent, Complex.add_re]
    linarith
  exact (compactEnergySeries_analyticAt_exponent K hKH E J hs).comp_of_eq
    (show AnalyticAt ℂ CuspFourierCutoff.exponent κ by unfold CuspFourierCutoff.exponent; fun_prop) rfl

/-- A fixed energy range gives a linear-energy norm bound on the threshold disk,
uniform in every integer spin and every observed point through the C(K) norm. -/
theorem exists_compactEnergySeries_parameter_norm_bound (K : Set ℂ) [CompactSpace K]
    (hKH : K ⊆ upperHalfPlaneSet) (B : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (E : ℂ), ‖E‖ ≤ B → ∀ (J : ℤ) (κ : ℂ), ‖κ‖ ≤ 1 / 8 →
      ‖compactEnergySeries K hKH E J (CuspFourierCutoff.exponent κ)‖ ≤ C * ‖E‖ := by
  obtain ⟨u, hu, hu0, hbound⟩ := compactEnergyTerm_normal_on_strip K hKH
    (a := 3 / 8) (b := 5 / 8) (by norm_num) (by norm_num) B
  have hsum0 : 0 ≤ ∑' q, u q := tsum_nonneg hu0
  refine ⟨(∑' q, u q) + 1, by linarith, ?_⟩
  intro E hE J κ hκ
  have hre : |κ.re| ≤ 1 / 8 := (Complex.abs_re_le_norm κ).trans hκ
  have hlow : (3 / 8 : ℝ) ≤ (CuspFourierCutoff.exponent κ).re := by
    have := (abs_le.mp hre).1
    norm_num [CuspFourierCutoff.exponent, Complex.add_re]
    linarith
  have hupp : (CuspFourierCutoff.exponent κ).re ≤ (5 / 8 : ℝ) := by
    have := (abs_le.mp hre).2
    norm_num [CuspFourierCutoff.exponent, Complex.add_re]
    linarith
  have hsum := compactEnergyTerm_summable_norm K hKH E J
    (s := CuspFourierCutoff.exponent κ) (by linarith)
  calc
    _ ≤ ∑' q : CuspCoset, ‖compactEnergyTerm K hKH E J (CuspFourierCutoff.exponent κ) q‖ :=
      norm_tsum_le_tsum_norm hsum
    _ ≤ ∑' q : CuspCoset, ‖E‖ * u q :=
      Summable.tsum_le_tsum (fun q => hbound E hE J q _ hlow hupp) hsum (hu.mul_left ‖E‖)
    _ = ‖E‖ * ∑' q, u q := tsum_mul_left
    _ ≤ _ := by nlinarith [norm_nonneg E]

end GapFamily.Analytic.PoincareEnergyConvergentAnalytic
