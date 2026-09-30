import GapFamily.Analytic.Poincare.Continuation.PoincareCompactTermAnalytic
import GapFamily.Analytic.Cusp.Fourier.CuspFourierCutoffProfile
import Mathlib.Analysis.Complex.LocallyUniformLimit

/-! Actual normally convergent C(K)-valued Poincaré series on Re s>1. -/
noncomputable section
namespace GapFamily.Analytic.PoincareConvergentAnalytic
open Set Filter MeasureTheory UpperHalfPlane
open scoped Topology

/-- Two actual compact-height majorants control a full closed parameter strip
in the supremum norm, including for empty or thin compact observation sets. -/
theorem compactTerm_normal_on_strip (K : Set ℂ) [CompactSpace K]
    (hKH : K ⊆ upperHalfPlaneSet) (J : ℤ) {a b : ℝ} (ha : 1 < a) (hb : 1 < b) :
    ∃ u : CuspCoset → ℝ, Summable u ∧ (∀ q, 0 ≤ u q) ∧
      ∀ (q : CuspCoset) (s : ℂ), a ≤ s.re → s.re ≤ b →
        ‖compactTerm K hKH J s q‖ ≤ u q := by
  let i : K → UpperHalfPlane := fun z => ⟨z, hKH z.property⟩
  have hi : Continuous i := continuous_subtype_val.upperHalfPlaneMk (fun z => hKH z.property)
  have hKi : IsCompact (range i) := isCompact_range hi
  obtain ⟨_, _, ua, hua, hua0, hba⟩ := exists_cusp_height_compact_majorant hKi ha
  obtain ⟨_, _, ub, hub, hub0, hbb⟩ := exists_cusp_height_compact_majorant hKi hb
  refine ⟨fun q => ua q + ub q, hua.add hub, fun q => add_nonneg (hua0 q) (hub0 q), ?_⟩
  intro q s has hsb
  apply (ContinuousMap.norm_le _ (add_nonneg (hua0 q) (hub0 q))).mpr
  intro z
  rw [compactTerm_apply, ofComplex_apply_of_im_pos (hKH z.property)]
  change ‖complexPoincareTerm 0 J s (i z) q‖ ≤ ua q + ub q
  rw [complexPoincareTerm_out, norm_complexPointSeed]
  simp only [Complex.zero_re, mul_zero, zero_mul, Real.exp_zero, mul_one]
  exact (rpow_le_add_endpoint (q.out • i z).im_pos has hsb).trans
    (add_le_add (hba q (i z) (mem_range_self z)).2 (hbb q (i z) (mem_range_self z)).2)

/-- The genuine term series is absolutely summable in C(K) throughout Re s>1. -/
theorem compactTerm_summable_norm (K : Set ℂ) [CompactSpace K]
    (hKH : K ⊆ upperHalfPlaneSet) (J : ℤ) {s : ℂ} (hs : 1 < s.re) :
    Summable (fun q : CuspCoset => ‖compactTerm K hKH J s q‖) := by
  obtain ⟨u, hu, _, hbound⟩ := compactTerm_normal_on_strip K hKH J hs hs
  exact hu.of_nonneg_of_le (fun _ => norm_nonneg _) (fun q => hbound q s le_rfl le_rfl)

/-- The actual sum of the literal spatially restricted Poincaré summands. -/
def compactSeries (K : Set ℂ) [CompactSpace K] (hKH : K ⊆ upperHalfPlaneSet)
    (J : ℤ) (s : ℂ) : C(K, ℂ) :=
  ∑' q : CuspCoset, compactTerm K hKH J s q

/-- Its value is the full original convergent zero-energy Poincaré series. -/
theorem compactSeries_apply (K : Set ℂ) [CompactSpace K] (hKH : K ⊆ upperHalfPlaneSet)
    (J : ℤ) {s : ℂ} (hs : 1 < s.re) (z : K) :
    compactSeries K hKH J s z = complexPoincareSeries 0 J s (ofComplex z.val) := by
  let ev : C(K, ℂ) →L[ℂ] ℂ := ContinuousMap.evalCLM ℂ z
  have h := (compactTerm_summable_norm K hKH J hs).of_norm.hasSum.map
    ev.toAddMonoidHom ev.continuous
  change HasSum (fun q : CuspCoset => compactTerm K hKH J s q z)
    (compactSeries K hKH J s z) at h
  simp only [compactTerm_apply] at h
  exact h.unique (hasSum_complexPoincareTerm 0 J hs (ofComplex z.val))

/-- The actual restricted Poincaré sum is analytic in the supremum norm on the
whole original convergence half-plane. -/
theorem compactSeries_analyticAt (K : Set ℂ) [CompactSpace K]
    (hKH : K ⊆ upperHalfPlaneSet) (J : ℤ) {s : ℂ} (hs : 1 < s.re) :
    AnalyticAt ℂ (compactSeries K hKH J) s := by
  let a : ℝ := (1 + s.re) / 2
  let b : ℝ := s.re + 1
  have ha : 1 < a := by dsimp [a]; linarith
  have hb : 1 < b := by dsimp [b]; linarith
  let U : Set ℂ := {w : ℂ | a < w.re ∧ w.re < b}
  have hU : IsOpen U :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)
  have hsU : s ∈ U := by dsimp [U, a, b]; constructor <;> linarith
  obtain ⟨u, hu, _, hbound⟩ := compactTerm_normal_on_strip K hKH J ha hb
  have hd : DifferentiableOn ℂ (compactSeries K hKH J) U := by
    apply Complex.differentiableOn_tsum_of_summable_norm hu
    · intro q w _
      exact (compactTerm_analyticAt K hKH J q w).differentiableAt.differentiableWithinAt
    · exact hU
    · intro q w hw
      exact hbound q w hw.1.le hw.2.le
  exact hd.analyticAt (hU.mem_nhds hsU)

/-- The norm-analytic family is defined on every point of the full convergence region. -/
theorem compactSeries_analyticOnNhd (K : Set ℂ) [CompactSpace K]
    (hKH : K ⊆ upperHalfPlaneSet) (J : ℤ) :
    AnalyticOnNhd ℂ (compactSeries K hKH J) {s : ℂ | 1 < s.re} :=
  fun _ hs => compactSeries_analyticAt K hKH J hs

/-- The same actual C(K) family in the source parameter κ, in Re κ>1/2. -/
theorem compactSeries_exponent_analyticAt (K : Set ℂ) [CompactSpace K]
    (hKH : K ⊆ upperHalfPlaneSet) (J : ℤ) {κ : ℂ} (hκ : (1 / 2 : ℝ) < κ.re) :
    AnalyticAt ℂ (fun w => compactSeries K hKH J (CuspFourierCutoff.exponent w)) κ := by
  have hs : 1 < (CuspFourierCutoff.exponent κ).re := by
    norm_num [CuspFourierCutoff.exponent, Complex.add_re]
    linarith
  exact (compactSeries_analyticAt K hKH J hs).comp_of_eq
    (show AnalyticAt ℂ CuspFourierCutoff.exponent κ by unfold CuspFourierCutoff.exponent; fun_prop) rfl

end GapFamily.Analytic.PoincareConvergentAnalytic
