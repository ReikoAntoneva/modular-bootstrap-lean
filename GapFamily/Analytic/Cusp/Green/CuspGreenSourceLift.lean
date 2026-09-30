import GapFamily.Analytic.Cusp.CuspCoordinateDeriv
import Mathlib.Topology.Algebra.Support
import GapFamily.Analytic.Cusp.Profile.CuspProfileNorm
import GapFamily.Analytic.Cusp.Profile.CuspLogCoordinateBasic
import GapFamily.Analytic.Cusp.Green.CuspGreenOperatorBasic

noncomputable section
namespace GapFamily.Analytic
open Set
open scoped ContDiff

/-- The actual square-root lift is supported in the exponential image of the source support. -/
theorem cuspGreenSourceProfile_tsupport_subset_exp_image (f : ℝ → ℂ)
    (hfc : HasCompactSupport f) :
    tsupport (cuspLift f) ⊆ Real.exp '' tsupport f := by
  apply closure_minimal _ (hfc.isCompact.image Real.continuous_exp).isClosed
  intro y hy
  change cuspLift f y ≠ 0 at hy
  have hypos : 0 < y := by
    by_contra hyn
    have hys : Real.sqrt y = 0 := Real.sqrt_eq_zero_of_nonpos (le_of_not_gt hyn)
    exact hy (by simp [cuspLift, hys])
  have hfn : f (Real.log y) ≠ 0 := by
    intro hz
    exact hy (by simp [cuspLift, hz])
  exact ⟨Real.log y, subset_tsupport f hfn, Real.exp_log hypos⟩

/-- Compactness is transported through the actual exponential coordinate map. -/
theorem cuspGreenSourceProfile_hasCompactSupport (f : ℝ → ℂ)
    (hfc : HasCompactSupport f) : HasCompactSupport (cuspLift f) :=
  (hfc.isCompact.image Real.continuous_exp).of_isClosed_subset
    (isClosed_tsupport _) (cuspGreenSourceProfile_tsupport_subset_exp_image f hfc)

/-- A source supported strictly above log height zero lifts strictly above height one. -/
theorem cuspGreenSourceProfile_tsupport_subset (f : ℝ → ℂ)
    (hfc : HasCompactSupport f) (hfs : tsupport f ⊆ Ioi (0 : ℝ)) :
    tsupport (cuspLift f) ⊆ Ioi (1 : ℝ) := by
  intro y hy
  obtain ⟨t, ht, rfl⟩ := cuspGreenSourceProfile_tsupport_subset_exp_image f hfc hy
  exact Real.one_lt_exp_iff.mpr (hfs ht)

/-- The actual lifted source is globally smooth, including across nonpositive
heights where the support condition makes it locally zero. -/
theorem cuspGreenSourceProfile_contDiff (f : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (hfs : tsupport f ⊆ Ioi (0 : ℝ)) : ContDiff ℝ ∞ (cuspLift f) := by
  have hs := cuspGreenSourceProfile_tsupport_subset f hfc hfs
  apply contDiff_iff_contDiffAt.mpr
  intro y
  by_cases hy : 0 < y
  · exact (Real.contDiffAt_sqrt (ne_of_gt hy)).smul
      (hf.contDiffAt.comp y (Real.contDiffAt_log.mpr (ne_of_gt hy)))
  · have hys : y ∉ tsupport (cuspLift f) := by
      intro h
      have hy1 : (1 : ℝ) < y := hs h
      exact hy (lt_trans (by norm_num : (0 : ℝ) < 1) hy1)
    apply (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
    exact notMem_tsupport_iff_eventuallyEq.mp hys


end GapFamily.Analytic


noncomputable section
namespace GapFamily.Analytic
open Set Filter MeasureTheory ModularGradient
open scoped Topology ContDiff

/-- The actual modular Hilbert source associated with a compact positive logarithmic profile. -/
def cuspGreenSourceLift (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (hs : tsupport f ⊆ Ioi (0 : ℝ)) : ModularHilbert :=
  value (cuspProfileCore (cuspLift f) (cuspGreenSourceProfile_contDiff f hf hc hs)
    (cuspGreenSourceProfile_hasCompactSupport f hc)
    (cuspGreenSourceProfile_tsupport_subset f hc hs))

/-- Its actual representative is the literal square-root/logarithmic lift. -/
theorem cuspGreenSourceLift_value_ae (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (hs : tsupport f ⊆ Ioi (0 : ℝ)) :
    cuspGreenSourceLift f hf hc hs =ᵐ[modularMeasure]
      (fun τ : UpperHalfPlane => cuspLift f τ.im) :=
  cuspProfileCore_value_ae _ _ _ _

/-- The same representative written as a source supported above the true cusp boundary. -/
theorem cuspGreenSourceLift_ae (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (hs : tsupport f ⊆ Ioi (0 : ℝ)) :
    cuspGreenSourceLift f hf hc hs =ᵐ[modularMeasure]
      (fun τ : UpperHalfPlane => if 1 < τ.im then
        Real.sqrt τ.im • f (Real.log τ.im) else 0) := by
  filter_upwards [cuspGreenSourceLift_value_ae f hf hc hs] with τ hτ
  rw [hτ]
  by_cases hy : 1 < τ.im
  · simp only [hy, ite_true, cuspLift]
  · rw [ite_eq_right hy]
    exact image_eq_zero_of_notMem_tsupport
      (fun h => hy (cuspGreenSourceProfile_tsupport_subset f hc hs h))

/-- The actual logarithmic coordinate of this lifted source is the original profile. -/
theorem cuspLogCoordinate_cuspLift_source (f : ℝ → ℂ) :
    cuspLogCoordinate (cuspLift f) = f := by
  rw [cuspLogCoordinate_eq_cuspPullback, cuspPullback_cuspLift]

/-- Exact ordinary source mass, using the genuine modular norm and exponential substitution. -/
theorem cuspGreenSourceLift_norm_sq (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (hs : tsupport f ⊆ Ioi (0 : ℝ)) :
    ‖cuspGreenSourceLift f hf hc hs‖ ^ 2 = ∫ t : ℝ in Ioi 0, ‖f t‖ ^ 2 := by
  unfold cuspGreenSourceLift
  rw [(cuspProfileCore_value_norm_sq _ _ _ _).2,
    integral_cuspLogCoordinate_mass (cuspGreenSourceProfile_contDiff f hf hc hs).continuous
      (cuspGreenSourceProfile_hasCompactSupport f hc)
      (cuspGreenSourceProfile_tsupport_subset f hc hs), cuspLogCoordinate_cuspLift_source]

/-- The ordinary logarithmic squared mass is integrable before any norm identity is used. -/
theorem cuspGreenSourceLift_mass_integrable (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) : Integrable (fun t => ‖f t‖ ^ 2) := by
  have hn : HasCompactSupport (fun t => ‖f t‖ ^ 2) :=
    hc.comp_left (g := fun z : ℂ => ‖z‖ ^ 2) (by simp)
  exact (hf.continuous.norm.pow 2).integrable_of_hasCompactSupport hn

/-- The literal collar source norm is its ordinary Lebesgue squared mass. -/
theorem cuspGreenCollarSource_norm_sq (T : ℝ) (f : ℝ → ℂ) (hf : Continuous f) :
    ‖cuspGreenCollarSource 0 T f hf‖ ^ 2 = ∫ t : ℝ in Icc 0 T, ‖f t‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  simp only [real_inner_self_eq_norm_sq]
  calc
    _ = ∫ u : CuspGreenCollar 0 T, ‖f u‖ ^ 2 ∂cuspGreenCollarMeasure 0 T := by
      apply integral_congr_ae
      filter_upwards [cuspGreenCollarSource_coeFn 0 T f hf] with u hu
      rw [hu]
    _ = _ := integral_subtype_comap measurableSet_Icc (fun t => ‖f t‖ ^ 2)

/-- Smooth interior sources have identical norms in the actual collar and modular spaces. -/
theorem cuspGreenSourceLift_collar_norm_sq (T : ℝ) (f : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (hs : tsupport f ⊆ Ioo (0 : ℝ) T) :
    ‖cuspGreenSourceLift f hf hc (hs.trans Ioo_subset_Ioi_self)‖ ^ 2 =
      ‖cuspGreenCollarSource 0 T f hf.continuous‖ ^ 2 := by
  rw [cuspGreenSourceLift_norm_sq, cuspGreenCollarSource_norm_sq]
  have hlo : (∫ t : ℝ in Ioi 0, ‖f t‖ ^ 2) = ∫ t : ℝ, ‖f t‖ ^ 2 := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro t ht
    have hz : f t = 0 := image_eq_zero_of_notMem_tsupport (fun h => ht (hs h).1)
    simp only [hz, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
  have hcc : (∫ t : ℝ in Icc 0 T, ‖f t‖ ^ 2) = ∫ t : ℝ, ‖f t‖ ^ 2 := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro t ht
    have hz : f t = 0 := image_eq_zero_of_notMem_tsupport
      (fun h => ht ⟨(hs h).1.le, (hs h).2.le⟩)
    simp only [hz, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
  exact hlo.trans hcc.symm

theorem cuspGreenSourceLift_collar_norm (T : ℝ) (f : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (hs : tsupport f ⊆ Ioo (0 : ℝ) T) :
    ‖cuspGreenSourceLift f hf hc (hs.trans Ioo_subset_Ioi_self)‖ =
      ‖cuspGreenCollarSource 0 T f hf.continuous‖ :=
  (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (cuspGreenSourceLift_collar_norm_sq T f hf hc hs)

end GapFamily.Analytic
