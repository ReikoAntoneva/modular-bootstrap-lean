import GapFamily.Analytic.Cusp.Green.CuspGreenOperatorBasic
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Interior smooth source density for the actual Green collar

The complex span of real smooth compactly supported sources lying strictly
inside the collar is dense in its literal Lebesgue `L²` space. Endpoint values
carry zero measure, so no positivity hypothesis on the upper endpoint is needed.
-/

noncomputable section

namespace GapFamily.Analytic

open MeasureTheory Set
open scoped ContDiff

/-- A real smooth source, regarded as complex-valued, in the actual collar space. -/
def cuspGreenSmoothRealSource (T : ℝ) (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) :
    Lp ℂ 2 (cuspGreenCollarMeasure 0 T) :=
  cuspGreenCollarSource 0 T (fun t => (φ t : ℂ))
    (Complex.continuous_ofReal.comp hφ.continuous)

theorem cuspGreenSmoothRealSource_coeFn (T : ℝ) (φ : ℝ → ℝ)
    (hφ : ContDiff ℝ ∞ φ) :
    cuspGreenSmoothRealSource T φ hφ =ᵐ[cuspGreenCollarMeasure 0 T]
      fun u : CuspGreenCollar 0 T => (φ u : ℂ) :=
  cuspGreenCollarSource_coeFn 0 T _ _

/-- The Hilbert pairing of a real source is the usual distribution pairing. -/
theorem cuspGreenSmoothRealSource_inner (T : ℝ) (φ : ℝ → ℝ)
    (hφ : ContDiff ℝ ∞ φ) (f : Lp ℂ 2 (cuspGreenCollarMeasure 0 T)) :
    inner ℂ (cuspGreenSmoothRealSource T φ hφ) f =
      ∫ u : CuspGreenCollar 0 T, φ u • f u ∂cuspGreenCollarMeasure 0 T := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [cuspGreenSmoothRealSource_coeFn T φ hφ] with u hu
  simp [hu, RCLike.inner_apply, Complex.real_smul, mul_comm]

/-- Interior real smooth tests separate every actual collar `L²` source. -/
theorem cuspGreenSmoothSource_separates (T : ℝ)
    (f : Lp ℂ 2 (cuspGreenCollarMeasure 0 T))
    (h : ∀ (φ : ℝ → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo 0 T →
      (∫ u : CuspGreenCollar 0 T, φ u • f u ∂cuspGreenCollarMeasure 0 T) = 0) :
    f = 0 := by
  let f₀ : ℝ → ℂ := Function.extend
    (Subtype.val : CuspGreenCollar 0 T → ℝ) f (fun _ => 0)
  have hf₀ (u : CuspGreenCollar 0 T) : f₀ u = f u :=
    Subtype.val_injective.extend_apply _ _ u
  have hmap : Measure.map (Subtype.val : CuspGreenCollar 0 T → ℝ)
      (cuspGreenCollarMeasure 0 T) = volume.restrict (Icc 0 T) :=
    map_comap_subtype_coe measurableSet_Icc volume
  have hmem : MemLp f₀ 2 (volume.restrict (Icc 0 T)) := by
    have htransport := (MeasurableEmbedding.subtype_coe measurableSet_Icc).memLp_map_measure_iff
        (g := f₀) (p := 2)
        (μ := cuspGreenCollarMeasure 0 T)
    rw [hmap] at htransport
    apply htransport.mpr
    have hcomp : f₀ ∘ (Subtype.val : CuspGreenCollar 0 T → ℝ) = f := funext hf₀
    rw [hcomp]
    exact Lp.memLp f
  have hfull : ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) T), t ∈ Ioo 0 T := by
    rw [← restrict_Ioo_eq_restrict_Icc]
    exact ae_restrict_mem measurableSet_Ioo
  have htest : ∀ (φ : ℝ → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo 0 T →
      (∫ t, φ t • f₀ t ∂volume.restrict (Icc 0 T)) = 0 := by
    intro φ hφ hc hs
    calc
      _ = ∫ u : CuspGreenCollar 0 T, φ u • f u ∂cuspGreenCollarMeasure 0 T := by
        rw [← integral_subtype_comap measurableSet_Icc]
        apply integral_congr_ae
        filter_upwards [] with u
        rw [hf₀]
      _ = 0 := h φ hφ hc hs
  have hz := isOpen_Ioo.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    ((hmem.locallyIntegrable (by norm_num)).locallyIntegrableOn (Ioo 0 T)) htest
  have hzero : ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) T), f₀ t = 0 := by
    filter_upwards [hz, hfull] with t ht hmem using ht hmem
  have hsub := (ae_restrict_iff_subtype measurableSet_Icc).mp hzero
  apply Lp.ext
  filter_upwards [hsub,
    Lp.coeFn_zero (E := ℂ) (p := 2) (μ := cuspGreenCollarMeasure 0 T)]
    with u hu hzero
  simpa only [hf₀, hzero, Pi.zero_apply] using hu

/-- The complex span of smooth real sources supported strictly inside the collar. -/
def cuspGreenSmoothSourceSpan (T : ℝ) :
    Submodule ℂ (Lp ℂ 2 (cuspGreenCollarMeasure 0 T)) :=
  Submodule.span ℂ {f | ∃ (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ),
    HasCompactSupport φ ∧ tsupport φ ⊆ Ioo 0 T ∧
      f = cuspGreenSmoothRealSource T φ hφ}

theorem cuspGreenSmoothRealSource_mem_span (T : ℝ) (φ : ℝ → ℝ)
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ Ioo 0 T) :
    cuspGreenSmoothRealSource T φ hφ ∈ cuspGreenSmoothSourceSpan T :=
  Submodule.subset_span ⟨φ, hφ, hc, hs, rfl⟩

/-- Genuine interior smooth-source density in the actual collar Hilbert space. -/
theorem cuspGreenSmoothSourceSpan_dense (T : ℝ) :
    Dense (cuspGreenSmoothSourceSpan T : Set (Lp ℂ 2 (cuspGreenCollarMeasure 0 T))) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top,
    Submodule.topologicalClosure_eq_top_iff, Submodule.eq_bot_iff]
  intro f hf
  apply cuspGreenSmoothSource_separates T f
  intro φ hφ hc hs
  rw [← cuspGreenSmoothRealSource_inner T φ hφ f]
  exact (cuspGreenSmoothSourceSpan T).inner_right_of_mem_orthogonal
    (cuspGreenSmoothRealSource_mem_span T φ hφ hc hs) hf

/-- Bounded source operators are determined by actual interior smooth sources. -/
theorem cuspGreenCollarOperator_ext_smoothSource (T : ℝ)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    {A B : Lp ℂ 2 (cuspGreenCollarMeasure 0 T) →L[ℂ] F}
    (h : ∀ (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ), HasCompactSupport φ →
      tsupport φ ⊆ Ioo 0 T →
      A (cuspGreenSmoothRealSource T φ hφ) = B (cuspGreenSmoothRealSource T φ hφ)) :
    A = B := by
  apply DFunLike.coe_injective
  apply Continuous.ext_on (cuspGreenSmoothSourceSpan_dense T) A.continuous B.continuous
  apply LinearMap.eqOn_span' (f := A.toLinearMap) (g := B.toLinearMap)
  rintro _ ⟨φ, hφ, hc, hs, rfl⟩
  exact h φ hφ hc hs

end GapFamily.Analytic
