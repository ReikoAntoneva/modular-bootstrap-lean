import GapFamily.Analytic.Modular.Periodization.ModularPeriodizationDensity
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-!
# Hilbert restriction to the actual high cusp

Restriction uses the literal restricted hyperbolic measure. Its right inverse
is extension by zero, and the smooth automorphic core remains dense after
restriction. No horizontal averaging operator is defined in this module.
-/

noncomputable section

namespace GapFamily.Analytic

open MeasureTheory Set Filter UpperHalfPlane

/-- The actual complex L² space above height H. -/
abbrev cuspHilbert (H : ℝ) :=
  Lp ℂ 2 (modularMeasure.restrict {τ : UpperHalfPlane | H < τ.im})

theorem measurableSet_highCusp (H : ℝ) :
    MeasurableSet {τ : UpperHalfPlane | H < τ.im} :=
  (isOpen_lt continuous_const UpperHalfPlane.continuous_im).measurableSet

private def cuspRestrictReal (H : ℝ) : ModularHilbert →L[ℝ] cuspHilbert H :=
  Lp.LpToLpOfMeasureLeSMul (c := 1) (by simp)
    (by simpa using (Measure.restrict_le_self :
      modularMeasure.restrict {τ : UpperHalfPlane | H < τ.im} ≤ modularMeasure))

private theorem cuspRestrictReal_ae (H : ℝ) (f : ModularHilbert) :
    cuspRestrictReal H f =ᵐ[modularMeasure.restrict {τ : UpperHalfPlane | H < τ.im}] f :=
  Lp.coeFn_LpToLpOfMeasureLeSMul _ _ _

/-- Restriction to the actual high-cusp L² space, as a complex-linear map. -/
def cuspRestrict (H : ℝ) : ModularHilbert →L[ℂ] cuspHilbert H where
  toFun := cuspRestrictReal H
  map_add' := map_add _
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [cuspRestrictReal_ae H (c • f),
      ae_restrict_of_ae (Lp.coeFn_smul c f),
      Lp.coeFn_smul c (cuspRestrictReal H f), cuspRestrictReal_ae H f] with τ hr hs ht hf
    simp only [RingHom.id_apply, hr, hs, ht, Pi.smul_apply, hf]
  cont := (cuspRestrictReal H).continuous

theorem cuspRestrict_ae (H : ℝ) (f : ModularHilbert) :
    cuspRestrict H f =ᵐ[modularMeasure.restrict {τ : UpperHalfPlane | H < τ.im}] f :=
  cuspRestrictReal_ae H f

/-- Restriction is a contraction. -/
theorem cuspRestrict_norm_le_one (H : ℝ) : ‖cuspRestrict H‖ ≤ 1 := by
  have hr : ‖cuspRestrictReal H‖ ≤ 1 := by
    simpa [cuspRestrictReal] using
      (Lp.norm_LpToLpOfMeasureLeSMul_le (E := ℂ) (p := 2) (c := 1)
        (μ := modularMeasure.restrict {τ : UpperHalfPlane | H < τ.im})
        (ν := modularMeasure) (by simp) (by simpa using Measure.restrict_le_self))
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  exact ((cuspRestrictReal H).le_opNorm f).trans (mul_le_mul_of_nonneg_right hr (norm_nonneg f))

theorem norm_cuspRestrict_le (H : ℝ) (f : ModularHilbert) :
    ‖cuspRestrict H f‖ ≤ ‖f‖ := by
  exact ((cuspRestrict H).le_opNorm f).trans
    (by simpa using mul_le_mul_of_nonneg_right (cuspRestrict_norm_le_one H) (norm_nonneg f))

def cuspZeroExtend (H : ℝ) (f : cuspHilbert H) : ModularHilbert :=
  ((memLp_indicator_iff_restrict (measurableSet_highCusp H)).mpr (Lp.memLp f)).toLp _

theorem cuspZeroExtend_ae (H : ℝ) (f : cuspHilbert H) :
    cuspZeroExtend H f =ᵐ[modularMeasure] {τ : UpperHalfPlane | H < τ.im}.indicator f :=
  MemLp.coeFn_toLp _

theorem cuspZeroExtend_norm (H : ℝ) (f : cuspHilbert H) :
    ‖cuspZeroExtend H f‖ = ‖f‖ := by
  rw [cuspZeroExtend, Lp.norm_toLp, eLpNorm_indicator_eq_eLpNorm_restrict (measurableSet_highCusp H), Lp.norm_def]

theorem cuspZeroExtend_restrict_ae (H : ℝ) (f : cuspHilbert H) :
    cuspZeroExtend H f =ᵐ[modularMeasure.restrict {τ : UpperHalfPlane | H < τ.im}] f :=
  Filter.EventuallyEq.trans (cuspZeroExtend_ae H f).restrict
    (indicator_ae_eq_restrict (measurableSet_highCusp H))

theorem cuspZeroExtend_add (H : ℝ) (f g : cuspHilbert H) :
    cuspZeroExtend H (f + g) = cuspZeroExtend H f + cuspZeroExtend H g := by
  apply Lp.ext
  have hadd := (ae_eq_restrict_iff_indicator_ae_eq (measurableSet_highCusp H)).mp
    (Lp.coeFn_add f g)
  filter_upwards [cuspZeroExtend_ae H (f + g), cuspZeroExtend_ae H f,
    cuspZeroExtend_ae H g, Lp.coeFn_add (cuspZeroExtend H f) (cuspZeroExtend H g),
    hadd] with τ hfg hf hg hsum hinner
  simp only [Pi.add_apply] at hsum
  rw [hfg, hsum, hf, hg, hinner]
  by_cases hτ : H < τ.im <;> simp [hτ]

theorem cuspZeroExtend_smul (H : ℝ) (c : ℂ) (f : cuspHilbert H) :
    cuspZeroExtend H (c • f) = c • cuspZeroExtend H f := by
  apply Lp.ext
  have hsmul := (ae_eq_restrict_iff_indicator_ae_eq (measurableSet_highCusp H)).mp
    (Lp.coeFn_smul c f)
  filter_upwards [cuspZeroExtend_ae H (c • f), cuspZeroExtend_ae H f,
    Lp.coeFn_smul c (cuspZeroExtend H f), hsmul] with τ hcf hf houter hinner
  simp only [Pi.smul_apply] at houter
  rw [hcf, houter, hf, hinner]
  by_cases hτ : H < τ.im <;> simp [hτ]

def cuspZeroExtension (H : ℝ) : cuspHilbert H →ₗᵢ[ℂ] ModularHilbert where
  toFun := cuspZeroExtend H
  map_add' := cuspZeroExtend_add H
  map_smul' := cuspZeroExtend_smul H
  norm_map' := cuspZeroExtend_norm H


/-- Extension by zero is a right inverse to actual cusp restriction. -/
theorem cuspRestrict_zeroExtend (H : ℝ) (f : cuspHilbert H) :
    cuspRestrict H (cuspZeroExtend H f) = f := by
  apply Lp.ext
  exact (cuspRestrict_ae H (cuspZeroExtend H f)).trans (cuspZeroExtend_restrict_ae H f)

theorem cuspRestrict_surjective (H : ℝ) : Function.Surjective (cuspRestrict H) :=
  fun f => ⟨cuspZeroExtend H f, cuspRestrict_zeroExtend H f⟩

/-- The actual restriction of a finite-energy smooth automorphic core value. -/
def cuspCoreValue (H : ℝ) : ModularGradient.smoothCore →ₗ[ℂ] cuspHilbert H :=
  (cuspRestrict H).toLinearMap.comp ModularGradient.value

theorem cuspCoreValue_ae (H : ℝ) (F : ModularGradient.smoothCore) :
    cuspCoreValue H F =ᵐ[modularMeasure.restrict {τ : UpperHalfPlane | H < τ.im}]
      fun τ : UpperHalfPlane => F.val τ :=
  (cuspRestrict_ae H (ModularGradient.value F)).trans
    (ae_restrict_of_ae (ModularGradient.value_ae F))

/-- Restricting the actual smooth automorphic core still gives a dense set of cusp values. -/
theorem cuspCoreValue_dense_range (H : ℝ) : DenseRange (cuspCoreValue H) := by
  change Dense (Set.range ((cuspRestrict H) ∘ ModularGradient.value))
  rw [Set.range_comp]
  exact (cuspRestrict_surjective H).denseRange.dense_image (cuspRestrict H).continuous
    ModularGradient.value_dense_range

end GapFamily.Analytic
