import GapFamily.Analytic.Cusp.Fourier.CuspHorizontalHilbertBasic

/-!
# Literal modular truncation by height

The high-height projection is actual cusp restriction followed by extension
by zero. Its complementary projection is precisely multiplication by the
indicator of `τ.im ≤ H`. Both are contractions for every real cutoff height;
the complementary inequalities partition even the height boundary exactly.
-/

noncomputable section

namespace GapFamily.Analytic

open MeasureTheory Set Filter UpperHalfPlane

theorem measurableSet_lowCusp (H : ℝ) :
    MeasurableSet {τ : UpperHalfPlane | τ.im ≤ H} :=
  (isClosed_le UpperHalfPlane.continuous_im continuous_const).measurableSet

/-- The literal high-height projection in the ambient modular `L²` space. -/
def modularHighCut (H : ℝ) : ModularHilbert →L[ℂ] ModularHilbert :=
  (cuspZeroExtension H).toContinuousLinearMap.comp (cuspRestrict H)

theorem modularHighCut_apply (H : ℝ) (f : ModularHilbert) :
    modularHighCut H f = cuspZeroExtend H (cuspRestrict H f) := rfl

theorem modularHighCut_ae (H : ℝ) (f : ModularHilbert) :
    modularHighCut H f =ᵐ[modularMeasure]
      {τ : UpperHalfPlane | H < τ.im}.indicator f :=
  (cuspZeroExtend_ae H (cuspRestrict H f)).trans
    ((ae_eq_restrict_iff_indicator_ae_eq (measurableSet_highCusp H)).mp
      (cuspRestrict_ae H f))

theorem norm_modularHighCut (H : ℝ) (f : ModularHilbert) :
    ‖modularHighCut H f‖ = ‖cuspRestrict H f‖ :=
  cuspZeroExtend_norm H (cuspRestrict H f)

theorem norm_modularHighCut_le (H : ℝ) (f : ModularHilbert) :
    ‖modularHighCut H f‖ ≤ ‖f‖ := by
  rw [norm_modularHighCut]
  exact norm_cuspRestrict_le H f

theorem modularHighCut_norm_le_one (H : ℝ) : ‖modularHighCut H‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  simpa only [one_mul] using norm_modularHighCut_le H f

/-- Literal projection onto heights at most `H`, in the actual modular `L²` space. -/
def modularLowCut (H : ℝ) : ModularHilbert →L[ℂ] ModularHilbert :=
  ContinuousLinearMap.id ℂ ModularHilbert - modularHighCut H

theorem modularLowCut_apply (H : ℝ) (f : ModularHilbert) :
    modularLowCut H f = f - modularHighCut H f := rfl

/-- The completed operator is the ordinary low-height indicator on every `L²` class. -/
theorem modularLowCut_ae (H : ℝ) (f : ModularHilbert) :
    modularLowCut H f =ᵐ[modularMeasure]
      {τ : UpperHalfPlane | τ.im ≤ H}.indicator f := by
  filter_upwards [Lp.coeFn_sub f (modularHighCut H f), modularHighCut_ae H f] with τ hs hh
  change (f - modularHighCut H f) τ = _
  rw [hs, Pi.sub_apply, hh]
  by_cases hτ : τ.im ≤ H
  · simp [hτ, not_lt.mpr hτ]
  · simp [hτ, lt_of_not_ge hτ]

theorem norm_modularLowCut_le (H : ℝ) (f : ModularHilbert) :
    ‖modularLowCut H f‖ ≤ ‖f‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [modularLowCut_ae H f] with τ hτ
  rw [hτ]
  by_cases ht : τ.im ≤ H <;> simp [ht]

theorem modularLowCut_norm_le_one (H : ℝ) : ‖modularLowCut H‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  simpa only [one_mul] using norm_modularLowCut_le H f

/-- The low and high height pieces reconstruct the actual modular vector. -/
theorem modularLowCut_add_highCut (H : ℝ) (f : ModularHilbert) :
    modularLowCut H f + modularHighCut H f = f :=
  sub_add_cancel f (modularHighCut H f)

theorem modularLowCut_add_highCut_eq_id (H : ℝ) :
    modularLowCut H + modularHighCut H = ContinuousLinearMap.id ℂ ModularHilbert := by
  apply ContinuousLinearMap.ext
  intro f
  exact modularLowCut_add_highCut H f

theorem cuspRestrict_modularLowCut (H : ℝ) (f : ModularHilbert) :
    cuspRestrict H (modularLowCut H f) = 0 := by
  change cuspRestrict H (f - cuspZeroExtend H (cuspRestrict H f)) = 0
  rw [map_sub, cuspRestrict_zeroExtend, sub_self]

theorem modularLowCut_cuspZeroExtend (H : ℝ) (f : cuspHilbert H) :
    modularLowCut H (cuspZeroExtend H f) = 0 := by
  change cuspZeroExtend H f - cuspZeroExtend H (cuspRestrict H (cuspZeroExtend H f)) = 0
  rw [cuspRestrict_zeroExtend, sub_self]

theorem modularHighCut_idempotent (H : ℝ) (f : ModularHilbert) :
    modularHighCut H (modularHighCut H f) = modularHighCut H f := by
  change cuspZeroExtend H (cuspRestrict H (cuspZeroExtend H (cuspRestrict H f))) = _
  rw [cuspRestrict_zeroExtend]
  rfl

theorem modularHighCut_lowCut (H : ℝ) (f : ModularHilbert) :
    modularHighCut H (modularLowCut H f) = 0 := by
  rw [modularHighCut_apply, cuspRestrict_modularLowCut]
  exact map_zero (cuspZeroExtension H)

theorem modularLowCut_idempotent (H : ℝ) (f : ModularHilbert) :
    modularLowCut H (modularLowCut H f) = modularLowCut H f := by
  rw [modularLowCut_apply, modularHighCut_lowCut, sub_zero]

end GapFamily.Analytic
