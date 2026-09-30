import GapFamily.Analytic.Cusp.Profile.CuspCollarIntegral
import GapFamily.Analytic.Cusp.CuspLowGeometry

/-!
# Ordinary Fubini integration on the curved low fundamental domain

The product indicator retains each actual variable lower fiber boundary.
-/

noncomputable section

namespace GapFamily.Analytic

open Set MeasureTheory ModularGradient UpperHalfPlane

private def lowFiberRegion (φ : ℝ → ℝ) : Set (ℝ × ℝ) :=
  {p | p.1 ∈ Ioo (-1/2 : ℝ) (1/2) ∧ p.2 ∈ Ioc (φ p.1) 1}

private theorem lowFiberRegion_slice_integral
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (φ : ℝ → ℝ) (f : ℝ × ℝ → E) (x : ℝ) :
    (∫ y : ℝ, (lowFiberRegion φ).indicator f (x,y)) =
      (Ioo (-1/2 : ℝ) (1/2)).indicator
        (fun x => ∫ y in Ioc (φ x) 1, f (x,y)) x := by
  by_cases hx : x ∈ Ioo (-1/2 : ℝ) (1/2)
  · rw [indicator_of_mem hx]
    calc
      _ = ∫ y : ℝ, (Ioc (φ x) 1).indicator (fun y => f (x,y)) y := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun y => by
          simp only [lowFiberRegion, indicator_apply, mem_ofPred_eq, hx, true_and])
      _ = _ := integral_indicator measurableSet_Ioc
  · simp only [lowFiberRegion, indicator_apply, mem_ofPred_eq, hx, false_and,
      ite_false, integral_zero]

private theorem lowFiberRegion_integral_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (φ : ℝ → ℝ) (f : ℝ × ℝ → E)
    (hS : MeasurableSet (lowFiberRegion φ))
    (hf : IntegrableOn f (lowFiberRegion φ) (volume.prod volume)) :
    (∫ p in lowFiberRegion φ, f p ∂volume.prod volume) =
      ∫ x in Ioo (-1/2 : ℝ) (1/2), ∫ y in Ioc (φ x) 1, f (x,y) := by
  rw [← integral_indicator hS, integral_prod _ (hf.integrable_indicator hS)]
  simp_rw [lowFiberRegion_slice_integral]
  exact integral_indicator measurableSet_Ioo

private theorem lowFiberRegion_outer_integrable
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (φ : ℝ → ℝ) (f : ℝ × ℝ → E)
    (hS : MeasurableSet (lowFiberRegion φ))
    (hf : IntegrableOn f (lowFiberRegion φ) (volume.prod volume)) :
    IntegrableOn (fun x => ∫ y in Ioc (φ x) 1, f (x,y))
      (Ioo (-1/2 : ℝ) (1/2)) := by
  have hi := (hf.integrable_indicator hS).integral_prod_left
  simp_rw [lowFiberRegion_slice_integral] at hi
  exact (integrable_indicator_iff measurableSet_Ioo).1 hi

/-- The exact real-product image of the curved low fundamental domain. -/
def cuspLowProductRegion : Set (ℝ × ℝ) :=
  {p | p.1 ∈ Ioo (-1/2 : ℝ) (1/2) ∧ p.2 ∈ Ioc (cuspLowFiber p.1) 1}

theorem measurableSet_cuspLowProductRegion : MeasurableSet cuspLowProductRegion :=
  measurableSet_region_between_oc continuous_cuspLowFiber.measurable measurable_const
    measurableSet_Ioo

theorem cuspLow_product_continuousOn
    {E : Type*} [TopologicalSpace E] {g : ℂ → E}
    (hg : ContinuousOn g upperHalfPlaneSet) :
    ContinuousOn (fun p : ℝ × ℝ => g (Complex.mk p.1 p.2))
      (Icc (-1/2 : ℝ) (1/2) ×ˢ Icc (3/4 : ℝ) 1) := by
  apply hg.comp (by
    have heq : (fun p : ℝ × ℝ => Complex.mk p.1 p.2) =
        (fun p => (p.1 : ℂ) + (p.2 : ℂ) * Complex.I) := by
      funext p
      exact Complex.ext (by simp) (by simp)
    rw [heq]
    fun_prop)
  intro p hp
  exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 3/4) hp.2.1

/-- Integrability is first obtained on a containing compact rectangle, then
restricted to the actual curved region before applying Fubini. -/
theorem cuspLow_product_integrable
    {E : Type*} [NormedAddCommGroup E] {g : ℂ → E}
    (hg : ContinuousOn g upperHalfPlaneSet) :
    IntegrableOn (fun p : ℝ × ℝ => g (Complex.mk p.1 p.2))
      cuspLowProductRegion (volume.prod volume) := by
  apply ((cuspLow_product_continuousOn hg).integrableOn_compact
    (isCompact_Icc.prod isCompact_Icc)).mono_set
  intro p hp
  exact ⟨⟨hp.1.1.le, hp.1.2.le⟩,
    ⟨(cuspLowFiber_lower ⟨hp.1.1.le, hp.1.2.le⟩).trans hp.2.1.le, hp.2.2⟩⟩

/-- The integral on the actual low complex region is genuinely convergent. -/
theorem cuspLow_integrable
    {E : Type*} [NormedAddCommGroup E] {g : ℂ → E}
    (hg : ContinuousOn g upperHalfPlaneSet) : IntegrableOn g cuspLowRegion := by
  have hi := Complex.volume_preserving_equiv_real_prod.integrable_comp_of_integrable
    ((cuspLow_product_integrable hg).integrable_indicator measurableSet_cuspLowProductRegion)
  have heq : (cuspLowProductRegion.indicator
      (fun p : ℝ × ℝ => g (Complex.mk p.1 p.2))) ∘ Complex.measurableEquivRealProd =
      cuspLowRegion.indicator g := by
    funext z
    rw [Function.comp_apply, ← indicator_comp_right]
    rw [show Complex.measurableEquivRealProd ⁻¹' cuspLowProductRegion = cuspLowRegion from
      cuspLowRegion_eq_preimage.symm]
    rfl
  rw [heq] at hi
  exact (integrable_indicator_iff measurableSet_cuspLowRegion).1 hi

/-- Every individual physical fiber integral converges, including horizontal
endpoints and the degenerate center fiber. -/
theorem cuspLow_fiber_intervalIntegrable
    {E : Type*} [NormedAddCommGroup E] {g : ℂ → E}
    (hg : ContinuousOn g upperHalfPlaneSet) {x : ℝ}
    (hx : x ∈ Icc (-1/2 : ℝ) (1/2)) :
    IntervalIntegrable (fun y => g (Complex.mk x y)) volume (cuspLowFiber x) 1 := by
  apply ContinuousOn.intervalIntegrable_of_Icc (cuspLowFiber_le_one x)
  apply hg.comp (by
    have heq : (Complex.mk x : ℝ → ℂ) =
        (fun y : ℝ => (x : ℂ) + (y : ℂ) * Complex.I) := by
      funext y
      exact Complex.ext (by simp) (by simp)
    rw [heq]
    fun_prop)
  intro y hy
  exact (cuspLowFiber_pos hx).trans_le hy.1

/-- The exact variable-fiber integral is integrable in the horizontal coordinate. -/
theorem cuspLow_iterated_intervalIntegrable
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {g : ℂ → E}
    (hg : ContinuousOn g upperHalfPlaneSet) :
    IntervalIntegrable (fun x => ∫ y in (cuspLowFiber x)..1, g (Complex.mk x y))
      volume (-1/2 : ℝ) (1/2) := by
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (-1/2 : ℝ) ≤ 1/2)]
  simp_rw [intervalIntegral.integral_of_le (cuspLowFiber_le_one _)]
  exact lowFiberRegion_outer_integrable cuspLowFiber _ measurableSet_cuspLowProductRegion
    (cuspLow_product_integrable hg)

/-- Fubini on the literal low fundamental-domain fibers; no derivative mass
outside the fundamental domain enters either side. -/
theorem cuspLow_integral_eq_iterated
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (g : ℂ → E) (hg : ContinuousOn g upperHalfPlaneSet) :
    (∫ z : ℂ in cuspLowRegion, g z) =
      ∫ x in (-1/2 : ℝ)..(1/2), ∫ y in (cuspLowFiber x)..1, g (Complex.mk x y) := by
  rw [cuspLowRegion_eq_preimage]
  trans (∫ p : ℝ × ℝ in cuspLowProductRegion,
    g (Complex.mk p.1 p.2) ∂volume.prod volume)
  · exact Complex.volume_preserving_equiv_real_prod.setIntegral_preimage_emb
      Complex.measurableEquivRealProd.measurableEmbedding
      (fun p : ℝ × ℝ => g (Complex.mk p.1 p.2)) _
  · rw [show cuspLowProductRegion = lowFiberRegion cuspLowFiber from rfl,
      lowFiberRegion_integral_eq cuspLowFiber _ measurableSet_cuspLowProductRegion
      (cuspLow_product_integrable hg)]
    simp_rw [intervalIntegral.integral_of_le (cuspLowFiber_le_one _)]
    rw [intervalIntegral.integral_of_le (by norm_num : (-1/2 : ℝ) ≤ 1/2),
      restrict_Ioo_eq_restrict_Ioc]

end GapFamily.Analytic
