import GapFamily.Analytic.Modular.Geometry.ModularCoordinateLocal
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Horizontal integration in the actual modular cusp
Above height one the fundamental domain is a vertical strip, up to its null boundary. The theorem below identifies actual modular integrals with ordinary horizontal and vertical Lebesgue integrals and the literal inverse-square density.
-/
noncomputable section
namespace GapFamily.Analytic
open Set MeasureTheory UpperHalfPlane
open scoped ENNReal NNReal

def horizontalCusp (H : ℝ) : Set ℂ := {z | |z.re| < 1 / 2 ∧ H < z.im}

theorem isOpen_horizontalCusp (H : ℝ) : IsOpen (horizontalCusp H) :=
  (isOpen_lt (continuous_abs.comp Complex.continuous_re) continuous_const).inter
    (isOpen_lt continuous_const Complex.continuous_im)

theorem horizontalCusp_subset_modularInterior {H : ℝ} (hH : 1 ≤ H) :
    horizontalCusp H ⊆ modularInterior := by
  intro z hz
  rw [modularInterior, ModularGroup.coe_fdo]
  have hi : 1 < z.im := hH.trans_lt hz.2
  refine ⟨by linarith, ?_, hz.1⟩
  exact hi.trans_le ((le_abs_self z.im).trans (Complex.abs_im_le_norm z))

theorem highCusp_ae_horizontalCusp (H : ℝ) :
    {z : ℂ | H < z.im} =ᵐ[modularCoordinateMeasure] horizontalCusp H := by
  filter_upwards [ae_mem_modularInterior] with z hz
  have hre : |z.re| < 1 / 2 := by
    rw [modularInterior, ModularGroup.coe_fdo] at hz
    exact hz.2.2
  simp only [horizontalCusp, Set.mem_ofPred_eq, hre, true_and]

/-- Actual high-cusp hyperbolic integration, with no global smoothness requirement. -/
theorem lintegral_modular_highCusp (g : ℂ → ℝ)
    (hg : ContinuousOn g upperHalfPlaneSet) {H : ℝ} (hH : 1 ≤ H) :
    (∫⁻ τ : UpperHalfPlane in {τ | H < τ.im}, ENNReal.ofReal (g τ) ∂modularMeasure) =
      ∫⁻ y : ℝ in Ioi H, ∫⁻ x : ℝ in Ioo (-1/2) (1/2),
        ENNReal.ofReal ((1 / y ^ 2) * g (Complex.mk x y)) := by
  have hS := (isOpen_horizontalCusp H).measurableSet
  have hsub := horizontalCusp_subset_modularInterior hH
  have hcoord :
      (∫⁻ τ : UpperHalfPlane in {τ | H < τ.im}, ENNReal.ofReal (g τ) ∂modularMeasure) =
        ∫⁻ z : ℂ in {z | H < z.im}, ENNReal.ofReal (g z) ∂modularCoordinateMeasure :=
    by simpa using (measurePreserving_modularCoordinate.setLIntegral_comp_preimage_emb
      UpperHalfPlane.measurableEmbedding_coe (fun z => ENNReal.ofReal (g z)) ({z : ℂ | H < z.im}))
  rw [hcoord, Measure.restrict_congr_set (highCusp_ae_horizontalCusp H),
    restrict_modularCoordinateMeasure hS hsub, Dirichlet.localHyperbolicMeasure]
  rw [lintegral_withDensity_eq_lintegral_mul_non_measurable _
    (by fun_prop : Measurable (fun z : ℂ => ENNReal.ofReal (1 / z.im ^ 2)))
    (Filter.Eventually.of_forall (fun z => ENNReal.ofReal_lt_top))]
  have hweight :
      (∫⁻ z : ℂ in horizontalCusp H,
        ENNReal.ofReal (1 / z.im ^ 2) * ENNReal.ofReal (g z)) =
        ∫⁻ z : ℂ in horizontalCusp H,
          ENNReal.ofReal ((1 / z.im ^ 2) * g z) := by
    apply lintegral_congr
    intro z
    rw [ENNReal.ofReal_mul (by positivity : 0 ≤ 1 / z.im ^ 2)]
  rw [show (fun z => ENNReal.ofReal (1 / z.im ^ 2)) *
      (fun z => ENNReal.ofReal (g z)) =
      (fun z => ENNReal.ofReal (1 / z.im ^ 2) * ENNReal.ofReal (g z)) from rfl,
    hweight]
  have hset : horizontalCusp H = Complex.measurableEquivRealProd ⁻¹'
      (Ioo (-1/2 : ℝ) (1/2) ×ˢ Ioi H) := by
    ext z
    simp [horizontalCusp, abs_lt, and_assoc, neg_div]
  rw [hset]
  trans (∫⁻ p : ℝ × ℝ in Ioo (-1/2 : ℝ) (1/2) ×ˢ Ioi H,
    ENNReal.ofReal ((1 / p.2 ^ 2) * g (Complex.mk p.1 p.2)) ∂volume.prod volume)
  · exact Complex.volume_preserving_equiv_real_prod.setLIntegral_comp_preimage_emb
      Complex.measurableEquivRealProd.measurableEmbedding
      (fun p : ℝ × ℝ => ENNReal.ofReal ((1 / p.2 ^ 2) * g (Complex.mk p.1 p.2))) _
  · apply setLIntegral_prod_symm
    have hcG : ContinuousOn (fun p : ℝ × ℝ => g (Complex.mk p.1 p.2))
        (Ioo (-1/2 : ℝ) (1/2) ×ˢ Ioi H) := by
      have hmk : Continuous (fun p : ℝ × ℝ => Complex.mk p.1 p.2) := by
        have hh : Continuous (fun p : ℝ × ℝ => (p.1 : ℂ) + (p.2 : ℂ) * Complex.I) := by fun_prop
        convert hh using 1
        funext p
        exact Complex.ext (by simp) (by simp)
      apply hg.comp hmk.continuousOn
      intro p hp
      exact lt_trans zero_lt_one (hH.trans_lt hp.2)
    have hcW : ContinuousOn (fun p : ℝ × ℝ => (1 / p.2 ^ 2) * g (Complex.mk p.1 p.2))
        (Ioo (-1/2 : ℝ) (1/2) ×ˢ Ioi H) :=
      (continuousOn_const.div (continuous_snd.pow 2).continuousOn
        (fun p hp => pow_ne_zero 2 (ne_of_gt (lt_trans zero_lt_one (hH.trans_lt hp.2))))).mul hcG
    exact (ENNReal.continuous_ofReal.comp_continuousOn hcW).aemeasurable
      (measurableSet_Ioo.prod measurableSet_Ioi)

end GapFamily.Analytic
