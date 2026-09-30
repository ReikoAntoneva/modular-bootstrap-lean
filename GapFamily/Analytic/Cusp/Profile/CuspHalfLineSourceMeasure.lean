import GapFamily.Analytic.Cusp.CuspCoordinate
import GapFamily.Analytic.Cusp.Fourier.CuspHorizontalMeasure
import GapFamily.Analytic.Cusp.Fourier.CuspHorizontalHilbertBasic

noncomputable section

namespace GapFamily.Analytic.CuspHalfLineSource

open Set MeasureTheory UpperHalfPlane
open scoped ENNReal NNReal

def rawLift (g : ℝ → ℂ) (τ : UpperHalfPlane) : ℂ :=
  if 1 < τ.im then cuspLift g τ.im else 0

theorem measurable_rawLift {g : ℝ → ℂ} (hg : Measurable g) : Measurable (rawLift g) := by
  unfold rawLift
  exact ((measurable_cuspLift hg).comp UpperHalfPlane.continuous_im.measurable).ite
    (measurableSet_highCusp 1) measurable_const

theorem lintegral_modular_highCusp_measurable (g : ℂ → ℝ)
    (hg : Measurable g) {H : ℝ} (hH : 1 ≤ H) :
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
    have hmk : Measurable (fun p : ℝ × ℝ => Complex.mk p.1 p.2) :=
      Complex.measurableEquivRealProd.symm.measurable
    exact ((measurable_const.div (measurable_snd.pow_const 2)).mul (hg.comp hmk)).ennreal_ofReal.aemeasurable

theorem lintegral_clippedProfile_norm_sq (b : ℝ → ℂ) (hb : Measurable b) :
    (∫⁻ τ : UpperHalfPlane, ENNReal.ofReal (‖if 1 < τ.im then b τ.im else 0‖ ^ 2)
      ∂modularMeasure) = ∫⁻ y : ℝ in Ioi 1, ENNReal.ofReal (‖b y‖ ^ 2 / y ^ 2) := by
  have heq : (fun τ : UpperHalfPlane => ENNReal.ofReal (‖if 1 < τ.im then b τ.im else 0‖ ^ 2)) =
      {τ : UpperHalfPlane | 1 < τ.im}.indicator (fun τ => ENNReal.ofReal (‖b τ.im‖ ^ 2)) := by
    funext τ
    by_cases hτ : 1 < τ.im <;> simp [hτ]
  rw [heq, lintegral_indicator (measurableSet_highCusp 1)]
  have htransport := lintegral_modular_highCusp_measurable
    (fun z : ℂ => ‖b z.im‖ ^ 2) ((hb.comp Complex.measurable_im).norm.pow_const 2) le_rfl
  simp only [coe_im] at htransport
  rw [htransport]
  apply lintegral_congr
  intro y
  norm_num [lintegral_const, Real.volume_Ioo, div_eq_mul_inv, mul_comm]

theorem lintegral_rawLift_norm_sq (g : ℝ → ℂ) (hg : Measurable g) :
    (∫⁻ τ : UpperHalfPlane, ENNReal.ofReal (‖rawLift g τ‖ ^ 2) ∂modularMeasure) =
      ∫⁻ t : ℝ in Ioi 0, ENNReal.ofReal (‖g t‖ ^ 2) := by
  simp only [rawLift]
  rw [lintegral_clippedProfile_norm_sq _ (measurable_cuspLift hg)]
  have h := lintegral_cuspLift_norm_sq g (Y := 1) zero_lt_one
  rw [Real.log_one] at h
  simpa only [← Measure.restrict_congr_set (Ioi_ae_eq_Ici (a := (1 : ℝ)) (μ := volume)),
    ← Measure.restrict_congr_set (Ioi_ae_eq_Ici (a := (0 : ℝ)) (μ := volume))] using h

theorem memLp_rawLift_iff {g : ℝ → ℂ} (hg : Measurable g) :
    MemLp (rawLift g) 2 modularMeasure ↔ MemLp g 2 (volume.restrict (Ioi 0)) := by
  rw [memLp_two_iff_integrable_sq_norm (measurable_rawLift hg).aestronglyMeasurable,
    memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable]
  rw [← lintegral_ofReal_ne_top_iff_integrable
      ((measurable_rawLift hg).norm.pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun _ => sq_nonneg _),
    ← lintegral_ofReal_ne_top_iff_integrable (hg.norm.pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun _ => sq_nonneg _),
    lintegral_rawLift_norm_sq g hg]

theorem integrable_rawLift_norm_sq (g : ℝ → ℂ) (hg : Measurable g)
    (hm : MemLp g 2 (volume.restrict (Ioi 0))) :
    Integrable (fun τ => ‖rawLift g τ‖ ^ 2) modularMeasure :=
  (memLp_two_iff_integrable_sq_norm (measurable_rawLift hg).aestronglyMeasurable).mp
    ((memLp_rawLift_iff hg).mpr hm)

theorem integral_rawLift_norm_sq (g : ℝ → ℂ) (hg : Measurable g)
    (hm : MemLp g 2 (volume.restrict (Ioi 0))) :
    (∫ τ : UpperHalfPlane, ‖rawLift g τ‖ ^ 2 ∂modularMeasure) =
      ∫ t : ℝ in Ioi 0, ‖g t‖ ^ 2 := by
  have hleft := integrable_rawLift_norm_sq g hg hm
  have hright := (memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable).mp hm
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun _ => sq_nonneg _)
    hleft.aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun _ => sq_nonneg _)
      hright.aestronglyMeasurable,
    lintegral_rawLift_norm_sq g hg]

end GapFamily.Analytic.CuspHalfLineSource
