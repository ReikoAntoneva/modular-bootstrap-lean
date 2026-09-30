import GapFamily.Analytic.Cusp.CuspProjectedEnergy
import GapFamily.Analytic.Cusp.CuspLowIntegral

/-!
# Actual projected mass and energy below height one

The ordinary low-region mass is the low part of the actual modular L² norm.
The projected derivative representative supplies the corresponding vertical
energy bound, with all integration confined to the actual fundamental region.
-/

noncomputable section
namespace GapFamily.Analytic
open Set Filter MeasureTheory UpperHalfPlane ModularGradient
open scoped Topology ContDiff

private theorem cuspLow_coordinate_integral (g : ℂ → ℝ) :
    (∫ z : ℂ in cuspLowRegion, g z ∂modularCoordinateMeasure) =
      ∫ z : ℂ in cuspLowRegion, g z / z.im ^ 2 := by
  have hweight := integral_eq_coordinate_weighted
    (cuspLowRegion.indicator (fun z => g z / z.im ^ 2)) (by
      intro z hz
      exact indicator_of_notMem (fun hk => hz (cuspLowRegion_subset_interior hk)) _)
  rw [integral_indicator measurableSet_cuspLowRegion] at hweight
  rw [hweight, ← integral_indicator measurableSet_cuspLowRegion]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro z
  dsimp only
  by_cases hz : z ∈ cuspLowRegion
  · rw [indicator_of_mem hz, indicator_of_mem hz]
    have hy : z.im ≠ 0 := (im_pos_of_mem_modularInterior hz.1).ne'
    field_simp
  · rw [indicator_of_notMem hz, indicator_of_notMem hz, mul_zero]

/-- The ordinary low weighted mass is genuinely integrable. -/
theorem cuspProjected_low_mass_integrable (F : smoothCore) :
    IntegrableOn (fun z : ℂ =>
      ‖F.val z - cuspHorizontalAverage F.val 1‖ ^ 2 / z.im ^ 2) cuspLowRegion := by
  apply cuspLow_integrable
  exact ((F.property.1.continuousOn.sub continuousOn_const).norm.pow 2).div
    (Complex.continuous_im.pow 2).continuousOn
    (fun z hz => pow_ne_zero 2 (ne_of_gt hz))

private theorem cuspProjected_low_mass_eq (F : smoothCore) :
    (∫ τ : UpperHalfPlane in {τ | τ.im ≤ 1},
      ‖meanZeroCuspEmbedding (cuspMeanZeroFormPart (coreForm F)) τ‖ ^ 2 ∂modularMeasure) =
      ∫ z : ℂ in cuspLowRegion,
        ‖F.val z - cuspHorizontalAverage F.val 1‖ ^ 2 / z.im ^ 2 := by
  let g : ℂ → ℝ := fun z => ‖F.val z - cuspHorizontalAverage F.val 1‖ ^ 2
  have hS : MeasurableSet {τ : UpperHalfPlane | τ.im ≤ 1} :=
    measurableSet_le UpperHalfPlane.continuous_im.measurable measurable_const
  calc
    _ = ∫ τ : UpperHalfPlane, cuspLowRegion.indicator g (τ : ℂ) ∂modularMeasure := by
      rw [← integral_indicator hS]
      apply integral_congr_ae
      filter_upwards [cuspMeanZeroFormPart_core_value_ae F, ae_mem_fdo] with τ hrep hτ
      have hint : (τ : ℂ) ∈ modularInterior := ⟨τ, hτ, rfl⟩
      by_cases hy : τ.im ≤ 1
      · rw [indicator_of_mem (show τ ∈ {τ : UpperHalfPlane | τ.im ≤ 1} from hy),
          hrep, ite_eq_right (not_lt_of_ge hy),
          indicator_of_mem (show (τ : ℂ) ∈ cuspLowRegion from ⟨hint, hy⟩)]
      · rw [indicator_of_notMem (show τ ∉ {τ : UpperHalfPlane | τ.im ≤ 1} from hy),
          indicator_of_notMem (show (τ : ℂ) ∉ cuspLowRegion from fun h => hy h.2)]
    _ = ∫ z : ℂ in cuspLowRegion, g z ∂modularCoordinateMeasure := by
      rw [← integral_modularCoordinate, integral_indicator measurableSet_cuspLowRegion]
    _ = _ := cuspLow_coordinate_integral g

/-- Exact decomposition of the actual projected mass into the curved low
region and the genuine high-cusp restriction. -/
theorem cuspProjected_mass_decomposition (F : smoothCore) :
    ‖meanZeroCuspEmbedding (cuspMeanZeroFormPart (coreForm F))‖ ^ 2 =
      (∫ z : ℂ in cuspLowRegion,
        ‖F.val z - cuspHorizontalAverage F.val 1‖ ^ 2 / z.im ^ 2) +
      ‖cuspRestrict 1 (meanZeroCuspEmbedding (cuspMeanZeroFormPart (coreForm F)))‖ ^ 2 := by
  let u := meanZeroCuspEmbedding (cuspMeanZeroFormPart (coreForm F))
  have hi : Integrable (fun τ : UpperHalfPlane => ‖u τ‖ ^ 2) modularMeasure :=
    (memLp_two_iff_integrable_sq_norm (Lp.memLp u).aestronglyMeasurable).mp (Lp.memLp u)
  have hsplit := integral_add_compl (measurableSet_highCusp 1) hi
  have hcompl : {τ : UpperHalfPlane | 1 < τ.im}ᶜ = {τ | τ.im ≤ 1} := by
    ext τ
    simp
  rw [hcompl] at hsplit
  have hhigh : ‖cuspRestrict 1 u‖ ^ 2 =
      ∫ τ : UpperHalfPlane in {τ | 1 < τ.im}, ‖u τ‖ ^ 2 ∂modularMeasure := by
    rw [cuspMean_l2_norm_sq]
    exact integral_congr_ae ((cuspRestrict_ae 1 u).mono fun τ hτ =>
      congrArg (fun z : ℂ => ‖z‖ ^ 2) hτ)
  change ‖u‖ ^ 2 = _ + ‖cuspRestrict 1 u‖ ^ 2
  rw [cuspMean_l2_norm_sq, hhigh, ← cuspProjected_low_mass_eq F]
  exact hsplit.symm.trans (add_comm _ _)

private theorem cuspProjected_region_energy_le_of_ae
    (K : Set ℂ) (hK : MeasurableSet K) (hKU : K ⊆ modularInterior)
    (u : ModularHilbert) (J H : ℂ → ℂ)
    (hrep : u =ᵐ[modularMeasure] (fun τ : UpperHalfPlane => J τ))
    (hJ : ∀ z ∈ K, J z = (z.im : ℂ) * H z) :
    (∫ z : ℂ in K, ‖H z‖ ^ 2) ≤ ‖u‖ ^ 2 := by
  have hm : MemLp (fun τ : UpperHalfPlane => J τ) 2 modularMeasure :=
    (memLp_congr_ae hrep).mp (Lp.memLp u)
  have hi : Integrable (fun z : ℂ => ‖J z‖ ^ 2) modularCoordinateMeasure :=
    (integrable_modularCoordinate_iff _).2
      ((memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).1 hm)
  have he : (∫ z : ℂ, ‖J z‖ ^ 2 ∂modularCoordinateMeasure) = ‖u‖ ^ 2 := by
    rw [integral_modularCoordinate, cuspMean_l2_norm_sq u]
    apply integral_congr_ae
    filter_upwards [hrep] with τ hτ
    rw [hτ]
  rw [← integral_indicator hK]
  rw [integral_eq_coordinate_weighted _ (by
    intro z hz
    exact indicator_of_notMem (fun hk => hz (hKU hk)) _)]
  calc
    _ ≤ ∫ z : ℂ, ‖J z‖ ^ 2 ∂modularCoordinateMeasure := by
      apply integral_mono_of_nonneg
        (Eventually.of_forall fun z => mul_nonneg (sq_nonneg _)
          (Set.indicator_nonneg (fun _ _ => sq_nonneg _) z)) hi
      apply Eventually.of_forall
      intro z
      dsimp only
      by_cases hz : z ∈ K
      · rw [indicator_of_mem hz, hJ z hz]
        simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
        exact le_rfl
      · rw [indicator_of_notMem hz, mul_zero]
        exact sq_nonneg _
    _ = _ := he

/-- Ordinary vertical energy on the actual curved low region is integrable. -/
theorem cuspProjected_low_vertical_energy_integrable (F : smoothCore) :
    IntegrableOn (fun z : ℂ => ‖fderiv ℝ F.val z Complex.I‖ ^ 2) cuspLowRegion := by
  apply cuspLow_integrable
  exact ((F.property.1.continuousOn_fderiv_of_isOpen
    isOpen_upperHalfPlaneSet (by simp)).clm_apply continuousOn_const).norm.pow 2

/-- The lower-region vertical derivative is controlled by the actual projected
vertical component, because the lifted average is clipped to heights above one. -/
theorem cuspProjected_low_vertical_component_energy_le (F : smoothCore) :
    (∫ z : ℂ in cuspLowRegion, ‖fderiv ℝ F.val z Complex.I‖ ^ 2) ≤
      ‖(formGradient (cuspMeanZeroFormPart (coreForm F) : FormDomain)).ofLp.2‖ ^ 2 := by
  apply cuspProjected_region_energy_le_of_ae cuspLowRegion measurableSet_cuspLowRegion
    cuspLowRegion_subset_interior
    (formGradient (cuspMeanZeroFormPart (coreForm F) : FormDomain)).ofLp.2
    (fun z => (z.im : ℂ) * (fderiv ℝ F.val z Complex.I -
      if 1 < z.im then deriv (cuspHorizontalAverage F.val) z.im else 0))
    (fun z => fderiv ℝ F.val z Complex.I)
    (cuspMeanZeroFormPart_core_gradient_snd_ae F)
  intro z hz
  have hlow : ¬ 1 < z.im := not_lt.mpr hz.2
  simp only [hlow, ite_false, sub_zero]

/-- No energy outside the fundamental domain is introduced into the low-region
estimate; the bound is by the true projected form gradient. -/
theorem cuspProjected_low_vertical_energy_le (F : smoothCore) :
    (∫ z : ℂ in cuspLowRegion, ‖fderiv ℝ F.val z Complex.I‖ ^ 2) ≤
      ‖formGradient (cuspMeanZeroFormPart (coreForm F) : FormDomain)‖ ^ 2 := by
  have hlow := cuspProjected_low_vertical_component_energy_le F
  have hn := WithLp.prod_norm_sq_eq_of_L2
    (formGradient (cuspMeanZeroFormPart (coreForm F) : FormDomain))
  change ‖formGradient (cuspMeanZeroFormPart (coreForm F) : FormDomain)‖ ^ 2 =
    ‖(formGradient (cuspMeanZeroFormPart (coreForm F) : FormDomain)).ofLp.1‖ ^ 2 +
    ‖(formGradient (cuspMeanZeroFormPart (coreForm F) : FormDomain)).ofLp.2‖ ^ 2 at hn
  nlinarith [sq_nonneg
    ‖(formGradient (cuspMeanZeroFormPart (coreForm F) : FormDomain)).ofLp.1‖]

end GapFamily.Analytic
