import GapFamily.Analytic.Cusp.CuspProjectedCore
import GapFamily.Analytic.Cusp.Profile.CuspCollarIntegral

/-!
# Actual projected gradient energy on the upper unit collar

The actual projected L² components supply their own global integrability.
On the open collar their representatives are height times the ordinary
residual derivatives, so the inverse-square density cancels exactly.
-/

noncomputable section
namespace GapFamily.Analytic

open Set Filter MeasureTheory UpperHalfPlane ModularGradient
open scoped Topology ContDiff

private theorem cuspProjected_collar_energy_le_of_ae
    (u : ModularHilbert) (J H : ℂ → ℂ)
    (hrep : u =ᵐ[modularMeasure] (fun τ : UpperHalfPlane => J τ))
    (hJ : ∀ z ∈ cuspCollarRectangle 1, J z = (z.im : ℂ) * H z) :
    (∫ z : ℂ in cuspCollarRectangle 1, ‖H z‖ ^ 2) ≤ ‖u‖ ^ 2 := by
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
  let K := cuspCollarRectangle 1
  have hK : MeasurableSet K := (isOpen_cuspCollarRectangle 1).measurableSet
  rw [← integral_indicator hK]
  rw [integral_eq_coordinate_weighted _ (by
    intro z hz
    exact indicator_of_notMem (fun hk => hz (cuspCollarRectangle_subset_interior 1 hk)) _)]
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

private theorem cuspProjected_continuousOn_horizontal (F : smoothCore) :
    ContinuousOn (fun z : ℂ => fderiv ℝ F.val z 1) upperHalfPlaneSet :=
  (F.property.1.continuousOn_fderiv_of_isOpen
    isOpen_upperHalfPlaneSet (by simp)).clm_apply continuousOn_const

private theorem cuspProjected_continuousOn_vertical (F : smoothCore) :
    ContinuousOn (fun z : ℂ => fderiv ℝ F.val z Complex.I -
      deriv (cuspHorizontalAverage F.val) z.im) upperHalfPlaneSet := by
  have hd : ContinuousOn (fun z : ℂ => fderiv ℝ F.val z Complex.I)
      upperHalfPlaneSet :=
    (F.property.1.continuousOn_fderiv_of_isOpen
      isOpen_upperHalfPlaneSet (by simp)).clm_apply continuousOn_const
  exact hd.sub ((continuousOn_deriv_cuspHorizontalAverage F).comp
    Complex.continuous_im.continuousOn (fun _ hz => hz))

/-- The ordinary horizontal collar energy is a genuine product integral. -/
theorem cuspProjected_horizontal_collar_energy_integrable (F : smoothCore) :
    IntegrableOn (fun p : ℝ × ℝ => ‖fderiv ℝ F.val (Complex.mk p.1 p.2) 1‖ ^ 2)
      (Icc (-1/2 : ℝ) (1/2) ×ˢ Icc 1 2) (volume.prod volume) := by
  simpa only [Pi.pow_apply, show (1 : ℝ) + 1 = 2 by norm_num] using
    cuspCollar_product_integrable ((cuspProjected_continuousOn_horizontal F).norm.pow 2) 1

/-- The ordinary vertical residual energy is a genuine product integral. -/
theorem cuspProjected_vertical_collar_energy_integrable (F : smoothCore) :
    IntegrableOn (fun p : ℝ × ℝ => ‖fderiv ℝ F.val (Complex.mk p.1 p.2) Complex.I -
      deriv (cuspHorizontalAverage F.val) p.2‖ ^ 2)
      (Icc (-1/2 : ℝ) (1/2) ×ˢ Icc 1 2) (volume.prod volume) := by
  simpa only [Pi.pow_apply, show (1 : ℝ) + 1 = 2 by norm_num] using
    cuspCollar_product_integrable ((cuspProjected_continuousOn_vertical F).norm.pow 2) 1

/-- The horizontal collar energy is bounded by the actual projected component. -/
theorem cuspProjected_horizontal_collar_energy_le (F : smoothCore) :
    (∫ x in (-1/2 : ℝ)..(1/2), ∫ y in (1 : ℝ)..2,
      ‖fderiv ℝ F.val (Complex.mk x y) 1‖ ^ 2) ≤
      ‖(formGradient (cuspMeanZeroFormPart (coreForm F) : FormDomain)).ofLp.1‖ ^ 2 := by
  have he := cuspCollar_integral_eq_iterated
    (fun z : ℂ => ‖fderiv ℝ F.val z 1‖ ^ 2)
    ((cuspProjected_continuousOn_horizontal F).norm.pow 2) (ε := 1) zero_le_one
  simp only [show (1 : ℝ) + 1 = 2 by norm_num] at he
  rw [← he]
  exact cuspProjected_collar_energy_le_of_ae
    (formGradient (cuspMeanZeroFormPart (coreForm F) : FormDomain)).ofLp.1
    (fun z => (z.im : ℂ) * fderiv ℝ F.val z 1)
    (fun z => fderiv ℝ F.val z 1)
    (cuspMeanZeroFormPart_core_gradient_fst_ae F) (fun _ _ => rfl)

/-- The vertical residual collar energy is bounded by the actual projected
vertical component, with no comparison to the unprojected gradient. -/
theorem cuspProjected_vertical_collar_energy_le (F : smoothCore) :
    (∫ x in (-1/2 : ℝ)..(1/2), ∫ y in (1 : ℝ)..2,
      ‖fderiv ℝ F.val (Complex.mk x y) Complex.I -
        deriv (cuspHorizontalAverage F.val) y‖ ^ 2) ≤
      ‖(formGradient (cuspMeanZeroFormPart (coreForm F) : FormDomain)).ofLp.2‖ ^ 2 := by
  have he := cuspCollar_integral_eq_iterated
    (fun z : ℂ => ‖fderiv ℝ F.val z Complex.I -
      deriv (cuspHorizontalAverage F.val) z.im‖ ^ 2)
    ((cuspProjected_continuousOn_vertical F).norm.pow 2) (ε := 1) zero_le_one
  simp only [show (1 : ℝ) + 1 = 2 by norm_num] at he
  rw [← he]
  apply cuspProjected_collar_energy_le_of_ae
    (formGradient (cuspMeanZeroFormPart (coreForm F) : FormDomain)).ofLp.2
    (fun z => (z.im : ℂ) * (fderiv ℝ F.val z Complex.I -
      if 1 < z.im then deriv (cuspHorizontalAverage F.val) z.im else 0))
    (fun z => fderiv ℝ F.val z Complex.I - deriv (cuspHorizontalAverage F.val) z.im)
    (cuspMeanZeroFormPart_core_gradient_snd_ae F)
  intro z hz
  simp only [hz.2.1, ite_true]

end GapFamily.Analytic
