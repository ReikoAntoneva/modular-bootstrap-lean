import GapFamily.Analytic.Cusp.Profile.CuspCollarEnergy

/-! # Ordinary Fubini transport on the actual cusp collar -/

noncomputable section
namespace GapFamily.Analytic

open Set MeasureTheory ModularGradient UpperHalfPlane

theorem cuspCollarRectangle_eq_preimage (ε : ℝ) :
    cuspCollarRectangle ε = Complex.measurableEquivRealProd ⁻¹'
      (Ioo (-1/2 : ℝ) (1/2) ×ˢ Ioo 1 (1 + ε)) := by
  ext z
  simp [cuspCollarRectangle, abs_lt, and_assoc, neg_div]

theorem cuspCollar_product_continuousOn
    {E : Type*} [TopologicalSpace E] {g : ℂ → E}
    (hg : ContinuousOn g upperHalfPlaneSet) (ε : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => g (Complex.mk p.1 p.2))
      (Icc (-1/2 : ℝ) (1/2) ×ˢ Icc 1 (1 + ε)) := by
  apply hg.comp (by
    have heq : (fun p : ℝ × ℝ => Complex.mk p.1 p.2) =
        (fun p => (p.1 : ℂ) + (p.2 : ℂ) * Complex.I) := by
      funext p
      exact Complex.ext (by simp) (by simp)
    rw [heq]
    fun_prop)
  intro p hp
  exact lt_of_lt_of_le zero_lt_one hp.2.1

theorem cuspCollar_product_integrable
    {E : Type*} [NormedAddCommGroup E] {g : ℂ → E}
    (hg : ContinuousOn g upperHalfPlaneSet) (ε : ℝ) :
    IntegrableOn (fun p : ℝ × ℝ => g (Complex.mk p.1 p.2))
      (Icc (-1/2 : ℝ) (1/2) ×ˢ Icc 1 (1 + ε)) (volume.prod volume) :=
  (cuspCollar_product_continuousOn hg ε).integrableOn_compact
    (isCompact_Icc.prod isCompact_Icc)

theorem cuspCollar_integral_eq_iterated
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (g : ℂ → E) (hg : ContinuousOn g upperHalfPlaneSet) {ε : ℝ} (hε : 0 ≤ ε) :
    (∫ z : ℂ in cuspCollarRectangle ε, g z) =
      ∫ x in (-1/2 : ℝ)..(1/2), ∫ y in (1 : ℝ)..(1 + ε), g (Complex.mk x y) := by
  rw [cuspCollarRectangle_eq_preimage]
  trans (∫ p : ℝ × ℝ in Ioo (-1/2 : ℝ) (1/2) ×ˢ Ioo 1 (1 + ε),
    g (Complex.mk p.1 p.2) ∂volume.prod volume)
  · exact Complex.volume_preserving_equiv_real_prod.setIntegral_preimage_emb
      Complex.measurableEquivRealProd.measurableEmbedding
      (fun p : ℝ × ℝ => g (Complex.mk p.1 p.2)) _
  · rw [setIntegral_prod _ ((cuspCollar_product_integrable hg ε).mono_set
      (Set.prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self))]
    simp_rw [restrict_Ioo_eq_restrict_Ioc]
    rw [intervalIntegral.integral_of_le (by norm_num : (-1/2 : ℝ) ≤ 1/2)]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun x =>
      (intervalIntegral.integral_of_le (by linarith : (1 : ℝ) ≤ 1 + ε)).symm)

theorem cuspCollar_integral_swap
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (g : ℂ → E) (hg : ContinuousOn g upperHalfPlaneSet) {ε : ℝ} (hε : 0 ≤ ε) :
    (∫ x in (-1/2 : ℝ)..(1/2), ∫ y in (1 : ℝ)..(1 + ε), g (Complex.mk x y)) =
      ∫ y in (1 : ℝ)..(1 + ε), ∫ x in (-1/2 : ℝ)..(1/2), g (Complex.mk x y) := by
  apply intervalIntegral_intervalIntegral_swap
  rw [uIoc_of_le (by norm_num : (-1/2 : ℝ) ≤ 1/2),
    uIoc_of_le (by linarith : (1 : ℝ) ≤ 1 + ε)]
  exact (cuspCollar_product_integrable hg ε).mono_set
    (Set.prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)

theorem cuspCollar_iterated_value_energy_le (F : smoothCore) {ε : ℝ}
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    (∫ x in (-1/2 : ℝ)..(1/2), ∫ y in (1 : ℝ)..(1 + ε),
      ‖F.val (Complex.mk x y)‖ ^ 2) ≤ 4 * ‖value F‖ ^ 2 := by
  have he := cuspCollar_integral_eq_iterated (fun z => ‖F.val z‖ ^ 2)
    (F.property.1.continuousOn.norm.pow 2) hε0
  rw [← he]
  exact cuspCollar_value_energy_le F hε1

theorem cuspCollar_iterated_vertical_energy_le (F : smoothCore) {ε : ℝ}
    (hε : 0 ≤ ε) :
    (∫ x in (-1/2 : ℝ)..(1/2), ∫ y in (1 : ℝ)..(1 + ε),
      ‖fderiv ℝ F.val (Complex.mk x y) Complex.I‖ ^ 2) ≤ ‖coreGradient F‖ ^ 2 := by
  have hc : ContinuousOn (fun z => ‖fderiv ℝ F.val z Complex.I‖ ^ 2)
      upperHalfPlaneSet :=
    ((F.property.1.continuousOn_fderiv_of_isOpen isOpen_upperHalfPlaneSet (by simp)).clm_apply
      continuousOn_const).norm.pow 2
  rw [← cuspCollar_integral_eq_iterated _ hc hε]
  exact cuspCollar_vertical_energy_le F ε

end GapFamily.Analytic
