import GapFamily.Analytic.Cusp.Fourier.CuspHorizontalMeasure

/-!
# Complex integration in the actual modular cusp

The coordinate embedding and the inverse-square hyperbolic density transport
ordinary integrability to a product strip. Bochner Fubini then gives the actual
complex integral as iterated horizontal and vertical integrals.
-/

noncomputable section

namespace GapFamily.Analytic

open Set MeasureTheory UpperHalfPlane
open scoped ENNReal NNReal

private theorem horizontalCusp_eq_prod_preimage (H : ℝ) :
    horizontalCusp H = Complex.measurableEquivRealProd ⁻¹'
      (Ioo (-1/2 : ℝ) (1/2) ×ˢ Ioi H) := by
  ext z
  simp [horizontalCusp, abs_lt, and_assoc, neg_div]

private theorem cuspDensity_toReal (z : ℂ) :
    (ENNReal.ofReal (1 / z.im ^ 2)).toReal = 1 / z.im ^ 2 :=
  ENNReal.toReal_ofReal (by positivity)

/-- Ordinary complex integrability on the high cusp gives integrability of the
literal inverse-square weighted integrand on the Euclidean product strip. -/
theorem integrableOn_modular_highCusp_weight (g : ℂ → ℂ)
    {H : ℝ} (hH : 1 ≤ H)
    (hgi : IntegrableOn (fun τ : UpperHalfPlane => g τ)
      {τ | H < τ.im} modularMeasure) :
    IntegrableOn (fun p : ℝ × ℝ => (1 / p.2 ^ 2 : ℝ) • g (Complex.mk p.1 p.2))
      (Ioo (-1/2 : ℝ) (1/2) ×ˢ Ioi H) (volume.prod volume) := by
  have hcoord : IntegrableOn g {z : ℂ | H < z.im} modularCoordinateMeasure := by
    exact (measurePreserving_modularCoordinate.integrableOn_comp_preimage
      UpperHalfPlane.measurableEmbedding_coe).mp hgi
  have hweighted : IntegrableOn (fun z : ℂ => (1 / z.im ^ 2 : ℝ) • g z)
      (horizontalCusp H) := by
    rw [IntegrableOn, Measure.restrict_congr_set (highCusp_ae_horizontalCusp H),
      restrict_modularCoordinateMeasure (isOpen_horizontalCusp H).measurableSet
        (horizontalCusp_subset_modularInterior hH), Dirichlet.localHyperbolicMeasure,
      integrable_withDensity_iff_integrable_smul'
        (by fun_prop : Measurable (fun z : ℂ => ENNReal.ofReal (1 / z.im ^ 2)))
        (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)] at hcoord
    simpa only [IntegrableOn, cuspDensity_toReal] using hcoord
  apply (Complex.volume_preserving_equiv_real_prod.integrableOn_comp_preimage
    Complex.measurableEquivRealProd.measurableEmbedding).mp
  change IntegrableOn (fun z : ℂ => (1 / z.im ^ 2 : ℝ) • g z)
    (Complex.measurableEquivRealProd ⁻¹' (Ioo (-1/2 : ℝ) (1/2) ×ˢ Ioi H)) _
  rwa [← horizontalCusp_eq_prod_preimage]

/-- Bochner Fubini for an integrable complex function on the actual modular high
cusp. The integrability premise is transported before product integration. -/
theorem integral_modular_highCusp_of_integrable (g : ℂ → ℂ)
    {H : ℝ} (hH : 1 ≤ H)
    (hgi : IntegrableOn (fun τ : UpperHalfPlane => g τ)
      {τ | H < τ.im} modularMeasure) :
    (∫ τ : UpperHalfPlane in {τ | H < τ.im}, g τ ∂modularMeasure) =
      ∫ y : ℝ in Ioi H, ∫ x : ℝ in Ioo (-1/2) (1/2),
        (1 / y ^ 2 : ℝ) • g (Complex.mk x y) := by
  have hcoord :
      (∫ τ : UpperHalfPlane in {τ | H < τ.im}, g τ ∂modularMeasure) =
        ∫ z : ℂ in {z | H < z.im}, g z ∂modularCoordinateMeasure :=
    measurePreserving_modularCoordinate.setIntegral_preimage_emb
      UpperHalfPlane.measurableEmbedding_coe g {z : ℂ | H < z.im}
  rw [hcoord, Measure.restrict_congr_set (highCusp_ae_horizontalCusp H),
    restrict_modularCoordinateMeasure (isOpen_horizontalCusp H).measurableSet
      (horizontalCusp_subset_modularInterior hH), Dirichlet.localHyperbolicMeasure,
    integral_withDensity_eq_integral_toReal_smul
      (by fun_prop : Measurable (fun z : ℂ => ENNReal.ofReal (1 / z.im ^ 2)))
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp_rw [cuspDensity_toReal]
  rw [horizontalCusp_eq_prod_preimage]
  trans (∫ p : ℝ × ℝ in Ioo (-1/2 : ℝ) (1/2) ×ˢ Ioi H,
    (1 / p.2 ^ 2 : ℝ) • g (Complex.mk p.1 p.2) ∂volume.prod volume)
  · exact Complex.volume_preserving_equiv_real_prod.setIntegral_preimage_emb
      Complex.measurableEquivRealProd.measurableEmbedding
      (fun p : ℝ × ℝ => (1 / p.2 ^ 2 : ℝ) • g (Complex.mk p.1 p.2)) _
  · have hi := integrableOn_modular_highCusp_weight g hH hgi
    rw [IntegrableOn, ← Measure.prod_restrict] at hi
    rw [← Measure.prod_restrict]
    exact integral_prod_symm _ hi

/-- Continuous-on-upper-half-plane specialization of the actual complex high-cusp
integration formula. No global extension regularity is required. -/
theorem integral_modular_highCusp (g : ℂ → ℂ)
    (_hg : ContinuousOn g upperHalfPlaneSet) {H : ℝ} (hH : 1 ≤ H)
    (hgi : IntegrableOn (fun τ : UpperHalfPlane => g τ)
      {τ | H < τ.im} modularMeasure) :
    (∫ τ : UpperHalfPlane in {τ | H < τ.im}, g τ ∂modularMeasure) =
      ∫ y : ℝ in Ioi H, ∫ x : ℝ in Ioo (-1/2) (1/2),
        (1 / y ^ 2 : ℝ) • g (Complex.mk x y) :=
  integral_modular_highCusp_of_integrable g hH hgi

end GapFamily.Analytic
