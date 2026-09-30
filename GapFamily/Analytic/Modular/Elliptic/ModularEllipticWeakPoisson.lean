import GapFamily.Analytic.Modular.Elliptic.ModularEllipticLocalL2

/-!
# The first-order weak Poisson identity for the actual modular operator

Testing the actual weak coordinate derivatives against first derivatives of a
smooth test converts the proved second-order distributional equation to the
ordinary gradient-pairing form used by interior elliptic estimates.
-/

noncomputable section

namespace GapFamily.Analytic.ModularGradient

open Set MeasureTheory
open scoped ContDiff

/-- The actual operator-domain vector satisfies the ordinary first-order weak Poisson equation. -/
theorem laplacian_first_order_weak_identity (u : laplacian.domain)
    (φ : ℂ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ modularInterior) :
    (∫ z in modularInterior,
      (fderiv ℝ φ z 1 : ℂ) * coordinateDx ⟨u, laplacian_domain_le u.property⟩ z +
      (fderiv ℝ φ z Complex.I : ℂ) * coordinateDy ⟨u, laplacian_domain_le u.property⟩ z) =
      ∫ z in modularInterior, (φ z : ℂ) * coordinateSource u z := by
  let v : closedGradient.domain := ⟨u, laplacian_domain_le u.property⟩
  have hx := coordinateDx_weak_identity v (fun z => fderiv ℝ φ z 1)
    (contDiff_testDerivative φ hφ 1) (hc.fderiv_apply ℝ 1)
    ((tsupport_fderiv_apply_subset ℝ 1).trans hs)
  have hy := coordinateDy_weak_identity v (fun z => fderiv ℝ φ z Complex.I)
    (contDiff_testDerivative φ hφ Complex.I) (hc.fderiv_apply ℝ Complex.I)
    ((tsupport_fderiv_apply_subset ℝ Complex.I).trans hs)
  have hxi := coordinateDx_test_integrable v (fun z => fderiv ℝ φ z 1)
    (contDiff_testDerivative φ hφ 1) (hc.fderiv_apply ℝ 1)
  have hyi := coordinateDy_test_integrable v (fun z => fderiv ℝ φ z Complex.I)
    (contDiff_testDerivative φ hφ Complex.I) (hc.fderiv_apply ℝ Complex.I)
  have hxx := coordinateValue_derivativeTest_integrable v (fun z => fderiv ℝ φ z 1)
    (contDiff_testDerivative φ hφ 1) (hc.fderiv_apply ℝ 1) 1
  have hyy := coordinateValue_derivativeTest_integrable v (fun z => fderiv ℝ φ z Complex.I)
    (contDiff_testDerivative φ hφ Complex.I) (hc.fderiv_apply ℝ Complex.I) Complex.I
  change (∫ z in modularInterior,
      (fderiv ℝ φ z 1 : ℂ) * coordinateDx v z +
      (fderiv ℝ φ z Complex.I : ℂ) * coordinateDy v z) = _
  rw [integral_add hxi hyi, hx, hy, ← neg_add, ← integral_add hxx hyy,
    laplacian_weak_identity u φ hφ hc hs]
  congr 1
  apply integral_congr_ae
  filter_upwards with z
  simp only [euclideanTestLaplacian, Complex.ofReal_add, add_mul, v]

/-- The first-order gradient pairing and the actual divided-source pairing are
ordinary integrable functions, independently of the equation between them. -/
theorem laplacian_first_order_test_integrable (u : laplacian.domain)
    (φ : ℂ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    IntegrableOn (fun z =>
      (fderiv ℝ φ z 1 : ℂ) * coordinateDx ⟨u, laplacian_domain_le u.property⟩ z +
      (fderiv ℝ φ z Complex.I : ℂ) * coordinateDy ⟨u, laplacian_domain_le u.property⟩ z)
      modularInterior ∧
    IntegrableOn (fun z => (φ z : ℂ) * coordinateSource u z) modularInterior := by
  refine ⟨?_, coordinateSource_test_integrable u φ hφ hc⟩
  exact (coordinateDx_test_integrable ⟨u, laplacian_domain_le u.property⟩
    (fun z => fderiv ℝ φ z 1) (contDiff_testDerivative φ hφ 1)
    (hc.fderiv_apply ℝ 1)).add
      (coordinateDy_test_integrable ⟨u, laplacian_domain_le u.property⟩
        (fun z => fderiv ℝ φ z Complex.I) (contDiff_testDerivative φ hφ Complex.I)
        (hc.fderiv_apply ℝ Complex.I))

end GapFamily.Analytic.ModularGradient
