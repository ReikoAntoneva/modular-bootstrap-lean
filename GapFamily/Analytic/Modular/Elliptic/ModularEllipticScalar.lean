import GapFamily.Analytic.Modular.Elliptic.ModularEllipticWeakPoisson

/-!
# Real projections of the actual modular weak identities

Any real continuous linear functional may be used, including real and imaginary
part. Moving the functional through each complex integral uses the separately
proved ordinary integrability of the actual modular test pairing.
-/

noncomputable section
namespace GapFamily.Analytic.ModularGradient
open Set MeasureTheory
open scoped ContDiff

lemma ellipticScalar_real_mul (L : ℂ →L[ℝ] ℝ) (a : ℝ) (b : ℂ) :
    L ((a : ℂ) * b) = L b * a := by
  change L (a • b) = L b * a
  simpa only [smul_eq_mul, mul_comm] using L.map_smul a b

theorem ellipticScalar_weak_x (L : ℂ →L[ℝ] ℝ) (u : closedGradient.domain)
    (φ : ℂ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ modularInterior) :
    (∫ z in modularInterior, L (coordinateValue u z) * fderiv ℝ φ z 1) =
      -(∫ z in modularInterior, L (coordinateDx u z) * φ z) := by
  have h := congrArg L (coordinateDx_weak_identity u φ hφ hc hs)
  rw [map_neg, ← L.integral_comp_comm (coordinateDx_test_integrable u φ hφ hc),
    ← L.integral_comp_comm (coordinateValue_derivativeTest_integrable u φ hφ hc 1)] at h
  simp_rw [ellipticScalar_real_mul] at h
  linarith

theorem ellipticScalar_weak_y (L : ℂ →L[ℝ] ℝ) (u : closedGradient.domain)
    (φ : ℂ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ modularInterior) :
    (∫ z in modularInterior, L (coordinateValue u z) * fderiv ℝ φ z Complex.I) =
      -(∫ z in modularInterior, L (coordinateDy u z) * φ z) := by
  have h := congrArg L (coordinateDy_weak_identity u φ hφ hc hs)
  rw [map_neg, ← L.integral_comp_comm (coordinateDy_test_integrable u φ hφ hc),
    ← L.integral_comp_comm (coordinateValue_derivativeTest_integrable u φ hφ hc Complex.I)] at h
  simp_rw [ellipticScalar_real_mul] at h
  linarith

theorem ellipticScalar_poisson (L : ℂ →L[ℝ] ℝ) (u : laplacian.domain)
    (φ : ℂ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ modularInterior) :
    (∫ z in modularInterior,
      L (coordinateDx ⟨u, laplacian_domain_le u.property⟩ z) * fderiv ℝ φ z 1 +
      L (coordinateDy ⟨u, laplacian_domain_le u.property⟩ z) * fderiv ℝ φ z Complex.I) =
      ∫ z in modularInterior, L (coordinateSource u z) * φ z := by
  have h := congrArg L (laplacian_first_order_weak_identity u φ hφ hc hs)
  have hi := laplacian_first_order_test_integrable u φ hφ hc
  rw [← L.integral_comp_comm hi.1, ← L.integral_comp_comm hi.2] at h
  simpa only [map_add, ellipticScalar_real_mul] using h

end GapFamily.Analytic.ModularGradient
