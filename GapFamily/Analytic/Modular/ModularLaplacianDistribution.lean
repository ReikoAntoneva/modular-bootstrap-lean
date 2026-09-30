import GapFamily.Analytic.Modular.ModularLaplacianTest

/-!
# The ordinary weak PDE of the actual modular Laplacian

For every actual operator-domain vector, its coordinate representative solves
`-Δu = (Au)/y²` in distributions on the open fundamental region. Both sides
are ordinary locally integrable functions and all test integrals converge.
-/

noncomputable section

namespace GapFamily.Analytic.ModularGradient

open Set MeasureTheory
open scoped ContDiff

theorem realTest_lebesgue_integrable (φ : ℂ → ℝ) (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (f : ModularCoordinateHilbert) :
    IntegrableOn (fun z => (φ z : ℂ) * (f z / (z.im : ℂ) ^ 2)) modularInterior := by
  apply (Dirichlet.localHyperbolic_integrable_im_sq_mul_iff
    measurableSet_modularInterior (fun _ hz => im_pos_of_mem_modularInterior hz) _).mp
  have h := L2.integrable_inner (𝕜 := ℂ) (coordinateRealL2 φ hφ.continuous hc) f
  apply h.congr
  filter_upwards [coordinateRealL2_ae φ hφ.continuous hc, ae_mem_modularInterior] with z hφz hz
  have hn : (z.im : ℂ) ≠ 0 := by
    exact_mod_cast (im_pos_of_mem_modularInterior hz).ne'
  simp only [hφz, RCLike.inner_apply, Complex.conj_ofReal]
  field_simp

theorem realTest_inner_lebesgue (φ : ℂ → ℝ) (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (f : ModularCoordinateHilbert) :
    inner ℂ (realTest φ hφ hc) (modularCoordinateEquiv f) =
      ∫ z in modularInterior, (φ z : ℂ) * (f z / (z.im : ℂ) ^ 2) := by
  rw [realTest, modularCoordinateEquiv.inner_map_map, L2.inner_def,
    ← Dirichlet.localHyperbolic_integral_im_sq_mul measurableSet_modularInterior
      (fun _ hz => im_pos_of_mem_modularInterior hz)]
  apply integral_congr_ae
  filter_upwards [coordinateRealL2_ae φ hφ.continuous hc, ae_mem_modularInterior] with z hφz hz
  have hn : (z.im : ℂ) ≠ 0 := by
    exact_mod_cast (im_pos_of_mem_modularInterior hz).ne'
  simp only [hφz, RCLike.inner_apply, Complex.conj_ofReal]
  field_simp

/-- The literal Euclidean source corresponding to the actual operator value. -/
def coordinateSource (u : laplacian.domain) (z : ℂ) : ℂ :=
  modularCoordinateEquiv.symm (laplacian u) z / (z.im : ℂ) ^ 2

theorem coordinateSource_locallyIntegrableOn (u : laplacian.domain) :
    LocallyIntegrableOn (coordinateSource u) modularInterior volume := by
  change LocallyIntegrableOn (fun z =>
    modularCoordinateEquiv.symm (laplacian u) z / (z.im : ℂ) ^ 2) modularInterior volume
  have hc : ContinuousOn (fun z : ℂ => ((z.im : ℂ) ^ 2)⁻¹) modularInterior := by
    apply ContinuousOn.inv₀
    · fun_prop
    · intro z hz
      exact pow_ne_zero _ (by exact_mod_cast (im_pos_of_mem_modularInterior hz).ne')
  simpa only [div_eq_mul_inv] using
    (modularCoordinate_locallyIntegrableOn (modularCoordinateEquiv.symm (laplacian u))).mul_continuousOn
      hc isOpen_modularInterior.isLocallyClosed

theorem coordinateSource_test_integrable (u : laplacian.domain)
    (φ : ℂ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    IntegrableOn (fun z => (φ z : ℂ) * coordinateSource u z) modularInterior :=
  realTest_lebesgue_integrable φ hφ hc _

/-- Every vector in the genuine operator domain solves the ordinary distributional PDE. -/
theorem laplacian_weak_identity (u : laplacian.domain)
    (φ : ℂ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ modularInterior) :
    (∫ z in modularInterior, (φ z : ℂ) * coordinateSource u z) =
      -(∫ z in modularInterior, (euclideanTestLaplacian φ z : ℂ) *
        coordinateValue ⟨u, laplacian_domain_le u.property⟩ z) := by
  have h := realTest_laplacian_pairing φ hφ hc hs u
  rw [← LinearIsometryEquiv.apply_symm_apply modularCoordinateEquiv (laplacian u),
    realTest_inner_lebesgue,
    ← LinearIsometryEquiv.apply_symm_apply modularCoordinateEquiv (u : ModularHilbert),
    realTestLaplacian_inner_lebesgue] at h
  exact h

/-- The constructed shifted inverse solves the actual coordinate equation
`-Δv + v/y² = f/y²`, with ordinary convergent compact test integrals. -/
theorem weakResolvent_weak_identity (f : ModularHilbert)
    (φ : ℂ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ modularInterior) :
    -(∫ z in modularInterior, (euclideanTestLaplacian φ z : ℂ) *
        modularCoordinateEquiv.symm (weakResolvent f) z) +
      (∫ z in modularInterior, (φ z : ℂ) *
        (modularCoordinateEquiv.symm (weakResolvent f) z / (z.im : ℂ) ^ 2)) =
      ∫ z in modularInterior, (φ z : ℂ) *
        (modularCoordinateEquiv.symm f z / (z.im : ℂ) ^ 2) := by
  have h := congrArg (inner ℂ (realTest φ hφ hc)) (laplacian_resolvent f)
  rw [inner_add_right, realTest_laplacian_pairing φ hφ hc hs] at h
  change inner ℂ (realTestLaplacian φ hφ hc) (weakResolvent f) +
    inner ℂ (realTest φ hφ hc) (weakResolvent f) = inner ℂ (realTest φ hφ hc) f at h
  rw [← LinearIsometryEquiv.apply_symm_apply modularCoordinateEquiv (weakResolvent f),
    realTestLaplacian_inner_lebesgue, realTest_inner_lebesgue,
    ← LinearIsometryEquiv.apply_symm_apply modularCoordinateEquiv f,
    realTest_inner_lebesgue] at h
  simpa only [LinearIsometryEquiv.apply_symm_apply] using h

end GapFamily.Analytic.ModularGradient
