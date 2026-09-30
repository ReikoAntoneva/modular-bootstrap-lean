import GapFamily.Analytic.Modular.ModularGradientWeak
import GapFamily.Analytic.Modular.Geometry.ModularCoordinateLocal

/-!
# Euclidean distributional derivatives of the closed modular gradient

The actual coordinate representative of a vector in the closed gradient domain
has weak Euclidean derivatives given by the two gradient components divided by
height. All test products below are integrable for ordinary Lebesgue measure.
-/

noncomputable section

namespace GapFamily.Analytic.ModularGradient

open Set MeasureTheory
open scoped ContDiff

private theorem coordinateReal_mul_integrable
    (ψ : ℂ → ℝ) (hψ : Continuous ψ) (hc : HasCompactSupport ψ)
    (f : ModularCoordinateHilbert) :
    Integrable (fun z => (ψ z : ℂ) * f z) modularCoordinateMeasure := by
  have h := L2.integrable_inner (𝕜 := ℂ) (coordinateRealL2 ψ hψ hc) f
  apply h.congr
  filter_upwards [coordinateRealL2_ae ψ hψ hc] with z hz
  simp [hz, RCLike.inner_apply, mul_comm]

/-- The frame test product is integrable after canceling hyperbolic area. -/
theorem frameTest_lebesgue_integrable
    (φ : ℂ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (f : ModularCoordinateHilbert) :
    IntegrableOn (fun z => (φ z : ℂ) * (f z / (z.im : ℂ))) modularInterior := by
  apply (Dirichlet.localHyperbolic_integrable_im_sq_mul_iff
    measurableSet_modularInterior (fun _ hz => im_pos_of_mem_modularInterior hz) _).mp
  have h := coordinateReal_mul_integrable (fun z => z.im * φ z)
    (Complex.continuous_im.mul hφ.continuous) hc.mul_left f
  apply h.congr
  filter_upwards [ae_mem_modularInterior] with z hz
  have hn : (z.im : ℂ) ≠ 0 := by
    exact_mod_cast (im_pos_of_mem_modularInterior hz).ne'
  push_cast
  field_simp

/-- The frame pairing becomes an ordinary Lebesgue test against the component
of the gradient divided by height. -/
theorem frameTest_inner_lebesgue
    (φ : ℂ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (f : ModularCoordinateHilbert) :
    inner ℂ (frameTest φ hφ hc) (modularCoordinateEquiv f) =
      ∫ z in modularInterior, (φ z : ℂ) * (f z / (z.im : ℂ)) := by
  rw [frameTest_inner_coordinate,
    ← Dirichlet.localHyperbolic_integral_im_sq_mul measurableSet_modularInterior
      (fun _ hz => im_pos_of_mem_modularInterior hz)]
  apply integral_congr_ae
  filter_upwards [ae_mem_modularInterior] with z hz
  have hn : (z.im : ℂ) ≠ 0 := by
    exact_mod_cast (im_pos_of_mem_modularInterior hz).ne'
  simp only [Complex.real_smul]
  field_simp

/-- The ordinary derivative-test product is integrable against any modular L² vector. -/
theorem divergenceTest_lebesgue_integrable
    (φ : ℂ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (v : ℂ) (f : ModularCoordinateHilbert) :
    IntegrableOn (fun z => (fderiv ℝ φ z v : ℂ) * f z) modularInterior := by
  apply (Dirichlet.localHyperbolic_integrable_im_sq_mul_iff
    measurableSet_modularInterior (fun _ hz => im_pos_of_mem_modularInterior hz) _).mp
  have hD : HasCompactSupport (fun z : ℂ => fderiv ℝ φ z v) := hc.fderiv_apply ℝ v
  have hmul : HasCompactSupport (fun z : ℂ => z.im ^ 2 * fderiv ℝ φ z v) :=
    hD.mul_left (f := fun z : ℂ => z.im ^ 2)
  have h := coordinateReal_mul_integrable (fun z => z.im ^ 2 * fderiv ℝ φ z v)
    ((Complex.continuous_im.pow 2).mul (continuous_testDerivative φ hφ v))
    hmul f
  simpa only [Complex.ofReal_mul, Complex.ofReal_pow, mul_assoc,
    modularCoordinateMeasure] using h

/-- The formal divergence pairing becomes minus the ordinary derivative-test integral. -/
theorem divergenceTest_inner_lebesgue
    (φ : ℂ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (v : ℂ) (f : ModularCoordinateHilbert) :
    inner ℂ (divergenceTest φ hφ hc v) (modularCoordinateEquiv f) =
      -(∫ z in modularInterior, (fderiv ℝ φ z v : ℂ) * f z) := by
  rw [divergenceTest, modularCoordinateEquiv.inner_map_map, L2.inner_def,
    ← Dirichlet.localHyperbolic_integral_im_sq_mul measurableSet_modularInterior
      (fun _ hz => im_pos_of_mem_modularInterior hz), ← integral_neg]
  apply integral_congr_ae
  filter_upwards [coordinateRealL2_ae (fun z => -(z.im ^ 2 * fderiv ℝ φ z v))
    (((Complex.continuous_im.pow 2).mul (continuous_testDerivative φ hφ v)).neg)
    (compactSupport_testDivergence φ hc v)] with z hz
  simp [hz, RCLike.inner_apply, mul_comm, mul_left_comm]

/-- The coordinate representative of an actual closed-gradient domain vector. -/
def coordinateValue (u : closedGradient.domain) : ModularCoordinateHilbert :=
  modularCoordinateEquiv.symm (u : ModularHilbert)

/-- The actual weak derivative in the horizontal Euclidean coordinate. -/
def coordinateDx (u : closedGradient.domain) (z : ℂ) : ℂ :=
  modularCoordinateEquiv.symm ((WithLp.ofLp (closedGradient u)).1) z / (z.im : ℂ)

/-- The actual weak derivative in the vertical Euclidean coordinate. -/
def coordinateDy (u : closedGradient.domain) (z : ℂ) : ℂ :=
  modularCoordinateEquiv.symm ((WithLp.ofLp (closedGradient u)).2) z / (z.im : ℂ)


/-- The domain vector is locally integrable for ordinary Lebesgue measure. -/
theorem coordinateValue_locallyIntegrableOn (u : closedGradient.domain) :
    LocallyIntegrableOn (fun z => coordinateValue u z) modularInterior volume :=
  modularCoordinate_locallyIntegrableOn _

/-- The horizontal weak derivative is locally Lebesgue integrable. -/
theorem coordinateDx_locallyIntegrableOn (u : closedGradient.domain) :
    LocallyIntegrableOn (coordinateDx u) modularInterior volume :=
  modularCoordinate_div_im_locallyIntegrableOn _

/-- The vertical weak derivative is locally Lebesgue integrable. -/
theorem coordinateDy_locallyIntegrableOn (u : closedGradient.domain) :
    LocallyIntegrableOn (coordinateDy u) modularInterior volume :=
  modularCoordinate_div_im_locallyIntegrableOn _

theorem coordinateDx_test_integrable
    (u : closedGradient.domain) (φ : ℂ → ℝ) (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) :
    IntegrableOn (fun z => (φ z : ℂ) * coordinateDx u z) modularInterior :=
  frameTest_lebesgue_integrable φ hφ hc _

theorem coordinateDy_test_integrable
    (u : closedGradient.domain) (φ : ℂ → ℝ) (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) :
    IntegrableOn (fun z => (φ z : ℂ) * coordinateDy u z) modularInterior :=
  frameTest_lebesgue_integrable φ hφ hc _

theorem coordinateValue_derivativeTest_integrable
    (u : closedGradient.domain) (φ : ℂ → ℝ) (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (v : ℂ) :
    IntegrableOn (fun z => (fderiv ℝ φ z v : ℂ) * coordinateValue u z)
      modularInterior :=
  divergenceTest_lebesgue_integrable φ hφ hc v _

/-- Ordinary Lebesgue weak derivative identity in the horizontal coordinate. -/
theorem coordinateDx_weak_identity
    (u : closedGradient.domain) (φ : ℂ → ℝ) (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ modularInterior) :
    (∫ z in modularInterior, (φ z : ℂ) * coordinateDx u z) =
      -(∫ z in modularInterior, (fderiv ℝ φ z 1 : ℂ) * coordinateValue u z) := by
  have h := frameTest_closedGradient_pairing_x φ hφ hc hs u
  rw [← LinearIsometryEquiv.apply_symm_apply modularCoordinateEquiv
    ((WithLp.ofLp (closedGradient u)).1), frameTest_inner_lebesgue,
    ← LinearIsometryEquiv.apply_symm_apply modularCoordinateEquiv (u : ModularHilbert),
    divergenceTest_inner_lebesgue] at h
  exact h

/-- Ordinary Lebesgue weak derivative identity in the vertical coordinate. -/
theorem coordinateDy_weak_identity
    (u : closedGradient.domain) (φ : ℂ → ℝ) (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ modularInterior) :
    (∫ z in modularInterior, (φ z : ℂ) * coordinateDy u z) =
      -(∫ z in modularInterior, (fderiv ℝ φ z Complex.I : ℂ) * coordinateValue u z) := by
  have h := frameTest_closedGradient_pairing_y φ hφ hc hs u
  rw [← LinearIsometryEquiv.apply_symm_apply modularCoordinateEquiv
    ((WithLp.ofLp (closedGradient u)).2), frameTest_inner_lebesgue,
    ← LinearIsometryEquiv.apply_symm_apply modularCoordinateEquiv (u : ModularHilbert),
    divergenceTest_inner_lebesgue] at h
  exact h

end GapFamily.Analytic.ModularGradient
