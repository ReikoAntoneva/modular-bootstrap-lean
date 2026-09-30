import GapFamily.Analytic.Modular.ModularGradientCore
import GapFamily.Analytic.Elliptic.GradientLocalDensity

/-!
# Actual compact test fields for the modular gradient

The frame test `y φ` and its formal divergence `-y² ∂φ` are actual modular
Hilbert vectors. Real smooth compact tests suffice to separate arbitrary
complex Hilbert vectors. Their integration-by-parts identity is proved
against the genuine smooth automorphic gradient core.
-/

noncomputable section

namespace GapFamily.Analytic.ModularGradient

open MeasureTheory Set UpperHalfPlane
open scoped ContDiff ComplexConjugate

/-- The actual coordinate `L²` class of a real continuous compactly supported function. -/
def coordinateRealL2 (ψ : ℂ → ℝ) (hψ : Continuous ψ) (hc : HasCompactSupport ψ) :
    ModularCoordinateHilbert :=
  ((Complex.continuous_ofReal.comp hψ).memLp_of_hasCompactSupport
    (hc.comp_left Complex.ofReal_zero)).toLp (fun z => (ψ z : ℂ))

theorem coordinateRealL2_ae (ψ : ℂ → ℝ) (hψ : Continuous ψ) (hc : HasCompactSupport ψ) :
    coordinateRealL2 ψ hψ hc =ᵐ[modularCoordinateMeasure] fun z => (ψ z : ℂ) :=
  MemLp.coeFn_toLp _

/-- The scaled scalar component of an interior gradient test field. -/
def frameTest (φ : ℂ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) : ModularHilbert :=
  modularCoordinateEquiv (coordinateRealL2 (fun z => z.im * φ z)
    (Complex.continuous_im.mul hφ.continuous) hc.mul_left)

theorem frameTest_ae (φ : ℂ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    frameTest φ hφ hc =ᵐ[modularMeasure] fun τ : UpperHalfPlane => (τ.im * φ τ : ℝ) := by
  have h := coordinateRealL2_ae (fun z => z.im * φ z)
    (Complex.continuous_im.mul hφ.continuous) hc.mul_left
  exact (modularCoordinateEquiv_apply_ae _).trans ((ae_modularCoordinate_iff _).mp h)

theorem continuous_testDerivative (φ : ℂ → ℝ) (hφ : ContDiff ℝ ∞ φ) (v : ℂ) :
    Continuous (fun z => fderiv ℝ φ z v) :=
  (hφ.continuous_fderiv_apply (by simp)).comp (continuous_id.prodMk continuous_const)

theorem compactSupport_testDivergence (φ : ℂ → ℝ) (hc : HasCompactSupport φ) (v : ℂ) :
    HasCompactSupport (fun z => -(z.im ^ 2 * fderiv ℝ φ z v)) := by
  have hD : HasCompactSupport (fun z : ℂ => fderiv ℝ φ z v) := hc.fderiv_apply ℝ v
  exact (hD.mul_left (f := fun z : ℂ => z.im ^ 2)).neg

/-- The genuine divergence component which pairs with a frame test. -/
def divergenceTest (φ : ℂ → ℝ) (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (v : ℂ) : ModularHilbert :=
  modularCoordinateEquiv (coordinateRealL2 (fun z => -(z.im ^ 2 * fderiv ℝ φ z v))
    (((Complex.continuous_im.pow 2).mul (continuous_testDerivative φ hφ v)).neg)
    (compactSupport_testDivergence φ hc v))

theorem divergenceTest_ae (φ : ℂ → ℝ) (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (v : ℂ) :
    divergenceTest φ hφ hc v =ᵐ[modularMeasure]
      fun τ : UpperHalfPlane => (-(τ.im ^ 2 * fderiv ℝ φ τ v) : ℝ) := by
  have h := coordinateRealL2_ae (fun z => -(z.im ^ 2 * fderiv ℝ φ z v))
    (((Complex.continuous_im.pow 2).mul (continuous_testDerivative φ hφ v)).neg)
    (compactSupport_testDivergence φ hc v)
  exact (modularCoordinateEquiv_apply_ae _).trans ((ae_modularCoordinate_iff _).mp h)

theorem frameTest_inner_coordinate (φ : ℂ → ℝ) (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (f : ModularCoordinateHilbert) :
    inner ℂ (frameTest φ hφ hc) (modularCoordinateEquiv f) =
      ∫ z, φ z • (z.im • f z) ∂modularCoordinateMeasure := by
  rw [frameTest, modularCoordinateEquiv.inner_map_map, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [coordinateRealL2_ae (fun z => z.im * φ z)
    (Complex.continuous_im.mul hφ.continuous) hc.mul_left] with z hz
  simp [hz, RCLike.inner_apply, Complex.real_smul, mul_comm, mul_left_comm, mul_assoc]

/-- The actual scaled interior tests separate all modular `L²` vectors. -/
theorem frameTest_separates (f : ModularHilbert)
    (h : ∀ (φ : ℂ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ),
      tsupport φ ⊆ modularInterior → inner ℂ (frameTest φ hφ hc) f = 0) : f = 0 := by
  have hz : modularCoordinateEquiv.symm f = 0 := by
    apply weightedLocalTest_L2_eq_zero _ isOpen_modularInterior ae_mem_modularInterior
      Complex.continuous_im.continuousOn (fun z hz => (im_pos_of_mem_modularInterior hz).ne')
    intro φ hφ hc hs
    rw [← frameTest_inner_coordinate φ hφ hc (modularCoordinateEquiv.symm f),
      LinearIsometryEquiv.apply_symm_apply]
    exact h φ hφ hc hs
  apply modularCoordinateEquiv.symm.injective
  simpa using hz

theorem fderiv_realTest (φ : ℂ → ℝ) (hφ : ContDiff ℝ ∞ φ) (z v : ℂ) :
    fderiv ℝ (fun w => (φ w : ℂ)) z v = (fderiv ℝ φ z v : ℂ) := by
  have h := Complex.ofRealCLM.hasFDerivAt.comp z
    ((hφ.differentiable (by simp) z).hasFDerivAt)
  exact congrArg (fun L : ℂ →L[ℝ] ℂ => L v) h.fderiv

/-- The ordinary scalar formal-adjoint identity against an actual core derivative. -/
theorem frameTest_core_pairing (φ : ℂ → ℝ) (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ modularInterior)
    (v : ℂ) (hmem : ∀ F : smoothCore, MemLp (directional F.val v) 2 modularMeasure)
    (F : smoothCore) :
    inner ℂ (frameTest φ hφ hc) (component v hmem F) =
      inner ℂ (divergenceTest φ hφ hc v) (value F) := by
  have hleft : inner ℂ (frameTest φ hφ hc) (component v hmem F) =
      ∫ z, ((z.im : ℂ) * fderiv ℝ F.val z v) * ((z.im : ℂ) * (φ z : ℂ))
        ∂modularCoordinateMeasure := by
    rw [integral_modularCoordinate, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [frameTest_ae φ hφ hc, component_ae v hmem F] with τ ht hd
    simp [ht, hd, directional, RCLike.inner_apply, mul_comm, mul_left_comm]
  have hright : inner ℂ (divergenceTest φ hφ hc v) (value F) =
      -(∫ z, F.val z * ((z.im : ℂ) ^ 2 * fderiv ℝ (fun w => (φ w : ℂ)) z v)
        ∂modularCoordinateMeasure) := by
    rw [integral_modularCoordinate, ← integral_neg, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [divergenceTest_ae φ hφ hc v, value_ae F] with τ ht hv
    simp [ht, hv, fderiv_realTest φ hφ, RCLike.inner_apply, mul_left_comm]
  rw [hleft, hright]
  apply Dirichlet.local_hyperbolic_gradient_test_identity isOpen_modularInterior
    (fun _ hz => im_pos_of_mem_modularInterior hz)
  · exact (F.property.1.of_le (by simp)).mono (fun _ hz => im_pos_of_mem_modularInterior hz)
  · exact (Complex.ofRealCLM.contDiff.comp hφ).of_le (by simp)
  · exact hc.comp_left Complex.ofReal_zero
  · exact (tsupport_comp_subset Complex.ofReal_zero φ).trans hs

end GapFamily.Analytic.ModularGradient
