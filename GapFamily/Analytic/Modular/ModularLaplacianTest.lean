import GapFamily.Analytic.Modular.ModularLaplacian
import GapFamily.Analytic.Modular.ModularGradientDistribution

/-!
# Compact interior tests in the actual Laplacian domain

The automorphic extension of a real smooth compact interior test belongs to
the second-order operator domain. Its actual operator value is the coordinate
expression `-y² (∂x² + ∂y²) φ`, proved from the closed-gradient test identities.
-/

noncomputable section

namespace GapFamily.Analytic.ModularGradient

open Set MeasureTheory
open scoped ContDiff

theorem contDiff_testDerivative (φ : ℂ → ℝ) (hφ : ContDiff ℝ ∞ φ) (v : ℂ) :
    ContDiff ℝ ∞ (fun z => fderiv ℝ φ z v) :=
  (hφ.fderiv_right (by simp)).clm_apply contDiff_const

/-- The actual class of a real smooth compact test. -/
def realTest (φ : ℂ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    ModularHilbert := modularCoordinateEquiv (coordinateRealL2 φ hφ.continuous hc)

theorem realTest_ae (φ : ℂ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    realTest φ hφ hc =ᵐ[modularMeasure] fun τ : UpperHalfPlane => (φ τ : ℂ) :=
  (modularCoordinateEquiv_apply_ae _).trans
    ((ae_modularCoordinate_iff _).mp (coordinateRealL2_ae φ hφ.continuous hc))

/-- A smooth automorphic representative of the compact interior test. -/
def realTestCore (φ : ℂ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ modularInterior) : smoothCore :=
  periodizedCore (fun z => (φ z : ℂ)) (Complex.ofRealCLM.contDiff.comp hφ)
    (hc.comp_left Complex.ofReal_zero) ((tsupport_comp_subset Complex.ofReal_zero φ).trans hs)

theorem value_realTestCore (φ : ℂ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ modularInterior) : value (realTestCore φ hφ hc hs) = realTest φ hφ hc := by
  apply Lp.ext
  exact (value_periodizedCore_ae _ _ _ _).trans (realTest_ae φ hφ hc).symm

theorem component_realTestCore (φ : ℂ → ℝ) (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ modularInterior)
    (v : ℂ) (hmem : ∀ F : smoothCore, MemLp (directional F.val v) 2 modularMeasure) :
    component v hmem (realTestCore φ hφ hc hs) =
      frameTest (fun z => fderiv ℝ φ z v) (contDiff_testDerivative φ hφ v)
        (hc.fderiv_apply ℝ v) := by
  apply Lp.ext
  have hp := modularPeriodization_directional_ae (Complex.ofRealCLM.contDiff.comp hφ)
    (hc.comp_left Complex.ofReal_zero) ((tsupport_comp_subset Complex.ofReal_zero φ).trans hs) v
  filter_upwards [component_ae v hmem (realTestCore φ hφ hc hs), hp,
    frameTest_ae (fun z => fderiv ℝ φ z v) (contDiff_testDerivative φ hφ v)
      (hc.fderiv_apply ℝ v)] with τ hcomp hper hframe
  change directional (realTestCore φ hφ hc hs).val v τ = directional (fun z => (φ z : ℂ)) v τ
    at hper
  rw [hcomp, hper, hframe]
  simp only [directional, fderiv_realTest φ hφ, Complex.ofReal_mul]

theorem realTest_mem_closedGradient_domain (φ : ℂ → ℝ) (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ modularInterior) :
    realTest φ hφ hc ∈ closedGradient.domain := by
  rw [← value_realTestCore φ hφ hc hs]
  exact gradient_le_closedGradient.1 (LinearMap.mem_range_self value _)

theorem closedGradient_realTest_x (φ : ℂ → ℝ) (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ modularInterior) :
    (WithLp.ofLp (closedGradient ⟨realTest φ hφ hc,
      realTest_mem_closedGradient_domain φ hφ hc hs⟩)).1 =
      frameTest (fun z => fderiv ℝ φ z 1) (contDiff_testDerivative φ hφ 1)
        (hc.fderiv_apply ℝ 1) := by
  have h := congrArg (fun p : GradientSpace => (WithLp.ofLp p).1)
    (closedGradient_apply_value (realTestCore φ hφ hc hs))
  rw [coreGradient_fst, xComponent, component_realTestCore] at h
  simpa only [value_realTestCore] using h

theorem closedGradient_realTest_y (φ : ℂ → ℝ) (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ modularInterior) :
    (WithLp.ofLp (closedGradient ⟨realTest φ hφ hc,
      realTest_mem_closedGradient_domain φ hφ hc hs⟩)).2 =
      frameTest (fun z => fderiv ℝ φ z Complex.I) (contDiff_testDerivative φ hφ Complex.I)
        (hc.fderiv_apply ℝ Complex.I) := by
  have h := congrArg (fun p : GradientSpace => (WithLp.ofLp p).2)
    (closedGradient_apply_value (realTestCore φ hφ hc hs))
  rw [coreGradient_snd, yComponent, component_realTestCore] at h
  simpa only [value_realTestCore] using h

/-- The explicit second-order value in the actual Hilbert space. -/
def realTestLaplacian (φ : ℂ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    ModularHilbert :=
  divergenceTest (fun z => fderiv ℝ φ z 1) (contDiff_testDerivative φ hφ 1)
      (hc.fderiv_apply ℝ 1) 1 +
    divergenceTest (fun z => fderiv ℝ φ z Complex.I) (contDiff_testDerivative φ hφ Complex.I)
      (hc.fderiv_apply ℝ Complex.I) Complex.I

theorem realTestLaplacian_energy (φ : ℂ → ℝ) (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ modularInterior)
    (u : closedGradient.domain) :
    inner ℂ (realTestLaplacian φ hφ hc) (u : ModularHilbert) =
      inner ℂ (closedGradient ⟨realTest φ hφ hc,
        realTest_mem_closedGradient_domain φ hφ hc hs⟩) (closedGradient u) := by
  change _ = inner ℂ (WithLp.ofLp (closedGradient ⟨realTest φ hφ hc,
      realTest_mem_closedGradient_domain φ hφ hc hs⟩)).1 (WithLp.ofLp (closedGradient u)).1 +
    inner ℂ (WithLp.ofLp (closedGradient ⟨realTest φ hφ hc,
      realTest_mem_closedGradient_domain φ hφ hc hs⟩)).2 (WithLp.ofLp (closedGradient u)).2
  rw [closedGradient_realTest_x φ hφ hc hs, closedGradient_realTest_y φ hφ hc hs]
  rw [frameTest_closedGradient_pairing_x _ _ _ ((tsupport_fderiv_apply_subset ℝ 1).trans hs),
    frameTest_closedGradient_pairing_y _ _ _ ((tsupport_fderiv_apply_subset ℝ Complex.I).trans hs)]
  exact inner_add_left _ _ _

theorem realTest_mem_laplacian_domain (φ : ℂ → ℝ) (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ modularInterior) :
    realTest φ hφ hc ∈ laplacian.domain := by
  apply (laplacian_domain_iff
    ⟨realTest φ hφ hc, realTest_mem_closedGradient_domain φ hφ hc hs⟩).mpr
  apply closedGradient.mem_adjoint_domain_of_exists
  exact ⟨realTestLaplacian φ hφ hc, realTestLaplacian_energy φ hφ hc hs⟩

theorem laplacian_realTest (φ : ℂ → ℝ) (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ modularInterior) :
    laplacian ⟨realTest φ hφ hc, realTest_mem_laplacian_domain φ hφ hc hs⟩ =
      realTestLaplacian φ hφ hc := by
  apply closedGradient_dense_domain.eq_of_inner_left ℂ
  intro u hu
  exact (laplacian_representation _ ⟨u, hu⟩).trans
    (realTestLaplacian_energy φ hφ hc hs ⟨u, hu⟩).symm

/-- The usual sum of the two real second directional derivatives. -/
def euclideanTestLaplacian (φ : ℂ → ℝ) (z : ℂ) : ℝ :=
  fderiv ℝ (fun w => fderiv ℝ φ w 1) z 1 +
    fderiv ℝ (fun w => fderiv ℝ φ w Complex.I) z Complex.I

theorem realTestLaplacian_ae (φ : ℂ → ℝ) (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) :
    realTestLaplacian φ hφ hc =ᵐ[modularMeasure] fun τ : UpperHalfPlane =>
      (-(τ.im ^ 2 * euclideanTestLaplacian φ τ) : ℝ) := by
  unfold realTestLaplacian
  filter_upwards [Lp.coeFn_add
    (divergenceTest (fun z => fderiv ℝ φ z 1) (contDiff_testDerivative φ hφ 1)
      (hc.fderiv_apply ℝ 1) 1)
    (divergenceTest (fun z => fderiv ℝ φ z Complex.I) (contDiff_testDerivative φ hφ Complex.I)
      (hc.fderiv_apply ℝ Complex.I) Complex.I),
    divergenceTest_ae (fun z => fderiv ℝ φ z 1) (contDiff_testDerivative φ hφ 1)
      (hc.fderiv_apply ℝ 1) 1,
    divergenceTest_ae (fun z => fderiv ℝ φ z Complex.I) (contDiff_testDerivative φ hφ Complex.I)
      (hc.fderiv_apply ℝ Complex.I) Complex.I] with τ ha hx hy
  rw [ha, Pi.add_apply, hx, hy]
  simp only [euclideanTestLaplacian, Complex.ofReal_neg, Complex.ofReal_mul,
    Complex.ofReal_add]
  ring

/-- The actual operator has the geometric differential expression on compact interior tests. -/
theorem laplacian_realTest_ae (φ : ℂ → ℝ) (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ modularInterior) :
    laplacian ⟨realTest φ hφ hc, realTest_mem_laplacian_domain φ hφ hc hs⟩
      =ᵐ[modularMeasure] fun τ : UpperHalfPlane =>
        (-(τ.im ^ 2 * euclideanTestLaplacian φ τ) : ℝ) := by
  rw [laplacian_realTest φ hφ hc hs]
  exact realTestLaplacian_ae φ hφ hc

theorem realTestLaplacian_test_integrable (φ : ℂ → ℝ) (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (f : ModularCoordinateHilbert) :
    IntegrableOn (fun z => (euclideanTestLaplacian φ z : ℂ) * f z) modularInterior := by
  have hx := divergenceTest_lebesgue_integrable (fun z => fderiv ℝ φ z 1)
    (contDiff_testDerivative φ hφ 1) (hc.fderiv_apply ℝ 1) 1 f
  have hy := divergenceTest_lebesgue_integrable (fun z => fderiv ℝ φ z Complex.I)
    (contDiff_testDerivative φ hφ Complex.I) (hc.fderiv_apply ℝ Complex.I) Complex.I f
  apply (hx.add hy).congr
  filter_upwards [] with z
  simp only [euclideanTestLaplacian, Complex.ofReal_add, add_mul, Pi.add_apply]

theorem realTestLaplacian_inner_lebesgue (φ : ℂ → ℝ) (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (f : ModularCoordinateHilbert) :
    inner ℂ (realTestLaplacian φ hφ hc) (modularCoordinateEquiv f) =
      -(∫ z in modularInterior, (euclideanTestLaplacian φ z : ℂ) * f z) := by
  rw [realTestLaplacian, inner_add_left, divergenceTest_inner_lebesgue,
    divergenceTest_inner_lebesgue, ← neg_add]
  congr 1
  rw [← integral_add
    (divergenceTest_lebesgue_integrable (fun z => fderiv ℝ φ z 1)
      (contDiff_testDerivative φ hφ 1) (hc.fderiv_apply ℝ 1) 1 f)
    (divergenceTest_lebesgue_integrable (fun z => fderiv ℝ φ z Complex.I)
      (contDiff_testDerivative φ hφ Complex.I) (hc.fderiv_apply ℝ Complex.I) Complex.I f)]
  apply integral_congr_ae
  filter_upwards [] with z
  simp only [euclideanTestLaplacian, Complex.ofReal_add, add_mul]

theorem realTest_laplacian_pairing (φ : ℂ → ℝ) (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ modularInterior)
    (u : laplacian.domain) :
    inner ℂ (realTest φ hφ hc) (laplacian u) =
      inner ℂ (realTestLaplacian φ hφ hc) (u : ModularHilbert) := by
  have h := laplacian_representation u
    ⟨realTest φ hφ hc, realTest_mem_closedGradient_domain φ hφ hc hs⟩
  have hswap : inner ℂ (realTest φ hφ hc) (laplacian u) =
      inner ℂ (closedGradient ⟨realTest φ hφ hc,
        realTest_mem_closedGradient_domain φ hφ hc hs⟩)
        (closedGradient ⟨u, laplacian_domain_le u.property⟩) := by
    simpa only [inner_conj_symm] using congrArg (starRingEnd ℂ) h
  exact hswap.trans (realTestLaplacian_energy φ hφ hc hs
    ⟨u, laplacian_domain_le u.property⟩).symm

end GapFamily.Analytic.ModularGradient
