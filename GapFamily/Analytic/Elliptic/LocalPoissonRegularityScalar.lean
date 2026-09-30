import GapFamily.Analytic.Elliptic.LocalPoissonJet
import GapFamily.Analytic.Modular.Elliptic.ModularEllipticScalar

/-! Real scalar projections of the actual integrable complex jet equations. -/
noncomputable section
namespace GapFamily.Analytic.LocalPoisson
open Set MeasureTheory ModularGradient
open scoped ContDiff

theorem scalar_weak_x (L : ℂ →L[ℝ] ℝ) (U : Set ℂ) (u : JetSpace U)
    (φ : ℂ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hcφ : HasCompactSupport φ)
    (hφU : tsupport φ ⊆ U) :
    (∫ z : ℂ, L (valueCLM U u z) * fderiv ℝ φ z 1) =
      -(∫ z : ℂ, L (dxCLM U u z) * φ z) := by
  have hφC : ContDiff ℝ ∞ (fun z => (φ z : ℂ)) := Complex.ofRealCLM.contDiff.comp hφ
  have hcC : HasCompactSupport (fun z => (φ z : ℂ)) := hcφ.comp_left Complex.ofReal_zero
  have hsC : tsupport (fun z => (φ z : ℂ)) ⊆ U :=
    (tsupport_comp_subset Complex.ofReal_zero φ).trans hφU
  have h := congrArg L (weak_dx U u _ hφC hcC hsC)
  have hi₁ := test_integrable _ hφC.continuous hcC (dxCLM U u)
  have hi₂ := derivative_test_integrable _ hφC hcC 1 (valueCLM U u)
  rw [map_neg, ← L.integral_comp_comm hi₁, ← L.integral_comp_comm hi₂] at h
  simp only [fderiv_realTest φ hφ, Complex.star_def, Complex.conj_ofReal,
    ellipticScalar_real_mul] at h
  linarith

theorem scalar_weak_y (L : ℂ →L[ℝ] ℝ) (U : Set ℂ) (u : JetSpace U)
    (φ : ℂ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hcφ : HasCompactSupport φ)
    (hφU : tsupport φ ⊆ U) :
    (∫ z : ℂ, L (valueCLM U u z) * fderiv ℝ φ z Complex.I) =
      -(∫ z : ℂ, L (dyCLM U u z) * φ z) := by
  have hφC : ContDiff ℝ ∞ (fun z => (φ z : ℂ)) := Complex.ofRealCLM.contDiff.comp hφ
  have hcC : HasCompactSupport (fun z => (φ z : ℂ)) := hcφ.comp_left Complex.ofReal_zero
  have hsC : tsupport (fun z => (φ z : ℂ)) ⊆ U :=
    (tsupport_comp_subset Complex.ofReal_zero φ).trans hφU
  have h := congrArg L (weak_dy U u _ hφC hcC hsC)
  have hi₁ := test_integrable _ hφC.continuous hcC (dyCLM U u)
  have hi₂ := derivative_test_integrable _ hφC hcC Complex.I (valueCLM U u)
  rw [map_neg, ← L.integral_comp_comm hi₁, ← L.integral_comp_comm hi₂] at h
  simp only [fderiv_realTest φ hφ, Complex.star_def, Complex.conj_ofReal,
    ellipticScalar_real_mul] at h
  linarith

theorem scalar_poisson (L : ℂ →L[ℝ] ℝ) (U : Set ℂ) (u : JetSpace U)
    (φ : ℂ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hcφ : HasCompactSupport φ)
    (hφU : tsupport φ ⊆ U) :
    (∫ z : ℂ, L (dxCLM U u z) * fderiv ℝ φ z 1 +
      L (dyCLM U u z) * fderiv ℝ φ z Complex.I) =
      ∫ z : ℂ, L (sourceCLM U u z) * φ z := by
  have hφC : ContDiff ℝ ∞ (fun z => (φ z : ℂ)) := Complex.ofRealCLM.contDiff.comp hφ
  have hcC : HasCompactSupport (fun z => (φ z : ℂ)) := hcφ.comp_left Complex.ofReal_zero
  have hsC : tsupport (fun z => (φ z : ℂ)) ⊆ U :=
    (tsupport_comp_subset Complex.ofReal_zero φ).trans hφU
  have h := congrArg L (weak_poisson U u _ hφC hcC hsC)
  have hi₁ : Integrable (fun z : ℂ =>
      star (fderiv ℝ (fun w => (φ w : ℂ)) z 1) * dxCLM U u z +
      star (fderiv ℝ (fun w => (φ w : ℂ)) z Complex.I) * dyCLM U u z) volume :=
    (derivative_test_integrable _ hφC hcC 1 (dxCLM U u)).add
      (derivative_test_integrable _ hφC hcC Complex.I (dyCLM U u))
  have hi₂ := test_integrable _ hφC.continuous hcC (sourceCLM U u)
  rw [← L.integral_comp_comm hi₁, ← L.integral_comp_comm hi₂] at h
  simpa only [fderiv_realTest φ hφ, Complex.star_def, Complex.conj_ofReal, map_add,
    ellipticScalar_real_mul] using h


end GapFamily.Analytic.LocalPoisson
