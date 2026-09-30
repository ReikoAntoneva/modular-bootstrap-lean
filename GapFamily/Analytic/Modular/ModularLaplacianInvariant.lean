import GapFamily.Analytic.Poincare.PoincareModularSmoothTransport
import GapFamily.Analytic.Geometry.LaplacianSeedResidual

/-! The ordinary hyperbolic Laplacian preserves genuine modular invariance. -/
noncomputable section
namespace GapFamily.Analytic.PoincareWeak

open Set UpperHalfPlane LaplacianCovariance
open scoped ContDiff MatrixGroups Topology

/-- Covariance and the actual invariant germ make the literal ordinary Laplacian
invariant. The field is only assumed real smooth on the upper half-plane. -/
theorem ordinaryHyperbolicLaplacian_modularInvariant (F : UpperHalfPlane → ℂ)
    (hF : ∀ (γ : SL(2, ℤ)) (τ : UpperHalfPlane), F (γ • τ) = F τ)
    (hsm : ContDiffOn ℝ ∞ (fun z : ℂ => F (UpperHalfPlane.ofComplex z))
      upperHalfPlaneSet) (γ : SL(2, ℤ)) (τ : UpperHalfPlane) :
    ordinaryHyperbolicLaplacian (fun z : ℂ => F (UpperHalfPlane.ofComplex z))
        (γ • τ : UpperHalfPlane) =
      ordinaryHyperbolicLaplacian (fun z : ℂ => F (UpperHalfPlane.ofComplex z)) τ := by
  have htarget : ContDiffAt ℝ 2 (fun z : ℂ => F (UpperHalfPlane.ofComplex z))
      (γ • τ : UpperHalfPlane) :=
    (hsm.contDiffAt (isOpen_upperHalfPlaneSet.mem_nhds (γ • τ : UpperHalfPlane).im_pos)).of_le
      (by norm_num)
  calc
    _ = ordinaryHyperbolicLaplacian
        ((fun z : ℂ => F (UpperHalfPlane.ofComplex z)) ∘ rawModularAction γ) τ :=
      (ordinaryHyperbolicLaplacian_comp_rawModularAction γ τ htarget).symm
    _ = _ := (ordinaryHyperbolicLaplacian_congr_germ
      (PoincareComplement.modularInvariant_rawAction_germ F hF γ τ)).symm

/-- Equality on the actual closed fundamental domain extends globally for two
genuinely invariant functions, without any measure or smoothness hypothesis. -/
theorem eq_of_modularInvariant_eqOn_fd (F G : UpperHalfPlane → ℂ)
    (hF : ∀ (γ : SL(2, ℤ)) (τ : UpperHalfPlane), F (γ • τ) = F τ)
    (hG : ∀ (γ : SL(2, ℤ)) (τ : UpperHalfPlane), G (γ • τ) = G τ)
    (hfd : EqOn F G ModularGroup.fd) : F = G := by
  funext τ
  obtain ⟨γ, hγ⟩ := ModularGroup.exists_smul_mem_fd τ
  calc
    F τ = F (γ • τ) := (hF γ τ).symm
    _ = G (γ • τ) := hfd hγ
    _ = G τ := hG γ τ

end GapFamily.Analytic.PoincareWeak
