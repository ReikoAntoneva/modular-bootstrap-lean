import GapFamily.Analytic.Modular.Periodization.ModularPeriodizationAction
import Mathlib.NumberTheory.Modular

noncomputable section
namespace GapFamily.Analytic.PoincareComplement
open Set Filter UpperHalfPlane
open scoped ContDiff MatrixGroups Topology

/-- Actual invariance identifies the ambient function with its raw modular pullback
on a neighborhood of each upper-half-plane point. -/
theorem modularInvariant_rawAction_germ (F : UpperHalfPlane → ℂ)
    (hF : ∀ (γ : SL(2, ℤ)) (τ : UpperHalfPlane), F (γ • τ) = F τ)
    (γ : SL(2, ℤ)) (τ : UpperHalfPlane) :
    (fun z : ℂ => F (UpperHalfPlane.ofComplex z)) =ᶠ[𝓝 (τ : ℂ)]
      ((fun z : ℂ => F (UpperHalfPlane.ofComplex z)) ∘ rawModularAction γ) := by
  filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds τ.im_pos] with z hz
  change F (UpperHalfPlane.ofComplex z) = F (UpperHalfPlane.ofComplex (rawModularAction γ z))
  rw [rawModularAction_coe γ (⟨z, hz⟩ : UpperHalfPlane),
    UpperHalfPlane.ofComplex_apply, UpperHalfPlane.ofComplex_apply_of_im_pos hz]
  exact (hF γ (⟨z, hz⟩ : UpperHalfPlane)).symm

/-- Smoothness above height one half transfers to each point using an actual
closed-fundamental-domain representative and the smooth real modular action. -/
theorem contDiffAt_of_modularInvariant_of_halfHeight (F : UpperHalfPlane → ℂ)
    (hF : ∀ (γ : SL(2, ℤ)) (τ : UpperHalfPlane), F (γ • τ) = F τ)
    (hstrip : ContDiffOn ℝ ∞ (fun z : ℂ => F (UpperHalfPlane.ofComplex z))
      {z : ℂ | (1 / 2 : ℝ) < z.im}) (τ : UpperHalfPlane) :
    ContDiffAt ℝ ∞ (fun z : ℂ => F (UpperHalfPlane.ofComplex z)) τ := by
  obtain ⟨γ, hγ⟩ := ModularGroup.exists_smul_mem_fd τ
  have hheight : (1 / 2 : ℝ) < (γ • τ : UpperHalfPlane).im := by
    have h := ModularGroup.three_le_four_mul_im_sq_of_mem_fd hγ
    nlinarith [(γ • τ : UpperHalfPlane).im_pos]
  have htarget : ContDiffAt ℝ ∞ (fun z : ℂ => F (UpperHalfPlane.ofComplex z))
      (rawModularAction γ τ) := by
    rw [rawModularAction_coe]
    exact hstrip.contDiffAt
      ((isOpen_lt continuous_const Complex.continuous_im).mem_nhds hheight)
  have hraw : ContDiffAt ℝ ∞ (rawModularAction γ) τ :=
    (contDiffOn_rawModularAction γ).contDiffAt
      (isOpen_upperHalfPlaneSet.mem_nhds τ.im_pos)
  exact (htarget.comp (τ : ℂ) hraw).congr_of_eventuallyEq
    (modularInvariant_rawAction_germ F hF γ τ)

/-- An actual invariant function smooth above height one half is smooth throughout H. -/
theorem contDiffOn_of_modularInvariant_of_halfHeight (F : UpperHalfPlane → ℂ)
    (hF : ∀ (γ : SL(2, ℤ)) (τ : UpperHalfPlane), F (γ • τ) = F τ)
    (hstrip : ContDiffOn ℝ ∞ (fun z : ℂ => F (UpperHalfPlane.ofComplex z))
      {z : ℂ | (1 / 2 : ℝ) < z.im}) :
    ContDiffOn ℝ ∞ (fun z : ℂ => F (UpperHalfPlane.ofComplex z))
      upperHalfPlaneSet := by
  intro z hz
  exact (contDiffAt_of_modularInvariant_of_halfHeight F hF hstrip
    (⟨z, hz⟩ : UpperHalfPlane)).contDiffWithinAt

end GapFamily.Analytic.PoincareComplement
