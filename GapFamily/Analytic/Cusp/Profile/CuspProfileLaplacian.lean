import GapFamily.Analytic.Cusp.Profile.CuspProfileLaplacianSource
import GapFamily.Analytic.Cusp.Profile.CuspProfileGradientPairing
import GapFamily.Analytic.Modular.Elliptic.ModularInteriorCompactCore
import GapFamily.Analytic.Modular.ModularLaplacian

/-!
# Compact scalar profiles in the actual modular Laplacian domain

Actual cusp Fubini and one-dimensional integration by parts first give the
identity on the genuine smooth graph core. Its proved density extends that
identity to every completed form test. The actual adjoint-domain criterion then
puts the scalar profile in the full modular Laplacian domain.
-/

noncomputable section

namespace GapFamily.Analytic

open Set MeasureTheory UpperHalfPlane ModularGradient
open scoped ContDiff

theorem cuspProfileCore_energy_pairing (b : ℝ → ℂ) (hb : ContDiff ℝ ∞ b)
    (hc : HasCompactSupport b) (hs : tsupport b ⊆ Ioi (1 : ℝ)) (F : smoothCore) :
    inner ℂ (coreGradient (cuspProfileCore b hb hc hs)) (coreGradient F) =
      inner ℂ (cuspProfileLaplacianValue b hb hc hs) (value F) := by
  rw [cuspProfileCore_gradient_pairing, cuspProfileLaplacianValue_pairing]
  exact cuspProfileLaplacian_integral_deriv_mul hb hc hs (contDiffOn_cuspHorizontalAverage F)

/-- The profile's true full-form weak equation, with no constraint on the test vector. -/
theorem cuspProfileCore_form_energy (b : ℝ → ℂ) (hb : ContDiff ℝ ∞ b)
    (hc : HasCompactSupport b) (hs : tsupport b ⊆ Ioi (1 : ℝ)) (u : FormDomain) :
    inner ℂ (cuspProfileLaplacianValue b hb hc hs) (formEmbedding u) =
      inner ℂ (coreGradient (cuspProfileCore b hb hc hs)) (formGradient u) := by
  refine coreForm_denseRange.induction_on (p := fun u : FormDomain =>
    inner ℂ (cuspProfileLaplacianValue b hb hc hs) (formEmbedding u) =
      inner ℂ (coreGradient (cuspProfileCore b hb hc hs)) (formGradient u)) u ?_ ?_
  · exact isClosed_eq (by fun_prop) (by fun_prop)
  · intro F
    simpa only [formEmbedding_coreForm, formGradient_coreForm] using
      (cuspProfileCore_energy_pairing b hb hc hs F).symm

theorem cuspProfileCore_mem_closedGradient_domain (b : ℝ → ℂ) (hb : ContDiff ℝ ∞ b)
    (hc : HasCompactSupport b) (hs : tsupport b ⊆ Ioi (1 : ℝ)) :
    value (cuspProfileCore b hb hc hs) ∈ closedGradient.domain :=
  gradient_le_closedGradient.1 (LinearMap.mem_range_self value _)

/-- Actual adjoint pairing against every vector in the full first-order domain. -/
theorem cuspProfileCore_closedGradient_energy (b : ℝ → ℂ) (hb : ContDiff ℝ ∞ b)
    (hc : HasCompactSupport b) (hs : tsupport b ⊆ Ioi (1 : ℝ))
    (u : closedGradient.domain) :
    inner ℂ (cuspProfileLaplacianValue b hb hc hs) (u : ModularHilbert) =
      inner ℂ (closedGradient ⟨value (cuspProfileCore b hb hc hs),
        cuspProfileCore_mem_closedGradient_domain b hb hc hs⟩) (closedGradient u) := by
  rw [closedGradient_apply_value]
  exact cuspProfileCore_form_energy b hb hc hs (formLift u)

/-- The compact scalar profile belongs to the actual full modular Laplacian domain. -/
theorem cuspProfileCore_mem_laplacian_domain (b : ℝ → ℂ) (hb : ContDiff ℝ ∞ b)
    (hc : HasCompactSupport b) (hs : tsupport b ⊆ Ioi (1 : ℝ)) :
    value (cuspProfileCore b hb hc hs) ∈ laplacian.domain := by
  apply (laplacian_domain_iff ⟨value (cuspProfileCore b hb hc hs),
    cuspProfileCore_mem_closedGradient_domain b hb hc hs⟩).mpr
  apply closedGradient.mem_adjoint_domain_of_exists
  exact ⟨cuspProfileLaplacianValue b hb hc hs,
    cuspProfileCore_closedGradient_energy b hb hc hs⟩

/-- The full modular Laplacian has exactly the scalar value -y²b'' on the profile. -/
theorem laplacian_cuspProfileCore (b : ℝ → ℂ) (hb : ContDiff ℝ ∞ b)
    (hc : HasCompactSupport b) (hs : tsupport b ⊆ Ioi (1 : ℝ)) :
    laplacian ⟨value (cuspProfileCore b hb hc hs),
      cuspProfileCore_mem_laplacian_domain b hb hc hs⟩ =
        cuspProfileLaplacianValue b hb hc hs := by
  apply closedGradient_dense_domain.eq_of_inner_left ℂ
  intro u hu
  exact (laplacian_representation _ ⟨u, hu⟩).trans
    (cuspProfileCore_closedGradient_energy b hb hc hs ⟨u, hu⟩).symm

theorem laplacian_cuspProfileCore_ae (b : ℝ → ℂ) (hb : ContDiff ℝ ∞ b)
    (hc : HasCompactSupport b) (hs : tsupport b ⊆ Ioi (1 : ℝ)) :
    laplacian ⟨value (cuspProfileCore b hb hc hs),
      cuspProfileCore_mem_laplacian_domain b hb hc hs⟩ =ᵐ[modularMeasure]
      fun τ : UpperHalfPlane => -((τ.im : ℂ) ^ 2) * deriv (deriv b) τ.im := by
  rw [laplacian_cuspProfileCore]
  exact cuspProfileLaplacianValue_ae b hb hc hs

end GapFamily.Analytic
