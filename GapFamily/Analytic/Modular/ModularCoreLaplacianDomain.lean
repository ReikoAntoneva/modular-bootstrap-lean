import GapFamily.Analytic.Modular.ModularCoreWeakPairing
import GapFamily.Analytic.Modular.ModularCompactCorePeriodization
import GapFamily.Analytic.Modular.ModularFormTruncation
import GapFamily.Analytic.Cusp.Schur.CuspSchurOperatorBridge

noncomputable section
namespace GapFamily.Analytic.PoincareGreen
open Set Filter MeasureTheory UpperHalfPlane ModularGradient LaplacianCovariance
open scoped ContDiff Topology

/-- Compact upper tests determine the full closed energy form, using actual
finite-height core approximation and actual compact-seed reconstruction. -/
theorem core_form_pairing_of_weak (F G : smoothCore)
    (hweak : ∀ (ψ : ℂ → ℂ), ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ upperHalfPlaneSet →
      (∫ z : ℂ, star (ordinaryHyperbolicLaplacian ψ z) * F.val z / (z.im : ℂ)^2) =
        ∫ z : ℂ, star (ψ z) * G.val z / (z.im : ℂ)^2)
    (t : FormDomain) :
    inner ℂ (formGradient t) (formGradient (coreForm F)) =
      inner ℂ (formEmbedding t) (value G) := by
  have hfinite (Q : smoothCore) (H : ℝ)
      (hzero : ∀ τ : UpperHalfPlane, τ ∈ ModularGroup.fd → H < τ.im → Q.val τ = 0) :
      inner ℂ (formGradient (coreForm Q)) (formGradient (coreForm F)) =
        inner ℂ (formEmbedding (coreForm Q)) (value G) := by
    obtain ⟨ψ, hψ, hc, hs, heq⟩ := exists_periodizedUpperCore_coreForm_eq_of_cusp_zero Q H hzero
    rw [← heq]
    exact core_form_pairing_periodized_of_weak F G hweak ψ hψ hc hs
  have hclosed : IsClosed {v : FormDomain |
      inner ℂ (formGradient v) (formGradient (coreForm F)) =
        inner ℂ (formEmbedding v) (value G)} :=
    isClosed_eq (formGradient.continuous.inner continuous_const)
      (formEmbedding.continuous.inner continuous_const)
  have hcore (Q : smoothCore) : coreForm Q ∈ {v : FormDomain |
      inner ℂ (formGradient v) (formGradient (coreForm F)) =
        inner ℂ (formEmbedding v) (value G)} := by
    obtain ⟨Qn, hQn, hlim⟩ := FormTruncation.exists_finiteHeight_core_approximation Q
    apply hclosed.mem_of_tendsto hlim
    apply Eventually.of_forall
    intro n
    obtain ⟨H, hH⟩ := hQn n
    exact hfinite (Qn n) H hH
  exact coreForm_denseRange.induction_on t hclosed hcore

/-- A true smooth-core distribution equation puts the literal Hilbert value in
the actual Laplacian domain and identifies its operator value. -/
theorem exists_laplacian_value_of_core_weak (F G : smoothCore)
    (hweak : ∀ (ψ : ℂ → ℂ), ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ upperHalfPlaneSet →
      (∫ z : ℂ, star (ordinaryHyperbolicLaplacian ψ z) * F.val z / (z.im : ℂ)^2) =
        ∫ z : ℂ, star (ψ z) * G.val z / (z.im : ℂ)^2) :
    ∃ hu : value F ∈ laplacian.domain, laplacian ⟨value F, hu⟩ = value G := by
  have hform : ∀ t : FormDomain, CuspSchur.formPairing 0 t (coreForm F) =
      inner ℂ (formEmbedding t) (value G) := by
    intro t
    simpa only [CuspSchur.formPairing, zero_mul, sub_zero] using
      core_form_pairing_of_weak F G hweak t
  have hu := CuspSchur.formEmbedding_mem_laplacian_domain_of_formPairing 0 (coreForm F) (value G) hform
  have hA := CuspSchur.laplacian_sub_smul_of_formPairing 0 (coreForm F) (value G) hform
  have hout : ∃ hu : formEmbedding (coreForm F) ∈ laplacian.domain,
      laplacian ⟨formEmbedding (coreForm F), hu⟩ = value G :=
    ⟨hu, by simpa only [zero_smul, sub_zero] using hA⟩
  simpa only [formEmbedding_coreForm] using hout

end GapFamily.Analytic.PoincareGreen
