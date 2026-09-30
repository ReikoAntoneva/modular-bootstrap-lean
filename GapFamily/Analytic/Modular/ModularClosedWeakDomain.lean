import GapFamily.Analytic.Modular.ModularCompactCorePeriodization
import GapFamily.Analytic.Modular.ModularFormTruncation
import GapFamily.Analytic.Cusp.Schur.CuspSchurOperatorBridge

/-!
# Compact energy tests determine the actual completed modular operator

The unknown is an arbitrary element of the genuine completed form domain and
the right-hand side is an arbitrary modular Hilbert vector. Finite-height core
approximation and compact periodization extend the tested energy equality to
the entire form domain, giving the literal existing Laplacian's domain/value.
-/

noncomputable section
namespace GapFamily.Analytic.ModularClosedWeakDomain
open Set Filter MeasureTheory UpperHalfPlane ModularGradient
open scoped ContDiff Topology

/-- Compact periodized tests determine the full actual closed energy pairing. -/
theorem form_pairing_of_periodized_pairing (u : FormDomain) (G : ModularHilbert)
    (hweak : ∀ (ψ : ℂ → ℂ) (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
      (hs : tsupport ψ ⊆ upperHalfPlaneSet),
      inner ℂ (coreGradient (periodizedUpperCore ψ hψ hc hs)) (formGradient u) =
        inner ℂ (value (periodizedUpperCore ψ hψ hc hs)) G)
    (t : FormDomain) :
    inner ℂ (formGradient t) (formGradient u) = inner ℂ (formEmbedding t) G := by
  have hfinite (Q : smoothCore) (H : ℝ)
      (hzero : ∀ τ : UpperHalfPlane, τ ∈ ModularGroup.fd → H < τ.im → Q.val τ = 0) :
      inner ℂ (formGradient (coreForm Q)) (formGradient u) =
        inner ℂ (formEmbedding (coreForm Q)) G := by
    obtain ⟨ψ, hψ, hc, hs, heq⟩ :=
      exists_periodizedUpperCore_coreForm_eq_of_cusp_zero Q H hzero
    rw [← heq, formGradient_coreForm, formEmbedding_coreForm]
    exact hweak ψ hψ hc hs
  have hclosed : IsClosed {v : FormDomain |
      inner ℂ (formGradient v) (formGradient u) = inner ℂ (formEmbedding v) G} :=
    isClosed_eq (formGradient.continuous.inner continuous_const)
      (formEmbedding.continuous.inner continuous_const)
  have hcore (Q : smoothCore) : coreForm Q ∈ {v : FormDomain |
      inner ℂ (formGradient v) (formGradient u) = inner ℂ (formEmbedding v) G} := by
    obtain ⟨Qn, hQn, hlim⟩ := FormTruncation.exists_finiteHeight_core_approximation Q
    apply hclosed.mem_of_tendsto hlim
    apply Eventually.of_forall
    intro n
    obtain ⟨H, hH⟩ := hQn n
    exact hfinite (Qn n) H hH
  exact coreForm_denseRange.induction_on t hclosed hcore

/-- The compact-tested completed form belongs to the literal modular Laplacian
domain, and its actual operator value is the supplied Hilbert right-hand side. -/
theorem exists_laplacian_value_of_periodized_pairing
    (u : FormDomain) (G : ModularHilbert)
    (hweak : ∀ (ψ : ℂ → ℂ) (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
      (hs : tsupport ψ ⊆ upperHalfPlaneSet),
      inner ℂ (coreGradient (periodizedUpperCore ψ hψ hc hs)) (formGradient u) =
        inner ℂ (value (periodizedUpperCore ψ hψ hc hs)) G) :
    ∃ hu : formEmbedding u ∈ laplacian.domain,
      laplacian ⟨formEmbedding u, hu⟩ = G := by
  have hform : ∀ t : FormDomain, CuspSchur.formPairing 0 t u =
      inner ℂ (formEmbedding t) G := by
    intro t
    simpa only [CuspSchur.formPairing, zero_mul, sub_zero] using
      form_pairing_of_periodized_pairing u G hweak t
  refine ⟨CuspSchur.formEmbedding_mem_laplacian_domain_of_formPairing 0 u G hform, ?_⟩
  simpa only [zero_smul, sub_zero] using
    CuspSchur.laplacian_sub_smul_of_formPairing 0 u G hform

end GapFamily.Analytic.ModularClosedWeakDomain
