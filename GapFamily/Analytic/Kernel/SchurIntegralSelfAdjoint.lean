import GapFamily.Analytic.Kernel.SchurIntegralOperator
import GapFamily.Analytic.Kernel.SchurKernelPairing
import Mathlib.Analysis.InnerProductSpace.Adjoint

noncomputable section
namespace GapFamily.Analytic.SchurIntegralOperator
open MeasureTheory
open SchurKernelPairing
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [SFinite μ]
variable {K : X × X → ℂ} {C : ℝ}

/-- The actual Hilbert pairing is the ordinary pairing of the constructed integral. -/
theorem inner_integralOperator (h : KernelData μ K C) (f g : Lp ℂ 2 μ) :
    inner ℂ g (integralOperator h f) =
      ∫ x, star (g x) * (∫ y, K (x, y) * f y ∂μ) ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [integralOperator_ae h f] with x hx
  simp only [hx, RCLike.inner_apply]
  exact mul_comm _ _

/-- Hermitian symmetry of the actual kernel makes the constructed operator selfadjoint.
All raw row integrals and double pairings are ordinarily integrable by the Schur hypotheses. -/
theorem isSelfAdjoint_integralOperator (h : KernelData μ K C)
    (hHermitian : ∀ᵐ p ∂μ.prod μ, K p = star (K p.swap)) :
    IsSelfAdjoint (integralOperator h) := by
  have hp (f g : Lp ℂ 2 μ) := integrable_pairing h.measurable h.nonneg
    h.row_integrable h.row_bound h.column_integrable h.column_bound f g
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro f g
  change inner ℂ (integralOperator h f) g = inner ℂ f (integralOperator h g)
  rw [← inner_conj_symm, inner_integralOperator, inner_integralOperator]
  have he := congrArg star (pairing_hermitian hHermitian f g (hp f g) (hp g f))
  simpa only [star_star, starRingEnd_apply] using he

end GapFamily.Analytic.SchurIntegralOperator
