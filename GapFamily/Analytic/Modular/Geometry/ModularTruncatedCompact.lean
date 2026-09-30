import GapFamily.Analytic.Modular.Geometry.ModularTruncatedForm
import GapFamily.Analytic.Modular.Geometry.ModularTruncatedCutoff
import GapFamily.Analytic.Modular.Geometry.ModularTruncatedTransport
import GapFamily.Analytic.Modular.Elliptic.ModularInteriorCompactUpper

/-!
# Compactness of the actual bounded-height modular restriction

A genuine smooth cutoff equals one on the compact truncated closed fundamental
domain. Its proved compact Euclidean cutoff operator, followed by the actual
bounded modular measure transport, agrees with literal height truncation on
the dense smooth graph core. Continuity gives equality on the completed form
domain and hence compactness of the actual indicator restriction.
-/

noncomputable section

namespace GapFamily.Analytic.ModularGradient

open Set MeasureTheory UpperHalfPlane
open scoped ContDiff

/-- On the actual smooth graph core the transported cutoff is the literal
bounded-height restriction, because its cutoff equals one on the target. -/
theorem modularTruncatedTransport_upperCutoffOperator_coreForm
    (H : ℝ) (χ : ℂ → ℂ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ upperHalfPlaneSet)
    (hone : EqOn χ 1 (modularTruncatedTarget H)) (F : smoothCore) :
    modularTruncatedTransport H
        (upperCutoffOperator χ hχ hc hs (modularTruncatedTarget H) (coreForm F)) =
      modularLowCut H (value F) := by
  rw [upperCutoffOperator_coreForm]
  change modularTruncatedTransport H
      (LocalSobolev.restrictedLp (modularTruncatedTarget H)
        (fun z => χ z * F.val z) (upperCutoff_contDiff hχ hs F).continuous) = _
  apply Lp.ext
  filter_upwards [modularTruncatedTransport_restrictedLp_ae H
      (fun z => χ z * F.val z) (upperCutoff_contDiff hχ hs F).continuous,
    modularLowCut_ae H (value F), value_ae F, ae_mem_fdo] with τ ht hl hv hfd
  rw [ht, hl]
  by_cases hτ : τ.im ≤ H
  · have htarget : (τ : ℂ) ∈ modularTruncatedTarget H :=
      ⟨τ, ⟨ModularGroup.fdo_subset_fd hfd, hτ⟩, rfl⟩
    have hχone : χ τ = 1 := by simpa only [Pi.one_apply] using hone htarget
    simp [hτ, hχone, hv]
  · simp [hτ]

/-- Equality with actual cutoff and coordinate transport holds on the complete
form domain, derived from equality on its proved dense smooth graph core. -/
theorem truncatedFormEmbedding_eq_cutoffTransport
    (H : ℝ) (χ : ℂ → ℂ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ upperHalfPlaneSet)
    (hone : EqOn χ 1 (modularTruncatedTarget H)) :
    truncatedFormEmbedding H = (modularTruncatedTransport H).comp
      (upperCutoffOperator χ hχ hc hs (modularTruncatedTarget H)) := by
  apply DFunLike.coe_injective
  apply coreForm_denseRange.equalizer (truncatedFormEmbedding H).continuous
    ((modularTruncatedTransport H).comp
      (upperCutoffOperator χ hχ hc hs (modularTruncatedTarget H))).continuous
  funext F
  change modularLowCut H (value F) = modularTruncatedTransport H
    (upperCutoffOperator χ hχ hc hs (modularTruncatedTarget H) (coreForm F))
  exact (modularTruncatedTransport_upperCutoffOperator_coreForm H χ hχ hc hs hone F).symm

/-- Literal restriction to heights at most H, extended by zero in the actual
modular Hilbert space, is compact on the completed modular form domain. -/
theorem isCompactOperator_truncatedFormEmbedding (H : ℝ) :
    IsCompactOperator (truncatedFormEmbedding H) := by
  obtain ⟨χ, hχ, hc, hs, hone⟩ := exists_upperCutoff_eq_one
    (isCompact_modularTruncatedTarget H) (modularTruncatedTarget_subset_upperHalfPlane H)
  rw [truncatedFormEmbedding_eq_cutoffTransport H χ hχ hc hs hone]
  exact (isCompactOperator_upperCutoffOperator χ hχ hc hs
    (modularTruncatedTarget H)).clm_comp (modularTruncatedTransport H)

/-- Every graph-norm bounded ball has relatively compact actual bounded-height
restriction in the literal modular Hilbert space. -/
theorem truncatedFormEmbedding_isCompact_closure_image_closedBall (H R : ℝ) :
    IsCompact (closure ((truncatedFormEmbedding H) '' Metric.closedBall 0 R)) :=
  (isCompactOperator_truncatedFormEmbedding H).isCompact_closure_image_closedBall R

end GapFamily.Analytic.ModularGradient
