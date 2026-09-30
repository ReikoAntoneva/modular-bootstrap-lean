import GapFamily.Analytic.Modular.Geometry.ModularCoordinate
import GapFamily.Analytic.Elliptic.LocalSobolevCompactRestriction

/-!
# The actual compact target for a truncated modular restriction

The source set is the complex image of the closed truncated fundamental
domain, including its seams. Its Euclidean `L²` measure is unnormalized area.
-/

noncomputable section

namespace GapFamily.Analytic.ModularGradient

open Set MeasureTheory UpperHalfPlane

def modularTruncatedTarget (H : ℝ) : Set ℂ :=
  UpperHalfPlane.coe '' ModularGroup.truncatedFundamentalDomain H

theorem isCompact_modularTruncatedTarget (H : ℝ) : IsCompact (modularTruncatedTarget H) :=
  (ModularGroup.isCompact_truncatedFundamentalDomain H).image UpperHalfPlane.continuous_coe

instance compactSpace_modularTruncatedTarget (H : ℝ) : CompactSpace (modularTruncatedTarget H) :=
  isCompact_iff_compactSpace.mp (isCompact_modularTruncatedTarget H)

theorem modularTruncatedTarget_subset_upperHalfPlane (H : ℝ) :
    modularTruncatedTarget H ⊆ upperHalfPlaneSet := by
  rintro z ⟨τ, hτ, rfl⟩
  exact τ.im_pos

@[simp] theorem coe_mem_modularTruncatedTarget_iff (H : ℝ) (τ : UpperHalfPlane) :
    (τ : ℂ) ∈ modularTruncatedTarget H ↔ τ ∈ ModularGroup.fd ∧ τ.im ≤ H := by
  constructor
  · rintro ⟨σ, hσ, hστ⟩
    have heq : σ = τ := UpperHalfPlane.coe_injective hστ
    simpa only [heq, ModularGroup.truncatedFundamentalDomain, mem_ofPred_eq] using hσ
  · intro hτ
    exact ⟨τ, hτ, rfl⟩

abbrev ModularTruncatedSource (H : ℝ) :=
  Lp ℂ 2 (LocalSobolev.restrictedVolume (modularTruncatedTarget H))

end GapFamily.Analytic.ModularGradient
