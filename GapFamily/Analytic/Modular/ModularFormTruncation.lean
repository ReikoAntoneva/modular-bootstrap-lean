import GapFamily.Analytic.Modular.ModularFormTruncationLp
import GapFamily.Analytic.Modular.Elliptic.ModularInteriorCompactCore

/-! Actual finite-height smooth-core approximation in the modular form norm. -/
noncomputable section
namespace GapFamily.Analytic.FormTruncation
open Set Filter MeasureTheory UpperHalfPlane ModularGradient
open scoped Topology

/-- Both actual truncated frame components converge in the Hilbert sum norm. -/
theorem coreGradient_truncatedCore_tendsto (F : smoothCore) :
    Tendsto (fun n => coreGradient (truncatedCore n F)) atTop (𝓝 (coreGradient F)) := by
  have hp := (xComponent_truncatedCore_tendsto F).prodMk_nhds
    (yComponent_truncatedCore_tendsto F)
  have ht := (WithLp.prodContinuousLinearEquiv 2 ℂ ModularHilbert ModularHilbert).symm.continuous
    |>.continuousAt.tendsto |>.comp hp
  exact ht

private theorem coreForm_val (F : smoothCore) :
    (coreForm F).val = WithLp.toLp 2 (value F, coreGradient F) := by
  change WithLp.toLp 2 (value F, closedGradient ⟨value F, _⟩) = _
  rw [closedGradient_apply_value]

/-- The explicit invariant cutoffs converge in the actual mass-plus-energy norm. -/
theorem coreForm_truncatedCore_tendsto (F : smoothCore) :
    Tendsto (fun n => coreForm (truncatedCore n F)) atTop (𝓝 (coreForm F)) := by
  have hp := (value_truncatedCore_tendsto F).prodMk_nhds
    (coreGradient_truncatedCore_tendsto F)
  have ht := (WithLp.prodContinuousLinearEquiv 2 ℂ ModularHilbert GradientSpace).symm.continuous
    |>.continuousAt.tendsto |>.comp hp
  change Tendsto (fun n => WithLp.toLp 2
    (value (truncatedCore n F), coreGradient (truncatedCore n F))) atTop
    (𝓝 (WithLp.toLp 2 (value F, coreGradient F))) at ht
  apply tendsto_subtype_rng.mpr
  simpa only [coreForm_val] using ht

/-- Every smooth automorphic finite-energy function has explicit finite-height
smooth approximants, with convergence in the completed form domain. -/
theorem exists_finiteHeight_core_approximation (F : smoothCore) :
    ∃ Fn : ℕ → smoothCore,
      (∀ n, ∃ H : ℝ, ∀ τ : UpperHalfPlane, τ ∈ ModularGroup.fd →
        H < τ.im → (Fn n).val τ = 0) ∧
      Tendsto (fun n => coreForm (Fn n)) atTop (𝓝 (coreForm F)) := by
  refine ⟨fun n => truncatedCore n F, ?_, coreForm_truncatedCore_tendsto F⟩
  intro n
  exact ⟨2 * scale n, fun τ hτ ht => truncatedCore_zero_above n F τ hτ ht.le⟩

/-- Literal finite-height smooth-core values are dense in the actual completed
form domain. Their height bounds may depend on the approximation index. -/
theorem finiteHeightCoreForm_dense :
    Dense {u : FormDomain | ∃ F : smoothCore, ∃ H : ℝ,
      (∀ τ : UpperHalfPlane, τ ∈ ModularGroup.fd → H < τ.im → F.val τ = 0) ∧
      coreForm F = u} := by
  let S : Set FormDomain := {u | ∃ F : smoothCore, ∃ H : ℝ,
    (∀ τ : UpperHalfPlane, τ ∈ ModularGroup.fd → H < τ.im → F.val τ = 0) ∧ coreForm F = u}
  have hsub : Set.range coreForm ⊆ closure S := by
    rintro u ⟨F, rfl⟩
    apply mem_closure_of_tendsto (coreForm_truncatedCore_tendsto F)
    exact Eventually.of_forall fun n =>
      ⟨truncatedCore n F, 2 * scale n,
        (fun τ hτ ht => truncatedCore_zero_above n F τ hτ ht.le), rfl⟩
  intro u
  exact (closure_minimal hsub isClosed_closure) (coreForm_denseRange u)

/-- An actual finite-height smooth approximation sequence for every completed
form-domain vector, with no supplied density or cutoff-sequence witness. -/
theorem exists_finiteHeight_coreForm_tendsto (u : FormDomain) :
    ∃ Fn : ℕ → smoothCore,
      (∀ n, ∃ H : ℝ, ∀ τ : UpperHalfPlane, τ ∈ ModularGroup.fd →
        H < τ.im → (Fn n).val τ = 0) ∧
      Tendsto (fun n => coreForm (Fn n)) atTop (𝓝 u) := by
  obtain ⟨p, hp, ht⟩ := mem_closure_iff_seq_limit.mp (finiteHeightCoreForm_dense u)
  choose F H hzero heq using hp
  refine ⟨F, fun n => ⟨H n, hzero n⟩, ?_⟩
  simpa only [heq] using ht

end GapFamily.Analytic.FormTruncation
