import GapFamily.Analytic.Modular.Periodization.ModularPeriodizationLocal
import GapFamily.Analytic.Modular.Periodization.ModularPeriodizationAction

/-!
# Smooth modular periodization
The actual full matrix-group sum is normalized by one half, since the two central matrices act identically. Compact interior support makes the sum locally finite.
-/
noncomputable section
namespace GapFamily.Analytic
open Set Filter UpperHalfPlane
open scoped ContDiff MatrixGroups Topology

def modularPeriodization (φ : ℂ → ℂ) (z : ℂ) : ℂ :=
  (1 / 2 : ℂ) * ∑' γ : SL(2, ℤ), φ (rawModularAction γ z)

theorem modularPeriodization_coe (φ : ℂ → ℂ) (τ : UpperHalfPlane) :
    modularPeriodization φ τ =
      (1 / 2 : ℂ) * ∑' γ : SL(2, ℤ), φ (↑(γ • τ : UpperHalfPlane) : ℂ) := by
  simp only [modularPeriodization, rawModularAction_coe]

theorem modularPeriodization_invariant (φ : ℂ → ℂ) (δ : SL(2, ℤ))
    (τ : UpperHalfPlane) :
    modularPeriodization φ (↑(δ • τ : UpperHalfPlane) : ℂ) =
      modularPeriodization φ τ := by
  simp only [modularPeriodization_coe]
  congr 1
  simpa only [Equiv.coe_mulRight, mul_smul] using
    (Equiv.mulRight δ).tsum_eq (fun γ : SL(2, ℤ) => φ (↑(γ • τ : UpperHalfPlane) : ℂ))

private theorem modular_one_ne_neg_one : (1 : SL(2, ℤ)) ≠ -1 := by
  intro h
  have hentry := congrArg (fun γ : SL(2, ℤ) => γ 0 0) h
  norm_num at hentry

theorem modular_summand_eq_zero {φ : ℂ → ℂ}
    (hs : tsupport φ ⊆ modularInterior) {τ : UpperHalfPlane}
    (hτ : τ ∈ ModularGroup.fd) {γ : SL(2, ℤ)} (hγ : γ ≠ 1) (hγ' : γ ≠ -1) :
    φ (↑(γ • τ : UpperHalfPlane) : ℂ) = 0 := by
  by_contra hne
  have hmem : γ • τ ∈ ModularGroup.fdo := by
    obtain ⟨τ', hτ', heq⟩ := hs (subset_tsupport φ hne)
    exact UpperHalfPlane.coe_injective heq ▸ hτ'
  have hi := ModularGroup.eq_one_or_neg_one_of_mem_fdo_mem_fd hmem
    (show γ⁻¹ • (γ • τ) ∈ ModularGroup.fd by simpa using hτ)
  rcases hi with hi | hi
  · exact hγ (by simpa only [inv_eq_one] using hi)
  · apply hγ'
    have := congrArg Inv.inv hi
    simpa using this

theorem modularPeriodization_eq_on_fd {φ : ℂ → ℂ}
    (hs : tsupport φ ⊆ modularInterior) {τ : UpperHalfPlane}
    (hτ : τ ∈ ModularGroup.fd) : modularPeriodization φ τ = φ τ := by
  classical
  rw [modularPeriodization_coe, tsum_eq_sum (s := {1, -1})]
  · simp only [Finset.sum_pair modular_one_ne_neg_one, one_smul,
      ModularGroup.SL_neg_smul]
    ring
  · intro γ hγ
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hγ
    exact modular_summand_eq_zero hs hτ hγ.1 hγ.2

theorem modularPeriodization_eqOn_interior {φ : ℂ → ℂ}
    (hs : tsupport φ ⊆ modularInterior) :
    EqOn (modularPeriodization φ) φ modularInterior := by
  rintro z ⟨τ, hτ, rfl⟩
  exact modularPeriodization_eq_on_fd hs (ModularGroup.fdo_subset_fd hτ)

theorem modularPeriodization_eventually_finset {φ : ℂ → ℂ}
    (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ modularInterior)
    {z : ℂ} (hz : z ∈ upperHalfPlaneSet) :
    ∃ s : Finset SL(2, ℤ), modularPeriodization φ =ᶠ[𝓝 z]
      fun w => (1 / 2 : ℂ) * ∑ γ ∈ s, φ (rawModularAction γ w) := by
  classical
  let τ : UpperHalfPlane := ⟨z, hz⟩
  obtain ⟨s, hsfin⟩ := (locallyFinite_modular_orbit_support hc hs).exists_finset_support τ
  obtain ⟨V, hVsub, hVopen, hVτ⟩ := mem_nhds_iff.mp hsfin
  refine ⟨s, ?_⟩
  have hW : UpperHalfPlane.coe '' V ∈ 𝓝 z :=
    (UpperHalfPlane.isOpenEmbedding_coe.isOpenMap V hVopen).mem_nhds ⟨τ, hVτ, rfl⟩
  filter_upwards [hW] with w hw
  obtain ⟨τ', hτ', rfl⟩ := hw
  simp only [modularPeriodization, rawModularAction_coe]
  congr 1
  apply tsum_eq_sum
  intro γ hγ
  by_contra hne
  exact hγ (hVsub hτ' hne)

theorem contDiffOn_modularPeriodization {φ : ℂ → ℂ}
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ modularInterior) :
    ContDiffOn ℝ ∞ (modularPeriodization φ) upperHalfPlaneSet := by
  intro z hz
  obtain ⟨s, heq⟩ := modularPeriodization_eventually_finset hc hs hz
  have hsum : ContDiffOn ℝ ∞
      (fun w => (1 / 2 : ℂ) * ∑ γ ∈ s, φ (rawModularAction γ w)) upperHalfPlaneSet :=
    contDiffOn_const.mul (ContDiffOn.sum fun γ _ =>
      hφ.contDiffOn.comp (contDiffOn_rawModularAction γ)
        (fun _ _ => Set.mem_univ _))
  exact ((hsum z hz).contDiffAt (isOpen_upperHalfPlaneSet.mem_nhds hz)).congr_of_eventuallyEq
    heq |>.contDiffWithinAt

end GapFamily.Analytic
