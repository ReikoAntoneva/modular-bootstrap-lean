import GapFamily.Analytic.Modular.Periodization.ModularPeriodizationUpper

/-! Literal smooth invariant functions vanishing above a finite modular height are in the core. -/
noncomputable section
namespace GapFamily.Analytic.FormTruncation
open Set Filter MeasureTheory UpperHalfPlane ModularGradient
open scoped ContDiff MatrixGroups Topology

/-- A globally specified invariant function, smooth on the upper half-plane
and zero above a finite height on the fundamental domain, has finite actual
value and frame-gradient norms. -/
theorem mem_smoothCore_of_finite_height {G : ℂ → ℂ}
    (hG : ContDiffOn ℝ ∞ G upperHalfPlaneSet)
    (hinv : ∀ γ : SL(2, ℤ), ∀ τ : UpperHalfPlane, G (γ • τ : UpperHalfPlane) = G τ)
    (H : ℝ) (hzero : ∀ τ ∈ ModularGroup.fd, H < τ.im → G τ = 0) :
    G ∈ smoothCore := by
  obtain ⟨χ, hχ, hχc, hχs, hχone⟩ := exists_upperCutoff_eq_one
    (isCompact_modularTruncatedTarget H) (modularTruncatedTarget_subset_upperHalfPlane H)
  let g : ℂ → ℂ := fun z => χ z * G z
  have hg : ContDiff ℝ ∞ g := by
    rw [contDiff_iff_contDiffAt]
    intro z
    by_cases hz : z ∈ tsupport χ
    · exact hχ.contDiffAt.mul (hG.contDiffAt
        (isOpen_upperHalfPlaneSet.mem_nhds (hχs hz)))
    · apply (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hz] with w hw
      simp [g, hw]
  have hgc : HasCompactSupport g := hχc.mul_right
  have hae : (fun τ : UpperHalfPlane => G τ) =ᵐ[modularMeasure]
      (fun τ : UpperHalfPlane => g τ) := by
    filter_upwards [ae_mem_fdo] with τ hτ
    by_cases hh : τ.im ≤ H
    · have hone : χ τ = 1 := hχone ((coe_mem_modularTruncatedTarget_iff H τ).mpr
        ⟨ModularGroup.fdo_subset_fd hτ, hh⟩)
      simp only [g, hone, one_mul]
    · simp only [g, hzero τ (ModularGroup.fdo_subset_fd hτ) (lt_of_not_ge hh), mul_zero]
  have hdir (v : ℂ) : directional G v =ᵐ[modularMeasure] directional g v :=
    modularDirectional_ae_eq
      (hG.continuousOn.mono (fun _ hz => im_pos_of_mem_modularInterior hz))
      hg.continuous.continuousOn hae v
  refine ⟨hG, hinv, ?_, ?_, ?_⟩
  · exact (memLp_congr_ae hae).mpr (memLp_test_value g hg.continuous hgc)
  · exact (memLp_congr_ae (hdir 1)).mpr (memLp_test_directional g hg hgc 1)
  · exact (memLp_congr_ae (hdir Complex.I)).mpr
      (memLp_test_directional g hg hgc Complex.I)

end GapFamily.Analytic.FormTruncation
