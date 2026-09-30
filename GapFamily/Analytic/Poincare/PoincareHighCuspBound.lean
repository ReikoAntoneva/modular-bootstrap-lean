import GapFamily.Analytic.Poincare.PoincareHighCuspLift

/-! A uniform compact bound for the actual high-cusp lift, independent of spin. -/
noncomputable section
namespace GapFamily.Analytic.PoincareHighCusp
open Set UpperHalfPlane CuspFourierCutoff
open scoped Topology MatrixGroups

/-- The Fourier phase has norm one; the small parameter disk leaves an
exponent between zero and one, so the high-cusp value is at most 1+y. -/
theorem norm_continuedHighCusp_le_of_mem_fd (J : ℤ) {κ : ℂ} (hκ : ‖κ‖ ≤ 1 / 8)
    {τ : UpperHalfPlane} (hτ : τ ∈ ModularGroup.fd) :
    ‖continuedHighCusp J κ τ‖ ≤ 1 + τ.im := by
  have hre : |κ.re| ≤ 1 / 8 := (Complex.abs_re_le_norm κ).trans hκ
  have hexp : (exponent κ).re = 1 / 2 + κ.re := by norm_num [exponent, Complex.add_re]
  have ha : 0 ≤ (exponent κ).re := by
    rw [hexp]
    linarith [(abs_le.mp hre).1]
  have hb : (exponent κ).re ≤ 1 := by
    rw [hexp]
    linarith [(abs_le.mp hre).2]
  rw [continuedHighCusp_eq_on_fd J κ hτ, complexPointSeed_zero_eq_cuspFourierMode,
    norm_mul, norm_mul, norm_cuspFourierMode, mul_one,
    Complex.norm_cpow_eq_rpow_re_of_pos τ.im_pos, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (show 0 ≤ cutoff τ.im from Real.smoothTransition.nonneg (τ.im - 2))]
  calc
    _ ≤ τ.im ^ (exponent κ).re := by
      simpa only [cutoff, one_mul] using mul_le_mul_of_nonneg_right
        (Real.smoothTransition.le_one (τ.im - 2)) (Real.rpow_nonneg τ.im_pos.le _)
    _ ≤ 1 + τ.im := by
      simpa only [Real.rpow_zero, Real.rpow_one] using
        (rpow_le_add_endpoint τ.im_pos ha hb)

/-- One constant bounds the actual global lift on a compact upper set for all
integer spins and every parameter in the closed radius-one-eighth disk. -/
theorem exists_compact_continuedHighCusp_bound {K : Set UpperHalfPlane} (hK : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧ ∀ (J : ℤ) (κ : ℂ), ‖κ‖ ≤ 1 / 8 →
      ∀ τ : UpperHalfPlane, τ ∈ K → ‖continuedHighCusp J κ τ‖ ≤ C := by
  obtain ⟨M, hM⟩ := exists_bound_modular_smul_im_of_isCompact hK
  refine ⟨1 + |M|, by positivity, ?_⟩
  intro J κ hκ τ hτ
  obtain ⟨γ, hγ⟩ := ModularGroup.exists_smul_mem_fd τ
  rw [← continuedHighCusp_smul J κ τ γ]
  apply (norm_continuedHighCusp_le_of_mem_fd J hκ hγ).trans
  linarith [hM τ hτ γ, le_abs_self M]

/-- Restriction of the actual smooth global lift to any upper-half-plane target. -/
def continuedHighCuspOn (K : Set UpperHalfPlane) (J : ℤ) (κ : ℂ) : C(K, ℂ) :=
  ⟨fun τ => continuedHighCusp J κ τ.val,
    ((contDiffOn_continuedHighCusp J κ).continuousOn.comp_continuous
      UpperHalfPlane.continuous_coe (fun τ => τ.im_pos)).comp continuous_subtype_val⟩

@[simp] theorem continuedHighCuspOn_apply (K : Set UpperHalfPlane) (J : ℤ) (κ : ℂ) (τ : K) :
    continuedHighCuspOn K J κ τ = continuedHighCusp J κ τ.val := rfl

/-- The same actual restriction is uniformly bounded in C(K), independently of spin. -/
theorem exists_continuedHighCuspOn_norm_bound (K : Set UpperHalfPlane) [CompactSpace K] :
    ∃ C : ℝ, 0 < C ∧ ∀ (J : ℤ) (κ : ℂ), ‖κ‖ ≤ 1 / 8 →
      ‖continuedHighCuspOn K J κ‖ ≤ C := by
  obtain ⟨C, hC, hb⟩ := exists_compact_continuedHighCusp_bound
    (isCompact_iff_compactSpace.mpr inferInstance : IsCompact K)
  refine ⟨C, hC, ?_⟩
  intro J κ hκ
  apply (ContinuousMap.norm_le _ hC.le).mpr
  intro τ
  exact hb J κ hκ τ.val τ.property

end GapFamily.Analytic.PoincareHighCusp
