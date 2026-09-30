import GapFamily.Analytic.Poincare.PoincareResidualGradient
import GapFamily.Analytic.Poincare.Continuation.PoincareComplementStrip

/-! Square-integrable actual frame derivatives of the automorphic complement series. -/
noncomputable section
namespace GapFamily.Analytic.PoincareComplementGradient
open Set Filter MeasureTheory UpperHalfPlane ModularGradient PoincareSeedGradient
open scoped Topology

/-- Above height one half the actual automorphic complement and the actual
cutoff-subtracted series have the same ordinary germ. -/
theorem series_germ_residual (J : ℤ) {s : ℂ} (hs : 1 < s.re)
    {z : ℂ} (hz : 1 / 2 < z.im) :
    (fun w : ℂ => PoincareComplement.series J s (UpperHalfPlane.ofComplex w))
      =ᶠ[𝓝 z] residual J s := by
  have hpos : 0 < z.im := by linarith
  filter_upwards [PoincareComplement.series_ofComplex_germ_residual_of_half_lt_im J hs hz,
    isOpen_upperHalfPlaneSet.mem_nhds hpos] with w hw hy
  rw [hw, residual_eq_cutoff_subtraction]
  have hr : rawSeed J s w = complexPointSeed 0 J s (UpperHalfPlane.ofComplex w) := by
    simpa only [UpperHalfPlane.ofComplex_apply_of_im_pos hy] using
      rawSeed_eq_complexPointSeed J s (UpperHalfPlane.ofComplex w)
  rw [hr]

/-- The derivative identification is a germ theorem on the full FD, not a
consequence of equality merely on its closed set. -/
theorem fderiv_series_eq_residual_of_mem_fd (J : ℤ) {s : ℂ} (hs : 1 < s.re)
    {τ : UpperHalfPlane} (hτ : τ ∈ ModularGroup.fd) :
    fderiv ℝ (fun z : ℂ => PoincareComplement.series J s (UpperHalfPlane.ofComplex z)) (τ : ℂ) =
      fderiv ℝ (residual J s) (τ : ℂ) :=
  (series_germ_residual J hs (one_half_lt_im_of_mem_fd hτ)).fderiv_eq

/-- One finite bound controls every actual complement frame derivative on the closed FD. -/
theorem exists_series_frame_bound (J : ℤ) {s : ℂ} (hs : 2 < s.re) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (τ : UpperHalfPlane), τ ∈ ModularGroup.fd → ∀ v : ℂ,
      ‖directional
        (fun z : ℂ => PoincareComplement.series J s (UpperHalfPlane.ofComplex z)) v τ‖ ≤
          B * ‖v‖ := by
  obtain ⟨B, hB, hb⟩ := exists_residual_frame_bound J hs
  refine ⟨B, hB, ?_⟩
  intro τ hτ v
  simp only [directional, fderiv_series_eq_residual_of_mem_fd J (by linarith) hτ,
    norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos τ.im_pos]
  exact hb τ hτ v

/-- The actual derivative fields agree almost everywhere for the actual modular measure. -/
theorem directional_series_ae_residual (J : ℤ) {s : ℂ} (hs : 1 < s.re) (v : ℂ) :
    directional (fun z : ℂ => PoincareComplement.series J s (UpperHalfPlane.ofComplex z)) v
      =ᵐ[modularMeasure] directional (residual J s) v := by
  filter_upwards [ae_mem_fdo] with τ hτ
  simp only [directional, fderiv_series_eq_residual_of_mem_fd J hs
    (ModularGroup.fdo_subset_fd hτ)]

/-- Every actual hyperbolic frame derivative of the complementary automorphic
series is in modular L², with no regularity or gradient-bound premise supplied. -/
theorem directional_series_memLp (J : ℤ) {s : ℂ} (hs : 2 < s.re) (v : ℂ) :
    MemLp
      (directional (fun z : ℂ => PoincareComplement.series J s (UpperHalfPlane.ofComplex z)) v)
      2 modularMeasure :=
  (memLp_congr_ae (directional_series_ae_residual J (by linarith) v)).mpr
    (directional_residual_memLp J hs v)

/-- Both literal basis frame fields required for the smooth automorphic core. -/
theorem basis_directional_series_memLp (J : ℤ) {s : ℂ} (hs : 2 < s.re) :
    MemLp
      (directional (fun z : ℂ => PoincareComplement.series J s (UpperHalfPlane.ofComplex z)) 1)
      2 modularMeasure ∧
    MemLp
      (directional (fun z : ℂ => PoincareComplement.series J s (UpperHalfPlane.ofComplex z)) Complex.I)
      2 modularMeasure :=
  ⟨directional_series_memLp J hs 1, directional_series_memLp J hs Complex.I⟩

end GapFamily.Analytic.PoincareComplementGradient
