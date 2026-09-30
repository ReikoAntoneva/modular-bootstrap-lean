import GapFamily.Analytic.Poincare.Seed.PoincareSeriesPointwise
import GapFamily.Analytic.Poincare.Continuation.PoincareComplementCutoffResidual
import GapFamily.Analytic.Modular.ModularLaplacianInvariant
import GapFamily.Analytic.Poincare.Continuation.PoincareComplementCore

/-! The actual complementary cusp series has its global ordinary equation. -/
noncomputable section
namespace GapFamily.Analytic.PoincareComplement
open Set MeasureTheory UpperHalfPlane LaplacianCovariance PoincareWeak
open scoped ContDiff MatrixGroups

/-- On the actual closed fundamental domain the open-strip germ and exact cutoff
commutator give the ordinary complement equation. -/
theorem ordinaryHyperbolicLaplacian_series_of_mem_fd (J : ℤ) {s : ℂ}
    (hs : 1 < s.re) {τ : UpperHalfPlane} (hτ : τ ∈ ModularGroup.fd) :
    ordinaryHyperbolicLaplacian (fun z : ℂ => series J s (ofComplex z)) τ =
      (2 * (Real.pi : ℂ) * (J : ℂ)) ^ 2 * series J (s + 2) τ +
        (CuspFourierCutoff.forcingCore J (s - 1 / 2)).val τ +
        s * (1 - s) * series J s τ := by
  have hheight : (1 / 2 : ℝ) < τ.im := by
    have h := ModularGroup.three_le_four_mul_im_sq_of_mem_fd hτ
    nlinarith [τ.im_pos]
  have hshift : 1 < (s + 2).re := by norm_num [Complex.add_re]; linarith
  have hP : ContDiffAt ℝ 2
      (fun z : ℂ => complexPoincareSeries 0 J s (ofComplex z)) τ :=
    ((PoincareSeriesSmooth.contDiffOn_complexPoincareSeries J hs).contDiffAt
      (isOpen_upperHalfPlaneSet.mem_nhds τ.im_pos)).of_le (by norm_num)
  have hC := (contDiffAt_cutoffPointSeed J s τ).of_le (show (2 : ℕ∞ω) ≤ ∞ by norm_num)
  rw [ordinaryHyperbolicLaplacian_congr_germ
    (series_ofComplex_germ_residual_of_half_lt_im J hs hheight)]
  change ordinaryHyperbolicLaplacian
    ((fun z : ℂ => complexPoincareSeries 0 J s (ofComplex z)) -
      (fun z : ℂ => (CuspFourierCutoff.cutoff z.im : ℂ) *
        complexPointSeed 0 J s (ofComplex z))) τ = _
  rw [ordinaryHyperbolicLaplacian_sub hP hC,
    series_eq_residual_of_half_lt_im J hs hheight,
    series_eq_residual_of_half_lt_im J hshift hheight,
    CuspFourierCutoff.forcingCore_eq_on_fd J (s - 1 / 2) hτ]
  have hraw := ordinaryHyperbolicLaplacian_complexPoincareSeries_zero J hs τ
  have hcut := ordinaryHyperbolicLaplacian_cutoffPointSeed J s τ
  linear_combination hraw - hcut

/-- Genuine modular invariance transports the exact ordinary residual from the
closed fundamental domain to every point of the upper half-plane. -/
theorem ordinaryHyperbolicLaplacian_series (J : ℤ) {s : ℂ}
    (hs : 1 < s.re) (τ : UpperHalfPlane) :
    ordinaryHyperbolicLaplacian (fun z : ℂ => series J s (ofComplex z)) τ =
      (2 * (Real.pi : ℂ) * (J : ℂ)) ^ 2 * series J (s + 2) τ +
        (CuspFourierCutoff.forcingCore J (s - 1 / 2)).val τ +
        s * (1 - s) * series J s τ := by
  apply congrFun (eq_of_modularInvariant_eqOn_fd
    (fun τ => ordinaryHyperbolicLaplacian (fun z : ℂ => series J s (ofComplex z)) τ)
    (fun τ => (2 * (Real.pi : ℂ) * (J : ℂ)) ^ 2 * series J (s + 2) τ +
      (CuspFourierCutoff.forcingCore J (s - 1 / 2)).val τ +
      s * (1 - s) * series J s τ) ?_ ?_ ?_) τ
  · exact ordinaryHyperbolicLaplacian_modularInvariant (series J s)
      (fun γ τ => series_smul J s τ γ) (contDiffOn_series J hs)
  · intro γ w
    rw [series_smul, series_smul,
      (CuspFourierCutoff.forcingCore J (s - 1 / 2)).property.2.1 γ w]
  · intro w hw
    exact ordinaryHyperbolicLaplacian_series_of_mem_fd J hs hw

/-- The explicitly constructed finite-energy source core is the actual pointwise
Laplacian of the explicitly constructed complement core. -/
theorem smoothCore_laplacian_eq (J : ℤ) (s : ℂ) (hs : 2 < s.re)
    (τ : UpperHalfPlane) :
    ordinaryHyperbolicLaplacian (smoothCore J s hs).val τ =
      (laplacianSourceCore J s hs).val τ := by
  simpa only [smoothCore_val, laplacianSourceCore_val, ofComplex_apply] using
    ordinaryHyperbolicLaplacian_series J (show 1 < s.re by linarith) τ

/-- The compact-test identity for the actual core pair, with both sides ordinary
integrable functions of the ambient complex variable. -/
theorem smoothCore_weak_equation_integrable (J : ℤ) (s : ℂ) (hs : 2 < s.re)
    (ψ : ℂ → ℂ) (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    (hψU : tsupport ψ ⊆ upperHalfPlaneSet) :
    Integrable (fun z : ℂ => star (ordinaryHyperbolicLaplacian ψ z) *
      (smoothCore J s hs).val z / (z.im : ℂ)^2) ∧
    Integrable (fun z : ℂ => star (ψ z) *
      (laplacianSourceCore J s hs).val z / (z.im : ℂ)^2) := by
  have h := PoincareGreen.hyperbolic_green_test_integrable ψ hψ hc hψU
    (smoothCore J s hs).val (smoothCore J s hs).property.1
  refine ⟨h.1, h.2.congr ?_⟩
  filter_upwards [] with z
  by_cases hz : z ∈ tsupport ψ
  · rw [smoothCore_laplacian_eq J s hs (⟨z, hψU hz⟩ : UpperHalfPlane)]
  · simp only [image_eq_zero_of_notMem_tsupport hz, star_zero, zero_mul, zero_div]

/-- The actual complementary core satisfies the ordinary compact-upper-test weak equation.
No operator-domain or differentiability assumption on an infinite sum occurs here. -/
theorem smoothCore_weak_equation (J : ℤ) (s : ℂ) (hs : 2 < s.re)
    (ψ : ℂ → ℂ) (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    (hψU : tsupport ψ ⊆ upperHalfPlaneSet) :
    (∫ z : ℂ, star (ordinaryHyperbolicLaplacian ψ z) *
      (smoothCore J s hs).val z / (z.im : ℂ)^2) =
      ∫ z : ℂ, star (ψ z) * (laplacianSourceCore J s hs).val z / (z.im : ℂ)^2 := by
  rw [PoincareGreen.integral_hyperbolic_green_test ψ hψ hc hψU
    (smoothCore J s hs).val (smoothCore J s hs).property.1]
  apply integral_congr_ae
  filter_upwards [] with z
  by_cases hz : z ∈ tsupport ψ
  · rw [smoothCore_laplacian_eq J s hs (⟨z, hψU hz⟩ : UpperHalfPlane)]
  · simp only [image_eq_zero_of_notMem_tsupport hz, star_zero, zero_mul, zero_div]

end GapFamily.Analytic.PoincareComplement
