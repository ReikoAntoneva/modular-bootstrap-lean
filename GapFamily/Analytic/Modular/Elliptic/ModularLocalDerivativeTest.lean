import GapFamily.Analytic.Modular.Elliptic.ModularUpperCutoffGradient

noncomputable section
namespace GapFamily.Analytic
open Set Filter MeasureTheory UpperHalfPlane ModularGradient
open scoped ContDiff Topology

/-- The ordinary derivative of a smooth compact test belongs to actual global Euclidean L². -/
theorem upperTestDerivative_memLp (ψ : ℂ → ℂ) (hψ : ContDiff ℝ ∞ ψ)
    (hc : HasCompactSupport ψ) (v : ℂ) :
    MemLp (fun z => fderiv ℝ ψ z v) 2 (volume : Measure ℂ) :=
  ((hψ.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport
    (hc.fderiv_apply ℝ v)

/-- The literal ordinary derivative test class. -/
def upperTestDerivativeL2 (ψ : ℂ → ℂ) (hψ : ContDiff ℝ ∞ ψ)
    (hc : HasCompactSupport ψ) (v : ℂ) : Lp ℂ 2 (volume : Measure ℂ) :=
  (upperTestDerivative_memLp ψ hψ hc v).toLp (fun z => fderiv ℝ ψ z v)

theorem upperTestDerivativeL2_ae (ψ : ℂ → ℂ) (hψ : ContDiff ℝ ∞ ψ)
    (hc : HasCompactSupport ψ) (v : ℂ) :
    upperTestDerivativeL2 ψ hψ hc v =ᵐ[(volume : Measure ℂ)]
      (fun z => fderiv ℝ ψ z v) :=
  MemLp.coeFn_toLp (upperTestDerivative_memLp ψ hψ hc v)

/-- On the actual core, a cutoff equal to one on the test support disappears from the pairing. -/
theorem inner_upperCutoffGradient_core_test
    (χ : ℂ → ℂ) (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hsχ : tsupport χ ⊆ upperHalfPlaneSet) (F : smoothCore)
    (ψ : ℂ → ℂ) (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ)
    (hχone : ∀ z ∈ tsupport ψ, χ z = 1) (v : ℂ) :
    inner ℂ (upperCutoffGradientOperator χ hχ hcχ hsχ v (coreForm F))
      (upperTestDerivativeL2 ψ hψ hcψ v) =
      ∫ z : ℂ, star (fderiv ℝ F.val z v) * fderiv ℝ ψ z v := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [upperCutoffGradientOperator_coreForm_ae χ hχ hcχ hsχ v F,
    upperTestDerivativeL2_ae ψ hψ hcψ v] with z hF hψz
  rw [hF, hψz]
  by_cases hz : z ∈ tsupport ψ
  · simp [hχone z hz, RCLike.inner_apply, mul_comm]
  · simp [fderiv_of_notMem_tsupport ℝ hz]

/-- The uncut core/test density is ordinarily integrable because the cutoff is one on its support. -/
theorem upperCutoffGradient_core_test_integrable
    (χ : ℂ → ℂ) (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hsχ : tsupport χ ⊆ upperHalfPlaneSet) (F : smoothCore)
    (ψ : ℂ → ℂ) (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ)
    (hχone : ∀ z ∈ tsupport ψ, χ z = 1) (v : ℂ) :
    Integrable (fun z : ℂ => star (fderiv ℝ F.val z v) * fderiv ℝ ψ z v) volume := by
  apply (L2.integrable_inner (𝕜 := ℂ)
    (upperCutoffGradientOperator χ hχ hcχ hsχ v (coreForm F))
      (upperTestDerivativeL2 ψ hψ hcψ v)).congr
  filter_upwards [upperCutoffGradientOperator_coreForm_ae χ hχ hcχ hsχ v F,
    upperTestDerivativeL2_ae ψ hψ hcψ v] with z hF hψz
  rw [hF, hψz]
  by_cases hz : z ∈ tsupport ψ
  · simp [hχone z hz, RCLike.inner_apply, mul_comm]
  · simp [fderiv_of_notMem_tsupport ℝ hz]

/-- Every completed local field pairs ordinarily with the actual test derivative. -/
theorem upperCutoffGradient_test_integrable
    (χ : ℂ → ℂ) (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hsχ : tsupport χ ⊆ upperHalfPlaneSet) (u : FormDomain)
    (ψ : ℂ → ℂ) (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ) (v : ℂ) :
    Integrable (fun z : ℂ => star (fderiv ℝ ψ z v) *
      upperCutoffGradientOperator χ hχ hcχ hsχ v u z) volume := by
  apply (L2.integrable_inner (𝕜 := ℂ) (upperTestDerivativeL2 ψ hψ hcψ v)
    (upperCutoffGradientOperator χ hχ hcχ hsχ v u)).congr
  filter_upwards [upperTestDerivativeL2_ae ψ hψ hcψ v] with z hz
  simp [hz, RCLike.inner_apply, mul_comm]

/-- The completed-field Hilbert pairing is its literal ordinary integral. -/
theorem inner_test_upperCutoffGradient_integral
    (χ : ℂ → ℂ) (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hsχ : tsupport χ ⊆ upperHalfPlaneSet) (u : FormDomain)
    (ψ : ℂ → ℂ) (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ) (v : ℂ) :
    inner ℂ (upperTestDerivativeL2 ψ hψ hcψ v)
      (upperCutoffGradientOperator χ hχ hcχ hsχ v u) =
      ∫ z : ℂ, star (fderiv ℝ ψ z v) * upperCutoffGradientOperator χ hχ hcχ hsχ v u z := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [upperTestDerivativeL2_ae ψ hψ hcψ v] with z hz
  simp [hz, RCLike.inner_apply, mul_comm]

end GapFamily.Analytic
