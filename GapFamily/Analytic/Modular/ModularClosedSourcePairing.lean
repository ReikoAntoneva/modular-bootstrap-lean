import GapFamily.Analytic.Modular.Elliptic.ModularUpperHilbertValue
import GapFamily.Analytic.Modular.Periodization.ModularPeriodizationValueEuclidean

/-! Ordinary local source pairing for every actual modular Hilbert vector. -/
noncomputable section
namespace GapFamily.Analytic
open Set Filter MeasureTheory UpperHalfPlane ModularGradient
open scoped ContDiff Topology

/-- The compact test with the actual inverse height-square weight belongs to ordinary L². -/
theorem upperSourceTest_memLp (ψ : ℂ → ℂ) (hψ : ContDiff ℝ ∞ ψ)
    (hcψ : HasCompactSupport ψ) (hsψ : tsupport ψ ⊆ upperHalfPlaneSet) :
    MemLp (upperSourceTestFunction ψ) 2 (volume : Measure ℂ) :=
  (contDiff_upperSourceTestFunction hψ hsψ).continuous.memLp_of_hasCompactSupport
    (hasCompactSupport_upperSourceTestFunction hcψ)

/-- Literal Euclidean source-test class with the inverse height-square factor. -/
def upperSourceTestL2 (ψ : ℂ → ℂ) (hψ : ContDiff ℝ ∞ ψ)
    (hcψ : HasCompactSupport ψ) (hsψ : tsupport ψ ⊆ upperHalfPlaneSet) :
    Lp ℂ 2 (volume : Measure ℂ) :=
  (upperSourceTest_memLp ψ hψ hcψ hsψ).toLp (upperSourceTestFunction ψ)

theorem upperSourceTestL2_ae (ψ : ℂ → ℂ) (hψ : ContDiff ℝ ∞ ψ)
    (hcψ : HasCompactSupport ψ) (hsψ : tsupport ψ ⊆ upperHalfPlaneSet) :
    upperSourceTestL2 ψ hψ hcψ hsψ =ᵐ[(volume : Measure ℂ)] upperSourceTestFunction ψ :=
  MemLp.coeFn_toLp (upperSourceTest_memLp ψ hψ hcψ hsψ)

/-- On genuine core values the weighted test sees literal cutoff multiplication. -/
theorem inner_upperSourceTest_core
    (χ : ℂ → ℂ) (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hsχ : tsupport χ ⊆ upperHalfPlaneSet) (F : smoothCore)
    (ψ : ℂ → ℂ) (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ)
    (hsψ : tsupport ψ ⊆ upperHalfPlaneSet) (hχone : ∀ z ∈ tsupport ψ, χ z = 1) :
    inner ℂ (upperSourceTestL2 ψ hψ hcψ hsψ)
      (upperCutoffHilbertValueOperator χ hχ hcχ hsχ (value F)) =
      ∫ z : ℂ, star (upperSourceTestFunction ψ z) * F.val z := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [upperSourceTestL2_ae ψ hψ hcψ hsψ,
    upperCutoffHilbertValueOperator_value_ae χ hχ hcχ hsχ F] with z hψz hF
  rw [hψz, hF]
  by_cases hz : z ∈ tsupport ψ
  · simp [hχone z hz, RCLike.inner_apply, mul_comm]
  · simp [upperSourceTestFunction, image_eq_zero_of_notMem_tsupport hz]

/-- Actual modular value density extends the test pairing to every Hilbert source. -/
theorem periodizedUpperCore_hilbert_source_pairing
    (χ : ℂ → ℂ) (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hsχ : tsupport χ ⊆ upperHalfPlaneSet)
    (ψ : ℂ → ℂ) (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ)
    (hsψ : tsupport ψ ⊆ upperHalfPlaneSet) (hχone : ∀ z ∈ tsupport ψ, χ z = 1)
    (f : ModularHilbert) :
    inner ℂ (value (periodizedUpperCore ψ hψ hcψ hsψ)) f =
      inner ℂ (upperSourceTestL2 ψ hψ hcψ hsψ)
        (upperCutoffHilbertValueOperator χ hχ hcχ hsχ f) := by
  have hd : DenseRange value := by
    simpa only [DenseRange, LinearMap.coe_range] using value_dense_range
  refine hd.induction_on f ?_ ?_
  · exact isClosed_eq (continuous_const.inner continuous_id)
      (continuous_const.inner (upperCutoffHilbertValueOperator χ hχ hcχ hsχ).continuous)
  · intro F
    rw [inner_upperSourceTest_core χ hχ hcχ hsχ F ψ hψ hcψ hsψ hχone]
    exact inner_periodizedUpperCore_value_eq_euclidean F hψ hcψ hsψ

/-- The literal ordinary source field uses the actual Hilbert lift, divided by y². -/
def upperCutoffSourceField
    (χ : ℂ → ℂ) (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hsχ : tsupport χ ⊆ upperHalfPlaneSet) (f : ModularHilbert) (z : ℂ) : ℂ :=
  upperCutoffHilbertValueOperator χ hχ hcχ hsχ f z / (z.im : ℂ) ^ 2

private theorem sourceTest_pairing_eq (ψ : ℂ → ℂ) (b : ℂ) (z : ℂ) :
    star (upperSourceTestFunction ψ z) * b = star (ψ z) * (b / (z.im : ℂ) ^ 2) := by
  simp [upperSourceTestFunction, div_eq_mul_inv, mul_assoc, mul_comm]

/-- The ordinary local source integral is genuinely convergent. -/
theorem upperCutoffSourceField_test_integrable
    (χ : ℂ → ℂ) (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hsχ : tsupport χ ⊆ upperHalfPlaneSet)
    (ψ : ℂ → ℂ) (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ)
    (hsψ : tsupport ψ ⊆ upperHalfPlaneSet) (f : ModularHilbert) :
    Integrable (fun z : ℂ => star (ψ z) * upperCutoffSourceField χ hχ hcχ hsχ f z) volume := by
  apply (L2.integrable_inner (𝕜 := ℂ) (upperSourceTestL2 ψ hψ hcψ hsψ)
    (upperCutoffHilbertValueOperator χ hχ hcχ hsχ f)).congr
  filter_upwards [upperSourceTestL2_ae ψ hψ hcψ hsψ] with z hψz
  rw [hψz]
  simpa [RCLike.inner_apply, mul_comm, upperCutoffSourceField] using
    sourceTest_pairing_eq ψ (upperCutoffHilbertValueOperator χ hχ hcχ hsχ f z) z

/-- Every actual modular Hilbert source has the literal local ordinary test integral. -/
theorem periodizedUpperCore_hilbert_source_integral
    (χ : ℂ → ℂ) (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hsχ : tsupport χ ⊆ upperHalfPlaneSet)
    (ψ : ℂ → ℂ) (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ)
    (hsψ : tsupport ψ ⊆ upperHalfPlaneSet) (hχone : ∀ z ∈ tsupport ψ, χ z = 1)
    (f : ModularHilbert) :
    inner ℂ (value (periodizedUpperCore ψ hψ hcψ hsψ)) f =
      ∫ z : ℂ, star (ψ z) * upperCutoffSourceField χ hχ hcχ hsχ f z := by
  rw [periodizedUpperCore_hilbert_source_pairing χ hχ hcχ hsχ ψ hψ hcψ hsψ hχone f,
    L2.inner_def]
  apply integral_congr_ae
  filter_upwards [upperSourceTestL2_ae ψ hψ hcψ hsψ] with z hψz
  rw [hψz]
  simpa [RCLike.inner_apply, mul_comm, upperCutoffSourceField] using
    sourceTest_pairing_eq ψ (upperCutoffHilbertValueOperator χ hχ hcχ hsχ f z) z

end GapFamily.Analytic
