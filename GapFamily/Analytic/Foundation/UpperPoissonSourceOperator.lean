import GapFamily.Analytic.Modular.Elliptic.ModularUpperWeakPoisson

noncomputable section
namespace GapFamily.Analytic.UpperSource
open Set Filter MeasureTheory ModularGradient UpperHalfPlane
open scoped ContDiff

/-- The actual globally L² source lift with the hyperbolic weight absorbed in its cutoff. -/
def sourceOperator (χ : ℂ → ℂ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ upperHalfPlaneSet) :
    ModularHilbert →L[ℂ] Lp ℂ 2 (volume : Measure ℂ) :=
  upperCutoffHilbertValueOperator (upperSourceTestFunction χ)
    (contDiff_upperSourceTestFunction hχ hs) (hasCompactSupport_upperSourceTestFunction hc)
    ((tsupport_upperSourceTestFunction_subset χ).trans hs)

theorem sourceOperator_core_ae
    (χ : ℂ → ℂ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ upperHalfPlaneSet) (F : smoothCore) :
    sourceOperator χ hχ hc hs (value F) =ᵐ[(volume : Measure ℂ)]
      (fun z => χ z * F.val z / (z.im : ℂ) ^ 2) := by
  filter_upwards [upperCutoffHilbertValueOperator_value_ae (upperSourceTestFunction χ)
    (contDiff_upperSourceTestFunction hχ hs) (hasCompactSupport_upperSourceTestFunction hc)
    ((tsupport_upperSourceTestFunction_subset χ).trans hs) F] with z hz
  change upperCutoffHilbertValueOperator _ _ _ _ (value F) z = _
  rw [hz, upperSourceTestFunction]
  ring

/-- Actual Hilbert density identifies the weighted source pairing for every input. -/
theorem sourceOperator_pairing
    (χ : ℂ → ℂ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ upperHalfPlaneSet)
    (ψ : ℂ → ℂ) (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ)
    (hsψ : tsupport ψ ⊆ upperHalfPlaneSet) (f : ModularHilbert) :
    inner ℂ (euclideanCompactTest ψ hψ.continuous hcψ) (sourceOperator χ hχ hc hs f) =
      inner ℂ (upperSourceTestL2 ψ hψ hcψ hsψ)
        (upperCutoffHilbertValueOperator χ hχ hc hs f) := by
  have hd : DenseRange value := by
    simpa only [DenseRange, LinearMap.coe_range] using value_dense_range
  refine hd.induction_on f ?_ ?_
  · exact isClosed_eq
      (continuous_const.inner (sourceOperator χ hχ hc hs).continuous)
      (continuous_const.inner (upperCutoffHilbertValueOperator χ hχ hc hs).continuous)
  · intro F
    simp only [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [euclideanCompactTest_ae ψ hψ.continuous hcψ,
      sourceOperator_core_ae χ hχ hc hs F, upperSourceTestL2_ae ψ hψ hcψ hsψ,
      upperCutoffHilbertValueOperator_value_ae χ hχ hc hs F] with z hψz hsF htψ hF
    rw [hψz, hsF, htψ, hF]
    simp only [RCLike.inner_apply, upperSourceTestFunction, map_div₀, map_pow,
      Complex.conj_ofReal]
    ring

theorem sourceOperator_test_integral
    (χ : ℂ → ℂ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ upperHalfPlaneSet)
    (ψ : ℂ → ℂ) (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ)
    (hsψ : tsupport ψ ⊆ upperHalfPlaneSet) (hχone : ∀ z ∈ tsupport ψ, χ z = 1)
    (f : ModularHilbert) :
    (∫ z : ℂ, star (ψ z) * sourceOperator χ hχ hc hs f z) =
      ∫ z : ℂ, star (ψ z) * upperCutoffSourceField χ hχ hc hs f z := by
  rw [← euclideanCompactTest_inner ψ hψ.continuous hcψ (sourceOperator χ hχ hc hs f),
    sourceOperator_pairing χ hχ hc hs ψ hψ hcψ hsψ f,
    ← periodizedUpperCore_hilbert_source_pairing χ hχ hc hs ψ hψ hcψ hsψ hχone f,
    periodizedUpperCore_hilbert_source_integral χ hχ hc hs ψ hψ hcψ hsψ hχone f]

/-- The same actual Poisson equation has a globally L² source coordinate. -/
theorem laplacian_sourceOperator_weakPoisson_local
    (χ : ℂ → ℂ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ upperHalfPlaneSet)
    (U : Set ℂ) (hU : IsOpen U) (hχU : EqOn χ (fun _ => 1) U)
    (u : laplacian.domain)
    (ψ : ℂ → ℂ) (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ)
    (hψU : tsupport ψ ⊆ U) :
    (∫ z : ℂ,
      star (fderiv ℝ ψ z 1) * upperCutoffGradientOperator χ hχ hc hs 1
        (formLift ⟨u, laplacian_domain_le u.property⟩) z +
      star (fderiv ℝ ψ z Complex.I) * upperCutoffGradientOperator χ hχ hc hs Complex.I
        (formLift ⟨u, laplacian_domain_le u.property⟩) z) =
      ∫ z : ℂ, star (ψ z) * sourceOperator χ hχ hc hs (laplacian u) z := by
  have hχone : ∀ z ∈ tsupport ψ, χ z = 1 := fun z hz => hχU (hψU hz)
  have hsψ : tsupport ψ ⊆ upperHalfPlaneSet := by
    intro z hz
    apply hs
    apply subset_tsupport χ
    rw [Function.mem_support, hχone z hz]
    exact one_ne_zero
  rw [sourceOperator_test_integral χ hχ hc hs ψ hψ hcψ hsψ hχone]
  exact (laplacian_upper_weakPoisson_local χ hχ hc hs U hU hχU u ψ hψ hcψ hψU).2

end GapFamily.Analytic.UpperSource
