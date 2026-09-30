import GapFamily.Analytic.Modular.Elliptic.ModularUpperCutoffWeakGradient

/-!
# Weak derivatives on a plateau of the actual upper cutoff

The correction from differentiating the cutoff pairs to zero with every
compact test supported where the cutoff is one. This identity passes through
the actual form-core density, without choosing completed pointwise derivatives.
-/

noncomputable section
namespace GapFamily.Analytic.ModularGradient
open Set MeasureTheory UpperHalfPlane Filter
open scoped ContDiff Topology

private theorem upperCutoff_fderiv_eq_zero_on {χ : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hχU : EqOn χ (fun _ => 1) U) {z : ℂ} (hz : z ∈ U) (v : ℂ) :
    fderiv ℝ χ z v = 0 := by
  have heq : χ =ᶠ[𝓝 z] (fun _ => 1) := by
    filter_upwards [hU.mem_nhds hz] with w hw
    exact hχU hw
  rw [heq.fderiv_eq]
  simp

/-- The cutoff-derivative correction vanishes against tests supported in an
actual open plateau, first on the genuine core and hence on every form vector. -/
theorem upperCutoffDerivativeValueOperator_pairing_eq_zero
    (χ : ℂ → ℂ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ upperHalfPlaneSet) (v : ℂ) (u : FormDomain)
    (ψ : ℂ → ℂ) (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ)
    (U : Set ℂ) (hU : IsOpen U) (hχU : EqOn χ (fun _ => 1) U)
    (hψU : tsupport ψ ⊆ U) :
    inner ℂ (euclideanCompactTest ψ hψ.continuous hcψ)
      (upperCutoffDerivativeValueOperator χ hχ hc hs v u) = 0 := by
  refine coreForm_denseRange.induction_on (p := fun u : FormDomain =>
    inner ℂ (euclideanCompactTest ψ hψ.continuous hcψ)
      (upperCutoffDerivativeValueOperator χ hχ hc hs v u) = 0) u ?_ ?_
  · exact isClosed_eq (by fun_prop) continuous_const
  · intro F
    rw [euclideanCompactTest_inner]
    apply integral_eq_zero_of_ae
    filter_upwards [upperCutoffDerivativeValueOperator_coreForm_ae χ hχ hc hs v F] with z hz
    rw [hz]
    by_cases hψz : z ∈ tsupport ψ
    · simp only [upperCutoff_fderiv_eq_zero_on hU hχU (hψU hψz) v,
        zero_mul, mul_zero, Pi.zero_apply]
    · simp [image_eq_zero_of_notMem_tsupport hψz]

/-- On a plateau, the actual extended cutoff gradient satisfies the ordinary
weak identity without a cutoff-derivative correction. -/
theorem upperCutoff_weakDerivative_local_inner
    (χ : ℂ → ℂ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ upperHalfPlaneSet) (v : ℂ) (u : FormDomain)
    (ψ : ℂ → ℂ) (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ)
    (U : Set ℂ) (hU : IsOpen U) (hχU : EqOn χ (fun _ => 1) U)
    (hψU : tsupport ψ ⊆ U) :
    inner ℂ (euclideanCompactTest ψ hψ.continuous hcψ)
      (upperCutoffGradientOperator χ hχ hc hs v u) =
      -inner ℂ (euclideanCompactTest (fun z => fderiv ℝ ψ z v)
        (contDiff_upperCutoffDerivative hψ v).continuous (hcψ.fderiv_apply ℝ v))
        (upperCutoffValueOperator χ hχ hc hs u) := by
  have h := upperCutoff_weakDerivative_inner χ hχ hc hs v u ψ hψ hcψ
  rw [inner_add_right,
    upperCutoffDerivativeValueOperator_pairing_eq_zero χ hχ hc hs v u ψ hψ hcψ U hU hχU hψU,
    add_zero] at h
  exact h

/-- The local identity is an ordinary global-area integral equality for
compact complex tests supported in the plateau. -/
theorem upperCutoff_weakDerivative_local
    (χ : ℂ → ℂ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ upperHalfPlaneSet) (v : ℂ) (u : FormDomain)
    (ψ : ℂ → ℂ) (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ)
    (U : Set ℂ) (hU : IsOpen U) (hχU : EqOn χ (fun _ => 1) U)
    (hψU : tsupport ψ ⊆ U) :
    (∫ z : ℂ, star (ψ z) * upperCutoffGradientOperator χ hχ hc hs v u z) =
      -(∫ z : ℂ, star (fderiv ℝ ψ z v) * upperCutoffValueOperator χ hχ hc hs u z) := by
  have h := upperCutoff_weakDerivative_local_inner χ hχ hc hs v u ψ hψ hcψ U hU hχU hψU
  simpa only [euclideanCompactTest_inner] using h

end GapFamily.Analytic.ModularGradient
