import GapFamily.Analytic.Modular.Elliptic.ModularUpperCutoffValue
import GapFamily.Analytic.Modular.Elliptic.ModularUpperCutoffGradient
import GapFamily.Analytic.Modular.Elliptic.ModularUpperCutoffIBP

/-!
# Ordinary weak derivative of the actual completed upper cutoff

The value is the zero extension of the existing upper cutoff operator.
The gradient and cutoff-derivative fields are actual bounded Euclidean L²
operators. Their ordinary compact-test identity passes through the genuine
smooth form core by continuity of the L² pairing.
-/

noncomputable section
namespace GapFamily.Analytic.ModularGradient
open Set MeasureTheory UpperHalfPlane
open scoped ContDiff ComplexConjugate

/-- An ordinary continuous compact test, with its genuine Euclidean L² class. -/
def euclideanCompactTest (ψ : ℂ → ℂ) (hψ : Continuous ψ) (hc : HasCompactSupport ψ) :
    Lp ℂ 2 (volume : Measure ℂ) :=
  (hψ.memLp_of_hasCompactSupport hc).toLp ψ

theorem euclideanCompactTest_ae (ψ : ℂ → ℂ) (hψ : Continuous ψ)
    (hc : HasCompactSupport ψ) :
    euclideanCompactTest ψ hψ hc =ᵐ[(volume : Measure ℂ)] ψ := MemLp.coeFn_toLp _

/-- The Hilbert pairing is the ordinary, convergent complex test integral. -/
theorem euclideanCompactTest_inner (ψ : ℂ → ℂ) (hψ : Continuous ψ)
    (hc : HasCompactSupport ψ) (f : Lp ℂ 2 (volume : Measure ℂ)) :
    inner ℂ (euclideanCompactTest ψ hψ hc) f = ∫ z : ℂ, star (ψ z) * f z := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [euclideanCompactTest_ae ψ hψ hc] with z hz
  simp only [hz, RCLike.inner_apply]
  exact mul_comm _ _

theorem euclideanCompactTest_integrable (ψ : ℂ → ℂ) (hψ : Continuous ψ)
    (hc : HasCompactSupport ψ) (f : Lp ℂ 2 (volume : Measure ℂ)) :
    Integrable (fun z : ℂ => star (ψ z) * f z) := by
  apply (L2.integrable_inner (𝕜 := ℂ) (euclideanCompactTest ψ hψ hc) f).congr
  filter_upwards [euclideanCompactTest_ae ψ hψ hc] with z hz
  simp only [hz, RCLike.inner_apply]
  exact mul_comm _ _

/-- The global completed product rule in the actual Hilbert test pairing. -/
theorem upperCutoff_weakDerivative_inner (χ : ℂ → ℂ) (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ upperHalfPlaneSet) (v : ℂ)
    (u : FormDomain) (ψ : ℂ → ℂ) (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ) :
    inner ℂ (euclideanCompactTest ψ hψ.continuous hcψ)
      (upperCutoffGradientOperator χ hχ hc hs v u +
        upperCutoffDerivativeValueOperator χ hχ hc hs v u) =
      -inner ℂ (euclideanCompactTest (fun z => fderiv ℝ ψ z v)
        (contDiff_upperCutoffDerivative hψ v).continuous (hcψ.fderiv_apply ℝ v))
        (upperCutoffValueOperator χ hχ hc hs u) := by
  refine coreForm_denseRange.induction_on (p := fun u : FormDomain =>
    inner ℂ (euclideanCompactTest ψ hψ.continuous hcψ)
      (upperCutoffGradientOperator χ hχ hc hs v u +
        upperCutoffDerivativeValueOperator χ hχ hc hs v u) =
      -inner ℂ (euclideanCompactTest (fun z => fderiv ℝ ψ z v)
        (contDiff_upperCutoffDerivative hψ v).continuous (hcψ.fderiv_apply ℝ v))
        (upperCutoffValueOperator χ hχ hc hs u)) u ?_ ?_
  · exact isClosed_eq (by fun_prop) (by fun_prop)
  · intro F
    rw [euclideanCompactTest_inner, euclideanCompactTest_inner]
    have hleft :
        (∫ z : ℂ, star (ψ z) *
          (upperCutoffGradientOperator χ hχ hc hs v (coreForm F) +
            upperCutoffDerivativeValueOperator χ hχ hc hs v (coreForm F)) z) =
        ∫ z : ℂ, star (ψ z) *
          (χ z * fderiv ℝ F.val z v + fderiv ℝ χ z v * F.val z) := by
      apply integral_congr_ae
      filter_upwards [upperCutoffGradientOperator_coreForm_ae χ hχ hc hs v F,
        upperCutoffDerivativeValueOperator_coreForm_ae χ hχ hc hs v F,
        Lp.coeFn_add (upperCutoffGradientOperator χ hχ hc hs v (coreForm F))
          (upperCutoffDerivativeValueOperator χ hχ hc hs v (coreForm F))]
        with z hgrad hcorr hadd
      simp only [hadd, Pi.add_apply, hgrad, hcorr]
    have hright :
        (∫ z : ℂ, star (fderiv ℝ ψ z v) * upperCutoffValueOperator χ hχ hc hs (coreForm F) z) =
        ∫ z : ℂ, star (fderiv ℝ ψ z v) * (χ z * F.val z) := by
      apply integral_congr_ae
      filter_upwards [upperCutoffValueOperator_coreForm_ae χ hχ hc hs F] with z hz
      rw [hz]
    rw [hleft, hright]
    exact upperCutoff_core_weakDerivative χ hχ hc hs F v ψ hψ hcψ

/-- Both ordinary integrals in the completed weak product rule are integrable. -/
theorem upperCutoff_weakDerivative_integrable (χ : ℂ → ℂ) (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ upperHalfPlaneSet) (v : ℂ)
    (u : FormDomain) (ψ : ℂ → ℂ) (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ) :
    Integrable (fun z : ℂ => star (ψ z) *
      (upperCutoffGradientOperator χ hχ hc hs v u z +
        upperCutoffDerivativeValueOperator χ hχ hc hs v u z)) ∧
    Integrable (fun z : ℂ => star (fderiv ℝ ψ z v) * upperCutoffValueOperator χ hχ hc hs u z) := by
  constructor
  · apply (euclideanCompactTest_integrable ψ hψ.continuous hcψ
      (upperCutoffGradientOperator χ hχ hc hs v u +
        upperCutoffDerivativeValueOperator χ hχ hc hs v u)).congr
    filter_upwards [Lp.coeFn_add (upperCutoffGradientOperator χ hχ hc hs v u)
      (upperCutoffDerivativeValueOperator χ hχ hc hs v u)] with z hz
    simp only [hz, Pi.add_apply]
  · exact euclideanCompactTest_integrable _ (contDiff_upperCutoffDerivative hψ v).continuous
      (hcψ.fderiv_apply ℝ v) _

/-- Ordinary Euclidean weak product rule for every completed modular form vector. -/
theorem upperCutoff_weakDerivative (χ : ℂ → ℂ) (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ upperHalfPlaneSet) (v : ℂ)
    (u : FormDomain) (ψ : ℂ → ℂ) (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ) :
    (∫ z : ℂ, star (ψ z) *
      (upperCutoffGradientOperator χ hχ hc hs v u z +
        upperCutoffDerivativeValueOperator χ hχ hc hs v u z)) =
      -(∫ z : ℂ, star (fderiv ℝ ψ z v) * upperCutoffValueOperator χ hχ hc hs u z) := by
  have h := upperCutoff_weakDerivative_inner χ hχ hc hs v u ψ hψ hcψ
  rw [euclideanCompactTest_inner, euclideanCompactTest_inner] at h
  refine Eq.trans ?_ h
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_add (upperCutoffGradientOperator χ hχ hc hs v u)
    (upperCutoffDerivativeValueOperator χ hχ hc hs v u)] with z hz
  simp only [hz, Pi.add_apply]

end GapFamily.Analytic.ModularGradient
