import GapFamily.Analytic.Cusp.Threshold.CuspConstrainedWeakEquation
import GapFamily.Analytic.Foundation.UpperPoissonSourceOperator
import GapFamily.Analytic.Elliptic.LocalPoissonJet

/-! Actual local Poisson fields of the constrained quarter-pencil solution,
including across modular seams. No translated norm bound is asserted here. -/
noncomputable section
namespace GapFamily.Analytic.CuspConstrainedPoissonJet
open Set MeasureTheory UpperHalfPlane ModularGradient LocalPoisson UpperSource
  CuspConstrainedWeakEquation
open scoped ContDiff

def constrainedPoissonSource (f : ModularHilbert) : ModularHilbert :=
  f - cuspScalarProjection f + (1 / 4 : ℂ) •
    meanZeroCuspEmbedding (cuspMeanZeroPencilSolution (1 / 4) f)

/-- The four fields are the actual existing ordinary cutoff lifts. -/
def constrainedJet (χ : ℂ → ℂ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ upperHalfPlaneSet) (f : ModularHilbert) : Jet :=
  (upperCutoffValueOperator χ hχ hc hs (cuspMeanZeroPencilSolution (1 / 4) f : FormDomain),
   upperCutoffGradientOperator χ hχ hc hs 1 (cuspMeanZeroPencilSolution (1 / 4) f : FormDomain),
   upperCutoffGradientOperator χ hχ hc hs Complex.I (cuspMeanZeroPencilSolution (1 / 4) f : FormDomain),
   sourceOperator χ hχ hc hs (constrainedPoissonSource f))

/-- On every actual high-cusp open plateau these fields satisfy all ordinary
Poisson-jet constraints. The projected ambient source is derived from the true
constrained equation rather than supplied as a local PDE premise. -/
theorem constrainedJet_mem (χ : ℂ → ℂ) (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ upperHalfPlaneSet)
    (U : Set ℂ) (hU : IsOpen U) (hχU : EqOn χ (fun _ => 1) U)
    (hhigh : U ⊆ {z : ℂ | 1 < z.im}) (f : ModularHilbert) :
    constrainedJet χ hχ hc hs f ∈ jetSubmodule U := by
  intro ψ hψ hcψ hψU
  let u : FormDomain := (cuspMeanZeroPencilSolution (1 / 4) f : FormDomain)
  have hsψ : tsupport ψ ⊆ upperHalfPlaneSet := by
    intro z hz
    have hh : 1 < z.im := hhigh (hψU hz)
    change 0 < z.im
    linarith
  have hχone : ∀ z ∈ tsupport ψ, χ z = 1 := fun _ hz => hχU (hψU hz)
  change inner ℂ (euclideanCompactTest ψ hψ.continuous hcψ)
      (upperCutoffGradientOperator χ hχ hc hs 1 u) =
      -inner ℂ (upperTestDerivativeL2 ψ hψ hcψ 1) (upperCutoffValueOperator χ hχ hc hs u) ∧
    inner ℂ (euclideanCompactTest ψ hψ.continuous hcψ)
      (upperCutoffGradientOperator χ hχ hc hs Complex.I u) =
      -inner ℂ (upperTestDerivativeL2 ψ hψ hcψ Complex.I)
        (upperCutoffValueOperator χ hχ hc hs u) ∧
    inner ℂ (upperTestDerivativeL2 ψ hψ hcψ 1) (upperCutoffGradientOperator χ hχ hc hs 1 u) +
      inner ℂ (upperTestDerivativeL2 ψ hψ hcψ Complex.I)
        (upperCutoffGradientOperator χ hχ hc hs Complex.I u) =
      inner ℂ (euclideanCompactTest ψ hψ.continuous hcψ)
        (sourceOperator χ hχ hc hs (constrainedPoissonSource f))
  refine ⟨?_, ?_, ?_⟩
  · rw [euclideanCompactTest_inner, inner_derivativeTest_eq_integral]
    exact upperCutoff_weakDerivative_local χ hχ hc hs 1 u ψ hψ hcψ U hU hχU hψU
  · rw [euclideanCompactTest_inner, inner_derivativeTest_eq_integral]
    exact upperCutoff_weakDerivative_local χ hχ hc hs Complex.I u ψ hψ hcψ U hU hχU hψU
  · rw [← periodizedUpperCore_formGradient_pairing χ hχ hc hs ψ hψ hcψ hsψ hχone u,
      sourceOperator_pairing χ hχ hc hs ψ hψ hcψ hsψ,
      ← periodizedUpperCore_hilbert_source_pairing χ hχ hc hs ψ hψ hcψ hsψ hχone]
    have hw := cuspMeanZeroPencilSolution_quarter_highCompact_equation f ψ hψ hcψ hsψ
      (hψU.trans hhigh)
    rw [formGradient_coreForm, formEmbedding_coreForm] at hw
    simp only [constrainedPoissonSource, inner_add_right, inner_smul_right,
      meanZeroCuspEmbedding_apply]
    exact sub_eq_iff_eq_add.mp hw

end GapFamily.Analytic.CuspConstrainedPoissonJet
