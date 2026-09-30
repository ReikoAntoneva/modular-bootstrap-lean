import GapFamily.Analytic.Modular.Elliptic.ModularUpperCutoffWeakGradient
import GapFamily.Analytic.Modular.Elliptic.ModularLocalDerivativeTest

/-!
# The closed space of local Poisson jets

The four fields are actual ordinary Euclidean L² classes. Membership consists
exactly of the two weak derivative identities and the weak Poisson identity
against every smooth compactly supported complex test in the chosen region.
-/

noncomputable section
namespace GapFamily.Analytic.LocalPoisson

open Set Filter MeasureTheory ModularGradient
open scoped ContDiff Topology

abbrev Field := Lp ℂ 2 (volume : Measure ℂ)
abbrev Jet := Field × (Field × (Field × Field))

/-- Coordinate projections of the genuine four-field ambient Banach space. -/
def valueProjection : Jet →L[ℂ] Field := ContinuousLinearMap.fst ℂ Field _
def dxProjection : Jet →L[ℂ] Field :=
  (ContinuousLinearMap.fst ℂ Field _).comp (ContinuousLinearMap.snd ℂ Field _)
def dyProjection : Jet →L[ℂ] Field :=
  (ContinuousLinearMap.fst ℂ Field Field).comp
    ((ContinuousLinearMap.snd ℂ Field _).comp (ContinuousLinearMap.snd ℂ Field _))
def sourceProjection : Jet →L[ℂ] Field :=
  (ContinuousLinearMap.snd ℂ Field Field).comp
    ((ContinuousLinearMap.snd ℂ Field _).comp (ContinuousLinearMap.snd ℂ Field _))

/-- The distributional first-order and Poisson constraints for an ordinary L² jet. -/
def jetSubmodule (U : Set ℂ) : Submodule ℂ Jet where
  carrier := {j | ∀ (ψ : ℂ → ℂ) (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ),
    tsupport ψ ⊆ U →
      inner ℂ (euclideanCompactTest ψ hψ.continuous hc) j.2.1 =
        -inner ℂ (upperTestDerivativeL2 ψ hψ hc 1) j.1 ∧
      inner ℂ (euclideanCompactTest ψ hψ.continuous hc) j.2.2.1 =
        -inner ℂ (upperTestDerivativeL2 ψ hψ hc Complex.I) j.1 ∧
      inner ℂ (upperTestDerivativeL2 ψ hψ hc 1) j.2.1 +
        inner ℂ (upperTestDerivativeL2 ψ hψ hc Complex.I) j.2.2.1 =
          inner ℂ (euclideanCompactTest ψ hψ.continuous hc) j.2.2.2}
  zero_mem' := by
    intro ψ hψ hc hs
    simp
  add_mem' := by
    intro a b ha hb ψ hψ hc hs
    obtain ⟨hax, hay, hap⟩ := ha ψ hψ hc hs
    obtain ⟨hbx, hby, hbp⟩ := hb ψ hψ hc hs
    change inner ℂ _ (a.2.1 + b.2.1) = -inner ℂ _ (a.1 + b.1) ∧
      inner ℂ _ (a.2.2.1 + b.2.2.1) = -inner ℂ _ (a.1 + b.1) ∧
      inner ℂ _ (a.2.1 + b.2.1) + inner ℂ _ (a.2.2.1 + b.2.2.1) =
        inner ℂ _ (a.2.2.2 + b.2.2.2)
    simp only [inner_add_right]
    exact ⟨by rw [hax, hbx]; ring, by rw [hay, hby]; ring,
      by linear_combination hap + hbp⟩
  smul_mem' := by
    intro c a ha ψ hψ hc hs
    obtain ⟨hax, hay, hap⟩ := ha ψ hψ hc hs
    change inner ℂ _ (c • a.2.1) = -inner ℂ _ (c • a.1) ∧
      inner ℂ _ (c • a.2.2.1) = -inner ℂ _ (c • a.1) ∧
      inner ℂ _ (c • a.2.1) + inner ℂ _ (c • a.2.2.1) =
        inner ℂ _ (c • a.2.2.2)
    simp only [inner_smul_right]
    exact ⟨by rw [hax]; ring, by rw [hay]; ring, by rw [← mul_add, hap]⟩

/-- Every test constraint is a closed continuous linear equation. -/
theorem isClosed_jetSubmodule (U : Set ℂ) : IsClosed (jetSubmodule U : Set Jet) := by
  change IsClosed {j : Jet | ∀ (ψ : ℂ → ℂ) (hψ : ContDiff ℝ ∞ ψ)
    (hc : HasCompactSupport ψ), tsupport ψ ⊆ U →
      inner ℂ (euclideanCompactTest ψ hψ.continuous hc) j.2.1 =
        -inner ℂ (upperTestDerivativeL2 ψ hψ hc 1) j.1 ∧
      inner ℂ (euclideanCompactTest ψ hψ.continuous hc) j.2.2.1 =
        -inner ℂ (upperTestDerivativeL2 ψ hψ hc Complex.I) j.1 ∧
      inner ℂ (upperTestDerivativeL2 ψ hψ hc 1) j.2.1 +
        inner ℂ (upperTestDerivativeL2 ψ hψ hc Complex.I) j.2.2.1 =
          inner ℂ (euclideanCompactTest ψ hψ.continuous hc) j.2.2.2}
  simp only [Set.ofPred_forall, Set.ofPred_and]
  refine isClosed_iInter fun ψ => isClosed_iInter fun hψ =>
    isClosed_iInter fun hc => isClosed_iInter fun hs => ?_
  exact (isClosed_eq (by fun_prop) (by fun_prop)).inter
    ((isClosed_eq (by fun_prop) (by fun_prop)).inter
      (isClosed_eq (by fun_prop) (by fun_prop)))

/-- A local Poisson jet, with all fields and all distributional tests included. -/
abbrev JetSpace (U : Set ℂ) := jetSubmodule U

instance (U : Set ℂ) : CompleteSpace (JetSpace U) :=
  (isClosed_jetSubmodule U).isComplete.completeSpace_coe

def valueCLM (U : Set ℂ) : JetSpace U →L[ℂ] Field :=
  valueProjection.comp (jetSubmodule U).subtypeL

def dxCLM (U : Set ℂ) : JetSpace U →L[ℂ] Field :=
  dxProjection.comp (jetSubmodule U).subtypeL

def dyCLM (U : Set ℂ) : JetSpace U →L[ℂ] Field :=
  dyProjection.comp (jetSubmodule U).subtypeL

def sourceCLM (U : Set ℂ) : JetSpace U →L[ℂ] Field :=
  sourceProjection.comp (jetSubmodule U).subtypeL

@[simp] theorem valueCLM_apply (U : Set ℂ) (u : JetSpace U) : valueCLM U u = u.val.1 := rfl
@[simp] theorem dxCLM_apply (U : Set ℂ) (u : JetSpace U) : dxCLM U u = u.val.2.1 := rfl
@[simp] theorem dyCLM_apply (U : Set ℂ) (u : JetSpace U) : dyCLM U u = u.val.2.2.1 := rfl
@[simp] theorem sourceCLM_apply (U : Set ℂ) (u : JetSpace U) : sourceCLM U u = u.val.2.2.2 := rfl

/-- Every compact continuous test pairs ordinarily with every field. -/
theorem test_integrable (ψ : ℂ → ℂ) (hψ : Continuous ψ)
    (hc : HasCompactSupport ψ) (f : Field) :
    Integrable (fun z : ℂ => star (ψ z) * f z) volume :=
  euclideanCompactTest_integrable ψ hψ hc f

/-- Every derivative test likewise gives an ordinary convergent integral. -/
theorem derivative_test_integrable (ψ : ℂ → ℂ) (hψ : ContDiff ℝ ∞ ψ)
    (hc : HasCompactSupport ψ) (v : ℂ) (f : Field) :
    Integrable (fun z : ℂ => star (fderiv ℝ ψ z v) * f z) volume :=
  euclideanCompactTest_integrable (fun z => fderiv ℝ ψ z v)
    (contDiff_upperCutoffDerivative hψ v).continuous (hc.fderiv_apply ℝ v) f

/-- The derivative-test Hilbert pairing is its literal ordinary integral. -/
theorem inner_derivativeTest_eq_integral (ψ : ℂ → ℂ) (hψ : ContDiff ℝ ∞ ψ)
    (hc : HasCompactSupport ψ) (v : ℂ) (f : Field) :
    inner ℂ (upperTestDerivativeL2 ψ hψ hc v) f =
      ∫ z : ℂ, star (fderiv ℝ ψ z v) * f z := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [upperTestDerivativeL2_ae ψ hψ hc v] with z hz
  simp [hz, RCLike.inner_apply, mul_comm]

/-- Literal horizontal weak derivative identity of every local Poisson jet. -/
theorem weak_dx (U : Set ℂ) (u : JetSpace U) (ψ : ℂ → ℂ)
    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ) (hs : tsupport ψ ⊆ U) :
    (∫ z : ℂ, star (ψ z) * dxCLM U u z) =
      -(∫ z : ℂ, star (fderiv ℝ ψ z 1) * valueCLM U u z) := by
  have h := (u.property ψ hψ hc hs).1
  change inner ℂ (euclideanCompactTest ψ hψ.continuous hc) (dxCLM U u) =
    -inner ℂ (upperTestDerivativeL2 ψ hψ hc 1) (valueCLM U u) at h
  rwa [euclideanCompactTest_inner, inner_derivativeTest_eq_integral] at h

/-- Literal vertical weak derivative identity of every local Poisson jet. -/
theorem weak_dy (U : Set ℂ) (u : JetSpace U) (ψ : ℂ → ℂ)
    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ) (hs : tsupport ψ ⊆ U) :
    (∫ z : ℂ, star (ψ z) * dyCLM U u z) =
      -(∫ z : ℂ, star (fderiv ℝ ψ z Complex.I) * valueCLM U u z) := by
  have h := (u.property ψ hψ hc hs).2.1
  change inner ℂ (euclideanCompactTest ψ hψ.continuous hc) (dyCLM U u) =
    -inner ℂ (upperTestDerivativeL2 ψ hψ hc Complex.I) (valueCLM U u) at h
  rwa [euclideanCompactTest_inner, inner_derivativeTest_eq_integral] at h

/-- The ordinary complex test identity for minus the Euclidean Laplacian. -/
theorem weak_poisson (U : Set ℂ) (u : JetSpace U) (ψ : ℂ → ℂ)
    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ) (hs : tsupport ψ ⊆ U) :
    (∫ z : ℂ, star (fderiv ℝ ψ z 1) * dxCLM U u z +
      star (fderiv ℝ ψ z Complex.I) * dyCLM U u z) =
        ∫ z : ℂ, star (ψ z) * sourceCLM U u z := by
  have h := (u.property ψ hψ hc hs).2.2
  change inner ℂ (upperTestDerivativeL2 ψ hψ hc 1) (dxCLM U u) +
    inner ℂ (upperTestDerivativeL2 ψ hψ hc Complex.I) (dyCLM U u) =
      inner ℂ (euclideanCompactTest ψ hψ.continuous hc) (sourceCLM U u) at h
  rw [inner_derivativeTest_eq_integral, inner_derivativeTest_eq_integral,
    euclideanCompactTest_inner] at h
  rw [integral_add (derivative_test_integrable ψ hψ hc 1 (dxCLM U u))
    (derivative_test_integrable ψ hψ hc Complex.I (dyCLM U u))]
  exact h

/-- Every integral in the three distributional constraints is genuinely convergent. -/
theorem weak_test_integrable (U : Set ℂ) (u : JetSpace U) (ψ : ℂ → ℂ)
    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ) :
    Integrable (fun z : ℂ => star (ψ z) * dxCLM U u z) volume ∧
    Integrable (fun z : ℂ => star (ψ z) * dyCLM U u z) volume ∧
    Integrable (fun z : ℂ => star (fderiv ℝ ψ z 1) * valueCLM U u z) volume ∧
    Integrable (fun z : ℂ => star (fderiv ℝ ψ z Complex.I) * valueCLM U u z) volume ∧
    Integrable (fun z : ℂ => star (fderiv ℝ ψ z 1) * dxCLM U u z +
      star (fderiv ℝ ψ z Complex.I) * dyCLM U u z) volume ∧
    Integrable (fun z : ℂ => star (ψ z) * sourceCLM U u z) volume :=
  ⟨test_integrable ψ hψ.continuous hc _, test_integrable ψ hψ.continuous hc _,
    derivative_test_integrable ψ hψ hc 1 _, derivative_test_integrable ψ hψ hc Complex.I _,
    (derivative_test_integrable ψ hψ hc 1 _).add
      (derivative_test_integrable ψ hψ hc Complex.I _), test_integrable ψ hψ.continuous hc _⟩

end GapFamily.Analytic.LocalPoisson
