import GapFamily.Analytic.Cusp.Green.CuspGreenSmoothPencil
import GapFamily.Analytic.Cusp.Green.CuspGreenSourceEmbedding
import GapFamily.Analytic.Cusp.Green.CuspGreenResponseDensity

/-!
# Actual scalar Green response for arbitrary collar L² sources

The checked source isometry and scalar pencil produce an actual closed-form
vector. Dense smooth-source identification and pointwise source continuity of
the literal Green integral establish its representative for every L² source.
The weak equation and ordinary source pairing require no rough-source smoothness.
-/

noncomputable section
namespace GapFamily.Analytic
open Set Filter MeasureTheory ModularGradient
open scoped Topology ContDiff

/-- The actual scalar form response to every compact-collar L² source.
The physical-half-plane theorems below identify it with the literal Green integral. -/
def cuspGreenScalarFormOperator (T : ℝ) (κ : ℂ) :
    Lp ℂ 2 (cuspGreenCollarMeasure 0 T) →L[ℂ] cuspScalarForm :=
  (cuspScalarPencilSolution (1/4 - κ^2)).comp
    (cuspGreenSourceEmbedding T).toContinuousLinearMap

/-- The actual modular L² value of that scalar form response. -/
def cuspGreenScalarResponseOperator (T : ℝ) (κ : ℂ) :
    Lp ℂ 2 (cuspGreenCollarMeasure 0 T) →L[ℂ] ModularHilbert :=
  scalarCuspEmbedding.comp (cuspGreenScalarFormOperator T κ)

/-- The completed source/response construction agrees with the literal smooth-source graph limit. -/
theorem cuspGreenScalarFormOperator_smooth {T : ℝ} (hT : 0 ≤ T)
    {κ : ℂ} (hκ : 0 < κ.re) {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f)
    (hfc : HasCompactSupport f) (hfS : tsupport f ⊆ Ioo 0 T) :
    cuspGreenScalarFormOperator T κ (cuspGreenCollarSource 0 T f hf.continuous) =
      (⟨cuspGreenSmoothForm hT hκ hf hfS,
        cuspGreenSmoothForm_mem_cuspScalarForm hT hκ hf hfS⟩ : cuspScalarForm) := by
  change cuspScalarPencilSolution (1/4 - κ^2)
    (cuspGreenSourceEmbedding T (cuspGreenCollarSource 0 T f hf.continuous)) = _
  rw [cuspGreenSourceEmbedding_smooth T f hf hfc hfS]
  exact (cuspGreenSmoothForm_eq_pencilSolution hT hκ hf hfc hfS).symm

/-- Every actual L² source yields an actual scalar form vector whose representative
is the literal Green integral, including below-cusp zero extension. -/
theorem cuspGreenScalarResponseOperator_ae {T : ℝ} (hT : 0 ≤ T)
    {κ : ℂ} (hκ : 0 < κ.re) (f : Lp ℂ 2 (cuspGreenCollarMeasure 0 T)) :
    cuspGreenScalarResponseOperator T κ f =ᵐ[modularMeasure]
      fun τ : UpperHalfPlane => if 1 < τ.im then
        Real.sqrt τ.im • cuspGreenCollarResponse 0 T κ f (Real.log τ.im) else 0 := by
  apply cuspGreenCollarResponse_ae_of_dense T κ (cuspGreenScalarResponseOperator T κ)
    (cuspGreenSourceRestriction_denseRange T)
  rintro g ⟨p, rfl⟩
  have hf := p.property.1
  have hfc := p.property.2.1
  have hfS := p.property.2.2
  have hfT : ∀ u : ℝ, T < u → (p : ℝ → ℂ) u = 0 := by
    intro u hu
    exact image_eq_zero_of_notMem_tsupport (fun h => (hfS h).2.not_ge hu.le)
  change scalarCuspEmbedding
    (cuspGreenScalarFormOperator T κ (cuspGreenCollarSource 0 T (p : ℝ → ℂ) hf.continuous)) =ᵐ[_] _
  rw [cuspGreenScalarFormOperator_smooth hT hκ hf hfc hfS]
  have he := cuspGreenSmoothForm_embedding_ae hT hκ hf hfS
  have hrestriction : cuspGreenSourceRestriction T p =
      cuspGreenCollarSource 0 T (p : ℝ → ℂ) hf.continuous := rfl
  rw [hrestriction]
  simpa only [scalarCuspEmbedding_apply,
    cuspGreenCollarResponse_source_eq_solution T hT κ (p : ℝ → ℂ) hf.continuous hfT] using he

/-- The true compact-collar response satisfies the test-first weak equation
against every actual scalar form test, without source regularity assumptions. -/
theorem cuspGreenScalarFormOperator_weak {T : ℝ} {κ : ℂ} (hκ : 0 < κ.re)
    (f : Lp ℂ 2 (cuspGreenCollarMeasure 0 T)) (w : cuspScalarForm) :
    inner ℂ (cuspScalarGradient w) (cuspScalarGradient (cuspGreenScalarFormOperator T κ f)) -
      (1/4 - κ^2) * inner ℂ (scalarCuspEmbedding w)
        (cuspGreenScalarResponseOperator T κ f) =
      inner ℂ (scalarCuspEmbedding w) (cuspGreenSourceEmbedding T f) :=
  cuspScalarPencilSolution_equation_physical hκ (cuspGreenSourceEmbedding T f) w

/-- Uniqueness is in the actual closed scalar form space. -/
theorem cuspGreenScalarFormOperator_unique {T : ℝ} {κ : ℂ} (hκ : 0 < κ.re)
    (f : Lp ℂ 2 (cuspGreenCollarMeasure 0 T)) (u : cuspScalarForm)
    (hu : ∀ w : cuspScalarForm,
      inner ℂ (cuspScalarGradient w) (cuspScalarGradient u) -
        (1/4 - κ^2) * inner ℂ (scalarCuspEmbedding w) (scalarCuspEmbedding u) =
        inner ℂ (scalarCuspEmbedding w) (cuspGreenSourceEmbedding T f)) :
    u = cuspGreenScalarFormOperator T κ f :=
  cuspScalarPencilSolution_unique_physical hκ (cuspGreenSourceEmbedding T f) u hu

/-- The literal Green response has finite physical mass, obtained from its actual form vector. -/
theorem cuspGreenScalarResponse_mass {T : ℝ} (hT : 0 ≤ T)
    {κ : ℂ} (hκ : 0 < κ.re) (f : Lp ℂ 2 (cuspGreenCollarMeasure 0 T)) :
    IntegrableOn (fun y => ‖cuspLift (cuspGreenCollarResponse 0 T κ f) y‖^2 / y^2) (Ioi 1) ∧
      ‖cuspGreenScalarResponseOperator T κ f‖^2 =
        ∫ y in Ioi (1 : ℝ), ‖cuspLift (cuspGreenCollarResponse 0 T κ f) y‖^2 / y^2 := by
  exact cuspProfile_form_value_norm_sq_of_ae
    (cuspGreenScalarFormOperator T κ f : FormDomain) _
    (cuspGreenScalarResponseOperator_ae hT hκ f)

/-- Ordinary logarithmic squared mass of the actual rough-source Green integral is finite. -/
theorem cuspGreenCollarResponse_mass_integrable {T : ℝ} (hT : 0 ≤ T)
    {κ : ℂ} (hκ : 0 < κ.re) (f : Lp ℂ 2 (cuspGreenCollarMeasure 0 T)) :
    IntegrableOn (fun t => ‖cuspGreenCollarResponse 0 T κ f t‖^2) (Ioi 0) := by
  have h := (integrableOn_cuspLogCoordinate_mass_iff
    (cuspLift (cuspGreenCollarResponse 0 T κ f))).mp (cuspGreenScalarResponse_mass hT hκ f).1
  simpa only [cuspLogCoordinate_cuspLift_source] using h

/-- Inner products against a continuous test are ordinary convergent collar integrals. -/
theorem cuspGreenCollarSource_inner_integral (T : ℝ) (ψ : ℝ → ℂ) (hψ : Continuous ψ)
    (f : Lp ℂ 2 (cuspGreenCollarMeasure 0 T)) :
    Integrable (fun u : CuspGreenCollar 0 T => inner ℂ (ψ u) (f u))
      (cuspGreenCollarMeasure 0 T) ∧
    inner ℂ (cuspGreenCollarSource 0 T ψ hψ) f =
      ∫ u : CuspGreenCollar 0 T, inner ℂ (ψ u) (f u) ∂cuspGreenCollarMeasure 0 T := by
  have hae : (fun u : CuspGreenCollar 0 T =>
      inner ℂ (cuspGreenCollarSource 0 T ψ hψ u) (f u)) =ᵐ[cuspGreenCollarMeasure 0 T]
      (fun u => inner ℂ (ψ u) (f u)) := by
    filter_upwards [cuspGreenCollarSource_coeFn 0 T ψ hψ] with u hu
    rw [hu]
  exact ⟨(L2.integrable_inner (cuspGreenCollarSource 0 T ψ hψ) f).congr hae,
    by rw [L2.inner_def, integral_congr_ae hae]⟩

/-- The all-L² source isometry retains the literal logarithmic source pairing
against every genuine compact scalar profile, not only smooth sources. -/
theorem cuspGreenSourceEmbedding_compact_pairing (T : ℝ)
    (f : Lp ℂ 2 (cuspGreenCollarMeasure 0 T))
    (b : ℝ → ℂ) (hb : ContDiff ℝ ∞ b) (hc : HasCompactSupport b)
    (hs : tsupport b ⊆ Ioi 1) :
    inner ℂ (value (cuspProfileCore b hb hc hs)) (cuspGreenSourceEmbedding T f) =
      ∫ u : CuspGreenCollar 0 T, inner ℂ (cuspLogCoordinate b u) (f u)
        ∂cuspGreenCollarMeasure 0 T := by
  let B : ModularHilbert := value (cuspProfileCore b hb hc hs)
  let ψ := cuspLogCoordinate b
  have hψ : Continuous ψ := continuous_cuspLogCoordinate hb.continuous
  let P : Lp ℂ 2 (cuspGreenCollarMeasure 0 T) := cuspGreenCollarSource 0 T ψ hψ
  have heq : inner ℂ B (cuspGreenSourceEmbedding T f) = inner ℂ P f := by
    refine (cuspGreenSourceRestriction_denseRange T).induction_on
      (p := fun g => inner ℂ B (cuspGreenSourceEmbedding T g) = inner ℂ P g) f ?_ ?_
    · exact isClosed_eq
        ((innerSL ℂ B).continuous.comp (cuspGreenSourceEmbedding T).continuous)
        (innerSL ℂ P).continuous
    · intro p
      have hr : cuspGreenSourceRestriction T p =
          cuspGreenCollarSource 0 T (p : ℝ → ℂ) p.property.1.continuous := rfl
      rw [hr, cuspGreenSourceEmbedding_smooth T (p : ℝ → ℂ)
        p.property.1 p.property.2.1 p.property.2.2]
      change inner ℂ (value (cuspProfileCore b hb hc hs)) _ = _
      rw [cuspGreenSourceLift_compact_pairing p.property.1 p.property.2.1 p.property.2.2 b hb hc hs]
      exact (cuspGreenCollarSource_inner_integral T ψ hψ _).2.symm
  exact heq.trans (cuspGreenCollarSource_inner_integral T ψ hψ f).2

/-- The actual arbitrary-L² scalar response solves the literal compact-profile
source equation in the modular form, with all source normalizations discharged. -/
theorem cuspGreenScalarFormOperator_compact_test {T : ℝ} {κ : ℂ} (hκ : 0 < κ.re)
    (f : Lp ℂ 2 (cuspGreenCollarMeasure 0 T))
    (b : ℝ → ℂ) (hb : ContDiff ℝ ∞ b) (hc : HasCompactSupport b)
    (hs : tsupport b ⊆ Ioi 1) :
    inner ℂ (coreGradient (cuspProfileCore b hb hc hs))
      (cuspScalarGradient (cuspGreenScalarFormOperator T κ f)) -
      (1/4 - κ^2) * inner ℂ (value (cuspProfileCore b hb hc hs))
        (cuspGreenScalarResponseOperator T κ f) =
      ∫ u : CuspGreenCollar 0 T, inner ℂ (cuspLogCoordinate b u) (f u)
        ∂cuspGreenCollarMeasure 0 T := by
  have h := cuspGreenScalarFormOperator_weak hκ f
    (⟨coreForm (cuspProfileCore b hb hc hs), cuspProfileCore_mem_cuspScalarForm b hb hc hs⟩ : cuspScalarForm)
  change inner ℂ (formGradient (coreForm (cuspProfileCore b hb hc hs))) _ -
    (1/4 - κ^2) * inner ℂ (formEmbedding (coreForm (cuspProfileCore b hb hc hs))) _ =
    inner ℂ (formEmbedding (coreForm (cuspProfileCore b hb hc hs))) _ at h
  rw [formGradient_coreForm, formEmbedding_coreForm,
    cuspGreenSourceEmbedding_compact_pairing T f b hb hc hs] at h
  exact h

end GapFamily.Analytic
