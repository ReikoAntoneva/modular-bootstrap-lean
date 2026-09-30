import GapFamily.Analytic.Cusp.Scalar.CuspConstantResponseWeakScalar
import GapFamily.Analytic.Cusp.Scalar.CuspConstantResponseWeakPairing

/-! The literal constant-source form response solves the test-first equation on the actual closed scalar cusp form space. -/

noncomputable section
namespace GapFamily.Analytic
open Set MeasureTheory ModularGradient
open scoped Topology ContDiff ComplexConjugate

/-- A bounded equation verified on literal compact cusp profiles extends to the
actual closed scalar form space. The generator premise will be discharged by
ordinary compact-profile integration by parts for the actual response. -/
theorem cuspScalarForm_test_weak_of_compact {U : FormDomain} {z : ℂ}
    (hgen : ∀ (b : ℝ → ℂ) (hb : ContDiff ℝ ∞ b) (hc : HasCompactSupport b)
      (hs : tsupport b ⊆ Ioi (1 : ℝ)),
      inner ℂ (coreGradient (cuspProfileCore b hb hc hs)) (formGradient U) -
        z * inner ℂ (value (cuspProfileCore b hb hc hs)) (formEmbedding U) =
        inner ℂ (value (cuspProfileCore b hb hc hs)) modularConstant)
    (w : cuspScalarForm) :
    inner ℂ (formGradient (w : FormDomain)) (formGradient U) -
      z * inner ℂ (formEmbedding (w : FormDomain)) (formEmbedding U) =
      inner ℂ (formEmbedding (w : FormDomain)) modularConstant := by
  let A : FormDomain →L[ℂ] ℂ :=
    (innerSL ℂ (formGradient U)).comp formGradient -
      ((starRingEnd ℂ) z) • (innerSL ℂ (formEmbedding U)).comp formEmbedding -
      (innerSL ℂ modularConstant).comp formEmbedding
  have hW : cuspScalarForm ≤ A.ker := by
    apply cuspScalarForm_le_of_isClosed _ A.isClosed_ker
    intro b hb hc hs
    change inner ℂ (formGradient U) (formGradient (coreForm (cuspProfileCore b hb hc hs))) -
      (starRingEnd ℂ) z * inner ℂ (formEmbedding U) (formEmbedding (coreForm (cuspProfileCore b hb hc hs))) -
      inner ℂ modularConstant (formEmbedding (coreForm (cuspProfileCore b hb hc hs))) = 0
    rw [formGradient_coreForm, formEmbedding_coreForm]
    have h := congrArg (starRingEnd ℂ) (hgen b hb hc hs)
    simp only [map_sub, map_mul, inner_conj_symm] at h
    exact sub_eq_zero.mpr h
  have h := hW w.property
  change inner ℂ (formGradient U) (formGradient (w : FormDomain)) -
    (starRingEnd ℂ) z * inner ℂ (formEmbedding U) (formEmbedding (w : FormDomain)) -
    inner ℂ modularConstant (formEmbedding (w : FormDomain)) = 0 at h
  have hs := congrArg (starRingEnd ℂ) h
  simpa only [map_sub, map_mul, starRingEnd_self_apply, inner_conj_symm, map_zero, sub_eq_zero] using hs

end GapFamily.Analytic

noncomputable section
namespace GapFamily.Analytic
open Set MeasureTheory ModularGradient
open scoped Topology ContDiff

/-- The literal response satisfies the actual modular equation for every smooth
compact scalar cusp test. Both scalar pairings are ordinary convergent integrals. -/
theorem cuspConstantForm_compact_test_weak {κ : ℂ} (hκ : 0 < κ.re)
    (b : ℝ → ℂ) (hb : ContDiff ℝ ∞ b) (hc : HasCompactSupport b)
    (hs : tsupport b ⊆ Ioi (1 : ℝ)) :
    inner ℂ (coreGradient (cuspProfileCore b hb hc hs)) (formGradient (cuspConstantForm hκ)) -
      (1 / 4 - κ ^ 2) *
        inner ℂ (value (cuspProfileCore b hb hc hs)) (formEmbedding (cuspConstantForm hκ)) =
      inner ℂ (value (cuspProfileCore b hb hc hs)) modularConstant := by
  rw [cuspConstantForm_test_gradient_pairing b hb hc hs hκ,
    cuspConstantForm_test_pairing b hb hc hs hκ, cuspConstantForm_test_source_pairing b hb hc hs]
  apply cuspConstantPhysicalResponse_compact_test_weak b hb hc hs
  intro h
  subst κ
  norm_num at hκ

/-- The actual constant-source form solves the test-first scalar cusp weak equation
against every vector in the actual closed scalar form space. -/
theorem cuspConstantForm_test_weak {κ : ℂ} (hκ : 0 < κ.re) (w : cuspScalarForm) :
    inner ℂ (formGradient (w : FormDomain)) (formGradient (cuspConstantForm hκ)) -
      (1 / 4 - κ ^ 2) *
        inner ℂ (formEmbedding (w : FormDomain)) (formEmbedding (cuspConstantForm hκ)) =
      inner ℂ (formEmbedding (w : FormDomain)) modularConstant :=
  cuspScalarForm_test_weak_of_compact (cuspConstantForm_compact_test_weak hκ) w

/-- The same genuine weak equation stated entirely with the constructed scalar
form-space response and the actual ambient scalar embedding. -/
theorem cuspConstantScalarForm_test_weak {κ : ℂ} (hκ : 0 < κ.re) (w : cuspScalarForm) :
    inner ℂ (formGradient (w : FormDomain))
        (formGradient (cuspConstantScalarForm hκ : FormDomain)) -
      (1 / 4 - κ ^ 2) *
        inner ℂ (scalarCuspEmbedding w) (scalarCuspEmbedding (cuspConstantScalarForm hκ)) =
      inner ℂ (scalarCuspEmbedding w) modularConstant :=
  cuspConstantForm_test_weak hκ w

/-- At the removable parameter the actual logarithm vector solves the unshifted
Dirichlet cusp equation against every scalar form test. -/
theorem cuspConstantScalarForm_half_test_weak (w : cuspScalarForm) :
    inner ℂ (formGradient (w : FormDomain))
        (formGradient (cuspConstantScalarForm (κ := (1 / 2 : ℂ)) (by norm_num) : FormDomain)) =
      inner ℂ (scalarCuspEmbedding w) modularConstant := by
  have h := cuspConstantScalarForm_test_weak (κ := (1 / 2 : ℂ)) (by norm_num) w
  norm_num at h
  exact h


end GapFamily.Analytic
