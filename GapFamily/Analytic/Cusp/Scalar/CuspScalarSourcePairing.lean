import GapFamily.Analytic.Cusp.Green.CuspGreenScalarResponse
import GapFamily.Analytic.Cusp.Scalar.CuspScalarForm

noncomputable section
namespace GapFamily.Analytic
open Set MeasureTheory ModularGradient
open scoped ContDiff

/-- Equality of actual source pairings on compact profiles extends to the actual scalar form space. -/
theorem cuspScalarForm_source_pairing_of_compact (F G : ModularHilbert)
    (hgen : ∀ (b : ℝ → ℂ) (hb : ContDiff ℝ ∞ b) (hc : HasCompactSupport b)
      (hs : tsupport b ⊆ Ioi (1 : ℝ)),
      inner ℂ (value (cuspProfileCore b hb hc hs)) F =
        inner ℂ (value (cuspProfileCore b hb hc hs)) G)
    (w : cuspScalarForm) :
    inner ℂ (scalarCuspEmbedding w) F = inner ℂ (scalarCuspEmbedding w) G := by
  let A : FormDomain →L[ℂ] ℂ := (innerSL ℂ (F - G)).comp formEmbedding
  have hW : cuspScalarForm ≤ A.ker := by
    apply cuspScalarForm_le_of_isClosed _ A.isClosed_ker
    intro b hb hc hs
    change inner ℂ (F - G) (formEmbedding (coreForm (cuspProfileCore b hb hc hs))) = 0
    rw [formEmbedding_coreForm, inner_sub_left]
    have h := congrArg (starRingEnd ℂ) (hgen b hb hc hs)
    simp only [inner_conj_symm] at h
    exact sub_eq_zero.mpr h
  have h := hW w.property
  change inner ℂ (F - G) (formEmbedding (w : FormDomain)) = 0 at h
  have hstar := congrArg (starRingEnd ℂ) h
  simpa only [inner_conj_symm, inner_sub_right, map_zero, sub_eq_zero, scalarCuspEmbedding_apply] using hstar

/-- Only the proved horizontal scalar projection of an ambient source affects its scalar response. -/
theorem cuspScalarPencilSolution_scalarProjection {κ : ℂ} (hκ : 0 < κ.re)
    (F : ModularHilbert) :
    cuspScalarPencilSolution (1/4 - κ^2) (cuspScalarProjection F) =
      cuspScalarPencilSolution (1/4 - κ^2) F := by
  apply cuspScalarPencilSolution_unique_physical hκ
  intro w
  rw [cuspScalarPencilSolution_equation_physical hκ,
    ← cuspScalarProjection_inner_symm, cuspScalarProjection_scalarCuspEmbedding]

end GapFamily.Analytic
