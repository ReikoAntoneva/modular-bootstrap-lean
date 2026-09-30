import GapFamily.Analytic.Cusp.Schur.CuspSchurForm
import GapFamily.Analytic.Cusp.MeanZero.CuspMeanZeroGap
import GapFamily.Analytic.Cusp.CuspHighCompactTrace

/-!
The actual constrained solution satisfies the projected ambient weak equation
against every form-domain test whose actual cusp-average trace vanishes.
-/

noncomputable section

namespace GapFamily.Analytic.CuspConstrainedWeakEquation

open ModularGradient CuspSchur
open scoped ContDiff

theorem meanZero_source_projection_pairing (v : cuspMeanZeroForm)
    (f : ModularHilbert) :
    inner ℂ (meanZeroCuspEmbedding v) (f - cuspScalarProjection f) =
      inner ℂ (meanZeroCuspEmbedding v) f := by
  rw [inner_sub_right, ← cuspScalarProjection_inner_symm,
    cuspScalarProjection_meanZeroCuspEmbedding, inner_zero_left, sub_zero]

theorem scalar_source_projection_pairing (w : cuspScalarForm)
    (f : ModularHilbert) :
    inner ℂ (scalarCuspEmbedding w) (f - cuspScalarProjection f) = 0 := by
  rw [inner_sub_right, ← cuspScalarProjection_inner_symm,
    cuspScalarProjection_scalarCuspEmbedding, sub_self]

theorem cuspMeanZeroPencilSolution_traceZero_formPairing {z : ℂ}
    (hz : IsUnit (cuspMeanZeroPencil z)) (f : ModularHilbert)
    (v : FormDomain) (hv : cuspAverageTrace v = 0) :
    formPairing z v (cuspMeanZeroPencilSolution z f : FormDomain) =
      inner ℂ (formEmbedding v) (f - cuspScalarProjection f) := by
  have hs : (cuspMeanZeroFormPart v : FormDomain) +
      (cuspScalarFormPart v : FormDomain) = v := by
    simpa only [hv, zero_smul, add_zero] using cuspForm_reconstruct v
  have he : formPairing z (cuspMeanZeroFormPart v : FormDomain)
      (cuspMeanZeroPencilSolution z f : FormDomain) =
      inner ℂ (meanZeroCuspEmbedding (cuspMeanZeroFormPart v)) f :=
    cuspMeanZeroPencilSolution_equation hz f (cuspMeanZeroFormPart v)
  have h : formPairing z
      ((cuspMeanZeroFormPart v : FormDomain) + (cuspScalarFormPart v : FormDomain))
      (cuspMeanZeroPencilSolution z f : FormDomain) =
      inner ℂ
        (formEmbedding
          ((cuspMeanZeroFormPart v : FormDomain) + (cuspScalarFormPart v : FormDomain)))
        (f - cuspScalarProjection f) := by
    rw [formPairing_add_left, formPairing_scalar_meanZero, he, add_zero]
    simp only [map_add, inner_add_left, ← meanZeroCuspEmbedding_apply,
      ← scalarCuspEmbedding_apply, meanZero_source_projection_pairing,
      scalar_source_projection_pairing, add_zero]
  simpa only [hs] using h

theorem cuspMeanZeroPencilSolution_traceZero_equation {z : ℂ}
    (hz : IsUnit (cuspMeanZeroPencil z)) (f : ModularHilbert)
    (v : FormDomain) (hv : cuspAverageTrace v = 0) :
    inner ℂ (formGradient v)
        (formGradient (cuspMeanZeroPencilSolution z f : FormDomain)) -
      z * inner ℂ (formEmbedding v)
        (formEmbedding (cuspMeanZeroPencilSolution z f : FormDomain)) =
      inner ℂ (formEmbedding v) (f - cuspScalarProjection f) :=
  cuspMeanZeroPencilSolution_traceZero_formPairing hz f v hv

theorem cuspMeanZeroPencilSolution_quarter_traceZero_equation
    (f : ModularHilbert) (v : FormDomain) (hv : cuspAverageTrace v = 0) :
    inner ℂ (formGradient v)
        (formGradient (cuspMeanZeroPencilSolution (1 / 4) f : FormDomain)) -
      (1 / 4 : ℂ) * inner ℂ (formEmbedding v)
        (formEmbedding (cuspMeanZeroPencilSolution (1 / 4) f : FormDomain)) =
      inner ℂ (formEmbedding v) (f - cuspScalarProjection f) :=
  cuspMeanZeroPencilSolution_traceZero_equation
    cuspMeanZeroPencil_isUnit_quarter f v hv

theorem cuspMeanZeroPencilSolution_quarter_highCompact_equation
    (f : ModularHilbert) (ψ : ℂ → ℂ) (hψ : ContDiff ℝ ∞ ψ)
    (hc : HasCompactSupport ψ) (hs : tsupport ψ ⊆ UpperHalfPlane.upperHalfPlaneSet)
    (hhigh : tsupport ψ ⊆ {z : ℂ | 1 < z.im}) :
    inner ℂ (formGradient (coreForm (periodizedUpperCore ψ hψ hc hs)))
        (formGradient (cuspMeanZeroPencilSolution (1 / 4) f : FormDomain)) -
      (1 / 4 : ℂ) * inner ℂ
        (formEmbedding (coreForm (periodizedUpperCore ψ hψ hc hs)))
        (formEmbedding (cuspMeanZeroPencilSolution (1 / 4) f : FormDomain)) =
      inner ℂ (formEmbedding (coreForm (periodizedUpperCore ψ hψ hc hs)))
        (f - cuspScalarProjection f) :=
  cuspMeanZeroPencilSolution_quarter_traceZero_equation f _
    (CuspHighCompactTrace.cuspAverageTrace_periodizedUpperCore_of_high_support
      ψ hψ hc hs hhigh)

end GapFamily.Analytic.CuspConstrainedWeakEquation
