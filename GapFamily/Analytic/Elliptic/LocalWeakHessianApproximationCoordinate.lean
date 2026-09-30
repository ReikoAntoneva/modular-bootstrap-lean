import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-!
# Exact pair coordinates for weak Hessian approximation

The two real coordinate models have the same ordinary Lebesgue measure. Smooth
first and mixed second derivatives commute with their linear identification.
-/

noncomputable section

namespace GapFamily.Analytic.LocalWeakHessian

open Set MeasureTheory
open scoped ContDiff ENNReal

/-- The coordinate pair `(x,y)` as the two-entry vector `![x,y]`. -/
def pairToVec : (ℝ × ℝ) ≃L[ℝ] (Fin 2 → ℝ) :=
  (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm

@[simp] theorem pairToVec_apply (q : ℝ × ℝ) : pairToVec q = ![q.1, q.2] := rfl

@[simp] theorem pairToVec_symm_apply (v : Fin 2 → ℝ) : pairToVec.symm v = (v 0, v 1) := rfl

theorem pairToVec_measurePreserving : MeasurePreserving pairToVec volume volume :=
  (volume_preserving_finTwoArrow ℝ).symm MeasurableEquiv.finTwoArrow

theorem pairToVec_measurePreserving_restrict_preimage (U : Set (Fin 2 → ℝ)) :
    MeasurePreserving pairToVec (volume.restrict (pairToVec ⁻¹' U)) (volume.restrict U) :=
  pairToVec_measurePreserving.restrict_preimage_emb
    pairToVec.toHomeomorph.toMeasurableEquiv.measurableEmbedding U

/-- Exact ordinary restricted Lp seminorm, including arbitrary sets and fields. -/
theorem eLpNorm_comp_pairToVec {E : Type*} [NormedAddCommGroup E]
    (U : Set (Fin 2 → ℝ)) (f : (Fin 2 → ℝ) → E) (p : ℝ≥0∞) :
    eLpNorm (fun q => f (pairToVec q)) p (volume.restrict (pairToVec ⁻¹' U)) =
      eLpNorm f p (volume.restrict U) := by
  rw [← (pairToVec_measurePreserving_restrict_preimage U).map_eq]
  exact pairToVec.toHomeomorph.toMeasurableEquiv.measurableEmbedding.eLpNorm_map_measure.symm

theorem memLp_comp_pairToVec_iff {E : Type*} [NormedAddCommGroup E]
    (U : Set (Fin 2 → ℝ)) (f : (Fin 2 → ℝ) → E) (p : ℝ≥0∞) :
    MemLp (fun q => f (pairToVec q)) p (volume.restrict (pairToVec ⁻¹' U)) ↔
      MemLp f p (volume.restrict U) := by
  rw [← (pairToVec_measurePreserving_restrict_preimage U).map_eq]
  exact pairToVec.toHomeomorph.toMeasurableEquiv.memLp_map_measure_iff.symm

@[simp] theorem pairToVec_basis (i : Fin 2) :
    pairToVec (![(1, 0), (0, 1)] i) = Pi.single i (1 : ℝ) := by
  fin_cases i <;> ext j <;> fin_cases j <;> rfl

/-- Both first coordinate directions have exactly the corresponding vector derivative. -/
theorem fderiv_comp_pairToVec_basis {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : (Fin 2 → ℝ) → E} (hf : ContDiff ℝ ∞ f) (q : ℝ × ℝ) (i : Fin 2) :
    fderiv ℝ (fun p => f (pairToVec p)) q (![(1, 0), (0, 1)] i) =
      fderiv ℝ f (pairToVec q) (Pi.single i (1 : ℝ)) := by
  change fderiv ℝ (f ∘ pairToVec) q _ = _
  rw [fderiv_comp q (hf.differentiable (by simp) _) pairToVec.differentiableAt]
  simp only [ContinuousLinearMap.comp_apply, pairToVec.fderiv, pairToVec_basis,
    ContinuousLinearEquiv.coe_coe]

/-- Mixed derivatives retain their order through the pair-to-vector coordinate map. -/
theorem second_fderiv_comp_pairToVec {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : (Fin 2 → ℝ) → E} (hf : ContDiff ℝ ∞ f) (q : ℝ × ℝ) (i j : Fin 2) :
    fderiv ℝ (fun p => fderiv ℝ (fun p' => f (pairToVec p')) p (![(1, 0), (0, 1)] i))
        q (![(1, 0), (0, 1)] j) =
      fderiv ℝ (fun v => fderiv ℝ f v (Pi.single i (1 : ℝ)))
        (pairToVec q) (Pi.single j (1 : ℝ)) := by
  have heq : (fun p => fderiv ℝ (fun p' => f (pairToVec p')) p (![(1, 0), (0, 1)] i)) =
      (fun p => fderiv ℝ f (pairToVec p) (Pi.single i (1 : ℝ))) :=
    funext fun p => fderiv_comp_pairToVec_basis hf p i
  rw [heq]
  exact fderiv_comp_pairToVec_basis
    ((hf.fderiv_right (by simp)).clm_apply contDiff_const) q j

end GapFamily.Analytic.LocalWeakHessian
