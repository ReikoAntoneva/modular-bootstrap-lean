import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Centered real coordinates for local modular elliptic regularity

The ordinary complex plane is identified with real coordinate pairs by a smooth,
volume-preserving affine chart centered at any prescribed point. The identities
below transport actual derivatives and restricted Lp membership without a Jacobian
factor.
-/

noncomputable section

namespace GapFamily.Analytic

open MeasureTheory
open scoped ContDiff ENNReal

/-- The real coordinate map `(x,y) ↦ x + y I`. -/
def ellipticChartLinear : (Fin 2 → ℝ) ≃L[ℝ] ℂ :=
  Complex.basisOneI.equivFun.toContinuousLinearEquiv.symm

@[simp] theorem ellipticChartLinear_apply (v : Fin 2 → ℝ) :
    ellipticChartLinear v = (v 0 : ℂ) + (v 1 : ℂ) * Complex.I := rfl

@[simp] theorem ellipticChartLinear_symm_apply (w : ℂ) :
    ellipticChartLinear.symm w = ![w.re, w.im] := rfl

/-- The affine real chart centered at `z`. -/
def ellipticChart (z : ℂ) : (Fin 2 → ℝ) ≃ₜ ℂ :=
  ellipticChartLinear.toHomeomorph.trans (Homeomorph.addLeft z)

@[simp] theorem ellipticChart_apply (z : ℂ) (v : Fin 2 → ℝ) :
    ellipticChart z v = z + ellipticChartLinear v := rfl

@[simp] theorem ellipticChart_re (z : ℂ) (v : Fin 2 → ℝ) :
    (ellipticChart z v).re = z.re + v 0 := by
  simp

@[simp] theorem ellipticChart_im (z : ℂ) (v : Fin 2 → ℝ) :
    (ellipticChart z v).im = z.im + v 1 := by
  simp

theorem ellipticChart_symm_apply (z w : ℂ) :
    (ellipticChart z).symm w = ellipticChartLinear.symm (w - z) := by
  change ellipticChartLinear.symm (-z + w) = ellipticChartLinear.symm (w - z)
  rw [sub_eq_add_neg, add_comm]

@[simp] theorem ellipticChart_symm_apply_zero (z w : ℂ) :
    (ellipticChart z).symm w 0 = w.re - z.re := by
  simp [ellipticChart_symm_apply]

@[simp] theorem ellipticChart_symm_apply_one (z w : ℂ) :
    (ellipticChart z).symm w 1 = w.im - z.im := by
  simp [ellipticChart_symm_apply]

@[simp] theorem ellipticChart_zero (z : ℂ) : ellipticChart z 0 = z := by
  simp

@[simp] theorem ellipticChart_symm_center (z : ℂ) : (ellipticChart z).symm z = 0 := by
  rw [ellipticChart_symm_apply, sub_self, map_zero]

theorem ellipticChart_contDiff (z : ℂ) : ContDiff ℝ ∞ (ellipticChart z) :=
  contDiff_const.add ellipticChartLinear.contDiff

theorem ellipticChart_symm_contDiff (z : ℂ) : ContDiff ℝ ∞ (ellipticChart z).symm := by
  change ContDiff ℝ ∞ (fun w => ellipticChartLinear.symm (-z + w))
  exact ellipticChartLinear.symm.contDiff.comp (contDiff_const.add contDiff_id)

theorem ellipticChartLinear_measurePreserving :
    MeasurePreserving ellipticChartLinear volume volume :=
  Complex.volume_preserving_equiv_pi.symm Complex.measurableEquivPi

theorem ellipticChart_measurePreserving (z : ℂ) :
    MeasurePreserving (ellipticChart z) volume volume :=
  (measurePreserving_add_left volume z).comp ellipticChartLinear_measurePreserving

theorem ellipticChart_symm_measurePreserving (z : ℂ) :
    MeasurePreserving (ellipticChart z).symm volume volume :=
  (ellipticChart_measurePreserving z).symm (ellipticChart z).toMeasurableEquiv

@[simp] theorem ellipticChartLinear_basis_zero :
    ellipticChartLinear (Pi.single (0 : Fin 2) (1 : ℝ)) = 1 := by
  simp

@[simp] theorem ellipticChartLinear_basis_one :
    ellipticChartLinear (Pi.single (1 : Fin 2) (1 : ℝ)) = Complex.I := by
  simp

@[simp] theorem ellipticChartLinear_symm_one :
    ellipticChartLinear.symm 1 = Pi.single (0 : Fin 2) (1 : ℝ) := by
  apply ellipticChartLinear.injective
  simp

@[simp] theorem ellipticChartLinear_symm_I :
    ellipticChartLinear.symm Complex.I = Pi.single (1 : Fin 2) (1 : ℝ) := by
  apply ellipticChartLinear.injective
  simp

theorem ellipticChartLinear_basis (j : Fin 2) :
    ellipticChartLinear (Pi.single j (1 : ℝ)) = ![1, Complex.I] j := by
  fin_cases j <;> simp

theorem ellipticChart_hasFDerivAt (z : ℂ) (v : Fin 2 → ℝ) :
    HasFDerivAt (ellipticChart z) ellipticChartLinear.toContinuousLinearMap v :=
  (ellipticChartLinear.hasFDerivAt (x := v)).const_add z

@[simp] theorem ellipticChart_fderiv (z : ℂ) (v : Fin 2 → ℝ) :
    fderiv ℝ (ellipticChart z) v = ellipticChartLinear.toContinuousLinearMap :=
  (ellipticChart_hasFDerivAt z v).fderiv

theorem ellipticChart_symm_hasFDerivAt (z w : ℂ) :
    HasFDerivAt (ellipticChart z).symm ellipticChartLinear.symm.toContinuousLinearMap w := by
  change HasFDerivAt (fun w => ellipticChartLinear.symm (-z + w)) _ w
  simpa using (ellipticChartLinear.symm.hasFDerivAt (x := -z + w)).comp w
    ((hasFDerivAt_id w).const_add (-z))

@[simp] theorem ellipticChart_symm_fderiv (z w : ℂ) :
    fderiv ℝ (ellipticChart z).symm w = ellipticChartLinear.symm.toContinuousLinearMap :=
  (ellipticChart_symm_hasFDerivAt z w).fderiv

@[simp] theorem ellipticChart_fderiv_basis_zero (z : ℂ) (v : Fin 2 → ℝ) :
    fderiv ℝ (ellipticChart z) v (Pi.single (0 : Fin 2) (1 : ℝ)) = 1 := by
  simp

@[simp] theorem ellipticChart_fderiv_basis_one (z : ℂ) (v : Fin 2 → ℝ) :
    fderiv ℝ (ellipticChart z) v (Pi.single (1 : Fin 2) (1 : ℝ)) = Complex.I := by
  simp

@[simp] theorem ellipticChart_symm_fderiv_one (z w : ℂ) :
    fderiv ℝ (ellipticChart z).symm w 1 = Pi.single (0 : Fin 2) (1 : ℝ) := by
  rw [ellipticChart_symm_fderiv]
  exact ellipticChartLinear_symm_one

@[simp] theorem ellipticChart_symm_fderiv_I (z w : ℂ) :
    fderiv ℝ (ellipticChart z).symm w Complex.I = Pi.single (1 : Fin 2) (1 : ℝ) := by
  rw [ellipticChart_symm_fderiv]
  exact ellipticChartLinear_symm_I

theorem ellipticChart_fderiv_basis (z : ℂ) (v : Fin 2 → ℝ) (j : Fin 2) :
    fderiv ℝ (ellipticChart z) v (Pi.single j (1 : ℝ)) = ![1, Complex.I] j := by
  rw [ellipticChart_fderiv]
  exact ellipticChartLinear_basis j

theorem ellipticChart_symm_fderiv_basis (z w : ℂ) (j : Fin 2) :
    fderiv ℝ (ellipticChart z).symm w (![1, Complex.I] j) = Pi.single j (1 : ℝ) := by
  fin_cases j
  · exact ellipticChart_symm_fderiv_one z w
  · exact ellipticChart_symm_fderiv_I z w

/-- Restriction transport holds even for arbitrary sets, using the measurable embedding. -/
theorem ellipticChart_measurePreserving_restrict_preimage (z : ℂ) (K : Set ℂ) :
    MeasurePreserving (ellipticChart z)
      (volume.restrict (ellipticChart z ⁻¹' K)) (volume.restrict K) :=
  (ellipticChart_measurePreserving z).restrict_preimage_emb
    (ellipticChart z).toMeasurableEquiv.measurableEmbedding K

theorem ellipticChart_measurePreserving_restrict_image (z : ℂ) (S : Set (Fin 2 → ℝ)) :
    MeasurePreserving (ellipticChart z)
      (volume.restrict S) (volume.restrict (ellipticChart z '' S)) :=
  (ellipticChart_measurePreserving z).restrict_image_emb
    (ellipticChart z).toMeasurableEquiv.measurableEmbedding S

theorem ellipticChart_symm_measurePreserving_restrict_image
    (z : ℂ) (S : Set (Fin 2 → ℝ)) :
    MeasurePreserving (ellipticChart z).symm
      (volume.restrict (ellipticChart z '' S)) (volume.restrict S) :=
  (ellipticChart_measurePreserving_restrict_image z S).symm
    (ellipticChart z).toMeasurableEquiv

/-- Ordinary set integrals transport with no Jacobian factor. -/
theorem integral_ellipticChart_image {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (z : ℂ) (S : Set (Fin 2 → ℝ)) (f : ℂ → E) :
    (∫ w in ellipticChart z '' S, f w) = ∫ v in S, f (ellipticChart z v) :=
  ((ellipticChart_measurePreserving_restrict_image z S).integral_comp
    (ellipticChart z).toMeasurableEquiv.measurableEmbedding f).symm

/-- Exact restricted Lp pullback, with no regularity condition on the set or field. -/
theorem memLp_comp_ellipticChart_iff {E : Type*} [NormedAddCommGroup E]
    (z : ℂ) (K : Set ℂ) (f : ℂ → E) (p : ℝ≥0∞) :
    MemLp (fun v => f (ellipticChart z v)) p (volume.restrict (ellipticChart z ⁻¹' K)) ↔
      MemLp f p (volume.restrict K) := by
  rw [← (ellipticChart_measurePreserving_restrict_preimage z K).map_eq]
  exact (ellipticChart z).toMeasurableEquiv.memLp_map_measure_iff.symm

/-- Exact Lp pullback from the image of any coordinate domain. -/
theorem memLp_comp_ellipticChart_image_iff {E : Type*} [NormedAddCommGroup E]
    (z : ℂ) (S : Set (Fin 2 → ℝ)) (f : ℂ → E) (p : ℝ≥0∞) :
    MemLp (fun v => f (ellipticChart z v)) p (volume.restrict S) ↔
      MemLp f p (volume.restrict (ellipticChart z '' S)) := by
  rw [← (ellipticChart_measurePreserving_restrict_image z S).map_eq]
  exact (ellipticChart z).toMeasurableEquiv.memLp_map_measure_iff.symm

end GapFamily.Analytic
