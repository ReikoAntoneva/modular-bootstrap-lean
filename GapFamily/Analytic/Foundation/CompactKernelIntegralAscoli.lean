import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Topology.ContinuousMap.Compact

/-!
# Compact operator from a continuous inner-product field

The field supplies both the uniform bound and the common modulus of continuity. Arzelà–Ascoli
then proves compactness of its actual inner-product operator, without an equicontinuity input.
-/

noncomputable section

open Set Metric
open scoped InnerProductSpace Topology BoundedContinuousFunction

namespace GapFamily.Analytic

variable {K H : Type*} [TopologicalSpace K] [CompactSpace K]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Pairing against a continuous compactly parametrized field, linear in the input vector. -/
def innerFieldOperator (v : C(K, H)) : H →L[ℂ] C(K, ℂ) :=
  ({ toFun := fun f => ⟨fun x => inner ℂ (v x) f, v.continuous.inner continuous_const⟩
     map_add' := by intros; ext; simp [inner_add_right]
     map_smul' := by intros; ext; simp [inner_smul_right] } : H →ₗ[ℂ] C(K, ℂ)).mkContinuous ‖v‖ (by
    intro f
    refine (ContinuousMap.norm_le _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))).2 ?_
    intro x
    exact (norm_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_right (v.norm_coe_le_norm x) (norm_nonneg _)))

@[simp]
theorem innerFieldOperator_apply (v : C(K, H)) (f : H) (x : K) :
    innerFieldOperator v f x = inner ℂ (v x) f := rfl

theorem norm_innerFieldOperator_le (v : C(K, H)) : ‖innerFieldOperator v‖ ≤ ‖v‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) ?_
  intro f
  refine (ContinuousMap.norm_le _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))).2 ?_
  intro x
  exact (norm_inner_le_norm _ _).trans
    (mul_le_mul_of_nonneg_right (v.norm_coe_le_norm x) (norm_nonneg _))

/-- On the unit ball, the field's variation bounds every paired function's variation. -/
theorem innerFieldOperator_dist_le (v : C(K, H)) {f : H} (hf : ‖f‖ ≤ 1) (x y : K) :
    dist (innerFieldOperator v f x) (innerFieldOperator v f y) ≤ ‖v x - v y‖ := by
  rw [dist_eq_norm, innerFieldOperator_apply, innerFieldOperator_apply, ← inner_sub_left]
  exact (norm_inner_le_norm _ _).trans
    (by simpa using mul_le_mul_of_nonneg_left hf (norm_nonneg (v x - v y)))

/-- The actual image of the unit ball has compact closure in the uniform norm. -/
theorem isCompact_closure_innerFieldOperator_image_closedBall (v : C(K, H)) :
    IsCompact (closure (innerFieldOperator v '' closedBall 0 1)) := by
  let e := ContinuousMap.linearIsometryBoundedOfCompact K ℂ ℂ
  let T : H →L[ℂ] K →ᵇ ℂ := e.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (innerFieldOperator v)
  have hTc : IsCompact (closure (T '' closedBall 0 1)) := by
    refine BoundedContinuousFunction.arzela_ascoli (closedBall 0 ‖v‖)
      (isCompact_closedBall _ _) (T '' closedBall 0 1) ?_ ?_
    · rintro g x ⟨f, hf, rfl⟩
      have hf' : ‖f‖ ≤ 1 := by simpa using hf
      change dist (inner ℂ (v x) f) 0 ≤ ‖v‖
      rw [dist_zero_right]
      calc
        ‖inner ℂ (v x) f‖ ≤ ‖v x‖ * ‖f‖ := norm_inner_le_norm _ _
        _ ≤ ‖v x‖ * 1 := mul_le_mul_of_nonneg_left hf' (norm_nonneg _)
        _ ≤ ‖v‖ := by simpa using v.norm_coe_le_norm x
    · intro x
      refine Metric.equicontinuousAt_of_continuity_modulus
        (fun y => ‖v x - v y‖) ?_ _ (Filter.Eventually.of_forall ?_)
      · simpa only [ContinuousAt, Pi.sub_apply, sub_self, norm_zero] using
          ((continuous_const.sub v.continuous).norm.continuousAt :
          ContinuousAt (fun y => ‖v x - v y‖) x)
      · intro y g
        rcases g.property with ⟨f, hf, hfg⟩
        have hf' : ‖f‖ ≤ 1 := by simpa using hf
        change dist (g.val x) (g.val y) ≤ _
        rw [← hfg]
        exact innerFieldOperator_dist_le v hf' x y
  have hT : IsCompactOperator T :=
    (isCompactOperator_iff_isCompact_closure_image_closedBall T.toLinearMap
      (show (0 : ℝ) < 1 by norm_num)).2 hTc
  have hV : IsCompactOperator (innerFieldOperator v) := by
    convert hT.clm_comp e.symm.toContinuousLinearEquiv.toContinuousLinearMap using 1
    ext f x
    simp [T, e]
  exact hV.isCompact_closure_image_closedBall (f := (innerFieldOperator v).toLinearMap) 1

/-- A continuous inner-product field on a compact space defines a compact operator. -/
theorem isCompactOperator_innerFieldOperator (v : C(K, H)) :
    IsCompactOperator (innerFieldOperator v) :=
  (isCompactOperator_iff_isCompact_closure_image_closedBall
    (innerFieldOperator v).toLinearMap (show (0 : ℝ) < 1 by norm_num)).2
    (isCompact_closure_innerFieldOperator_image_closedBall v)

end GapFamily.Analytic
