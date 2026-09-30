import GapFamily.Quadrature.Midpoint
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.MonotoneContinuity
import Mathlib.Topology.ContinuousMap.Compact

/-!
# Quantiles of positive continuous densities

The cumulative distribution is the actual interval integral. Its inverse is
constructed from strict monotonicity and the intermediate value theorem.
-/

open Set MeasureTheory
open scoped Topology

namespace GapFamily.Quadrature

/-- Cumulative mass measured from the left endpoint. -/
noncomputable def cumulative (ρ : ℝ → ℝ) (a x : ℝ) : ℝ :=
  ∫ t in a..x, ρ t

@[simp] theorem cumulative_left (ρ : ℝ → ℝ) (a : ℝ) : cumulative ρ a a = 0 := by
  simp [cumulative]

/-- Positive continuous density gives a strictly increasing cumulative mass. -/
theorem cumulative_strictMonoOn {ρ : ℝ → ℝ} {a b : ℝ}
    (hρ : ContinuousOn ρ (Icc a b)) (hpos : ∀ x ∈ Icc a b, 0 < ρ x) :
    StrictMonoOn (cumulative ρ a) (Icc a b) := by
  intro x hx y hy hxy
  have hsub : Icc x y ⊆ Icc a b := Icc_subset_Icc hx.1 hy.2
  have hax : IntervalIntegrable ρ volume a x :=
    (hρ.mono (Icc_subset_Icc_right hx.2)).intervalIntegrable_of_Icc hx.1
  have hxyi : IntervalIntegrable ρ volume x y :=
    (hρ.mono hsub).intervalIntegrable_of_Icc hxy.le
  have hp : 0 < ∫ t in x..y, ρ t := intervalIntegral.integral_pos hxy
    (hρ.mono hsub) (fun t ht => (hpos t (hsub ⟨ht.1.le, ht.2⟩)).le)
    ⟨x, ⟨le_rfl, hxy.le⟩, hpos x hx⟩
  have hadd := intervalIntegral.integral_add_adjacent_intervals hax hxyi
  dsimp [cumulative]
  linarith

/-- Continuity of cumulative mass on the density's interval. -/
theorem cumulative_continuousOn {ρ : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hρ : ContinuousOn ρ (Icc a b)) :
    ContinuousOn (cumulative ρ a) (Icc a b) := by
  change ContinuousOn (fun x => ∫ t in a..x, ρ t) _
  simpa only [uIcc_of_le hab] using
    intervalIntegral.continuousOn_primitive_interval'
      (hρ.intervalIntegrable_of_Icc hab) left_mem_uIcc

/-- Unit total mass makes the cumulative distribution map onto the unit interval. -/
theorem cumulative_surjOn {ρ : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hρ : ContinuousOn ρ (Icc a b)) (hmass : ∫ t in a..b, ρ t = 1) :
    SurjOn (cumulative ρ a) (Icc a b) (Icc 0 1) := by
  have h := (cumulative_continuousOn hab hρ).surjOn_Icc
    (left_mem_Icc.mpr hab) (right_mem_Icc.mpr hab)
  simpa [cumulative, hmass] using h

/-- The cumulative distribution of a positive probability density is an order
isomorphism of closed intervals; its inverse is a continuous quantile. -/
noncomputable def cumulativeOrderIso {ρ : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hρ : ContinuousOn ρ (Icc a b)) (hpos : ∀ x ∈ Icc a b, 0 < ρ x)
    (hmass : ∫ t in a..b, ρ t = 1) : Icc a b ≃o Icc (0 : ℝ) 1 := by
  have hmono := cumulative_strictMonoOn hρ hpos
  have hmap : MapsTo (cumulative ρ a) (Icc a b) (Icc 0 1) := by
    intro x hx
    constructor
    · simpa using hmono.monotoneOn (left_mem_Icc.mpr hab) hx hx.1
    · simpa only [cumulative, hmass] using
        hmono.monotoneOn hx (right_mem_Icc.mpr hab) hx.2
  let F : Icc a b → Icc (0 : ℝ) 1 := fun x => ⟨cumulative ρ a x, hmap x.property⟩
  apply StrictMono.orderIsoOfSurjective F
  · intro x y hxy
    exact hmono x.property y.property hxy
  · intro t
    obtain ⟨x, hx, heq⟩ := cumulative_surjOn hab hρ hmass t.property
    exact ⟨⟨x, hx⟩, Subtype.ext heq⟩

@[simp] theorem cumulativeOrderIso_apply {ρ : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hρ : ContinuousOn ρ (Icc a b)) (hpos : ∀ x ∈ Icc a b, 0 < ρ x)
    (hmass : ∫ t in a..b, ρ t = 1) (x : Icc a b) :
    (cumulativeOrderIso hab hρ hpos hmass x : ℝ) = cumulative ρ a x := rfl

/-- Constant extension outside `[0,1]` gives a real function for integration APIs. -/
noncomputable def quantile {ρ : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hρ : ContinuousOn ρ (Icc a b)) (hpos : ∀ x ∈ Icc a b, 0 < ρ x)
    (hmass : ∫ t in a..b, ρ t = 1) (t : ℝ) : ℝ :=
  (cumulativeOrderIso hab hρ hpos hmass).symm (projIcc 0 1 zero_le_one t)

theorem quantile_continuous {ρ : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hρ : ContinuousOn ρ (Icc a b)) (hpos : ∀ x ∈ Icc a b, 0 < ρ x)
    (hmass : ∫ t in a..b, ρ t = 1) :
    Continuous (quantile hab hρ hpos hmass) :=
  continuous_subtype_val.comp
    ((cumulativeOrderIso hab hρ hpos hmass).symm.continuous.comp continuous_projIcc)

theorem quantile_monotone {ρ : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hρ : ContinuousOn ρ (Icc a b)) (hpos : ∀ x ∈ Icc a b, 0 < ρ x)
    (hmass : ∫ t in a..b, ρ t = 1) :
    Monotone (quantile hab hρ hpos hmass) := by
  intro x y hxy
  exact (cumulativeOrderIso hab hρ hpos hmass).symm.monotone (monotone_projIcc _ hxy)

theorem quantile_mem {ρ : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hρ : ContinuousOn ρ (Icc a b)) (hpos : ∀ x ∈ Icc a b, 0 < ρ x)
    (hmass : ∫ t in a..b, ρ t = 1) (t : ℝ) :
    quantile hab hρ hpos hmass t ∈ Icc a b :=
  Subtype.property _

theorem cumulative_quantile {ρ : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hρ : ContinuousOn ρ (Icc a b)) (hpos : ∀ x ∈ Icc a b, 0 < ρ x)
    (hmass : ∫ t in a..b, ρ t = 1) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    cumulative ρ a (quantile hab hρ hpos hmass t) = t := by
  have h := congrArg Subtype.val
    ((cumulativeOrderIso hab hρ hpos hmass).apply_symm_apply ⟨t, ht⟩)
  simpa only [cumulativeOrderIso_apply, quantile, projIcc_of_mem _ ht] using h

theorem quantile_cumulative {ρ : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hρ : ContinuousOn ρ (Icc a b)) (hpos : ∀ x ∈ Icc a b, 0 < ρ x)
    (hmass : ∫ t in a..b, ρ t = 1) {x : ℝ} (hx : x ∈ Icc a b) :
    quantile hab hρ hpos hmass (cumulative ρ a x) = x := by
  have heq := (cumulativeOrderIso hab hρ hpos hmass).symm_apply_apply ⟨x, hx⟩
  have hmem := ((cumulativeOrderIso hab hρ hpos hmass) ⟨x, hx⟩).property
  change cumulative ρ a x ∈ Icc (0 : ℝ) 1 at hmem
  dsimp [quantile]
  rw [projIcc_of_mem _ hmem]
  exact congrArg Subtype.val heq

@[simp] theorem quantile_zero {ρ : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hρ : ContinuousOn ρ (Icc a b)) (hpos : ∀ x ∈ Icc a b, 0 < ρ x)
    (hmass : ∫ t in a..b, ρ t = 1) :
    quantile hab hρ hpos hmass 0 = a := by
  simpa only [cumulative_left] using
    quantile_cumulative hab hρ hpos hmass (left_mem_Icc.mpr hab)

@[simp] theorem quantile_one {ρ : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hρ : ContinuousOn ρ (Icc a b)) (hpos : ∀ x ∈ Icc a b, 0 < ρ x)
    (hmass : ∫ t in a..b, ρ t = 1) :
    quantile hab hρ hpos hmass 1 = b := by
  simpa only [cumulative, hmass] using
    quantile_cumulative hab hρ hpos hmass (right_mem_Icc.mpr hab)

theorem quantile_strictMonoOn {ρ : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hρ : ContinuousOn ρ (Icc a b)) (hpos : ∀ x ∈ Icc a b, 0 < ρ x)
    (hmass : ∫ t in a..b, ρ t = 1) :
    StrictMonoOn (quantile hab hρ hpos hmass) (Icc (0 : ℝ) 1) := by
  intro x hx y hy hxy
  dsimp [quantile]
  rw [projIcc_of_mem _ hx, projIcc_of_mem _ hy]
  exact (cumulativeOrderIso hab hρ hpos hmass).symm.strictMono
      (show (⟨x, hx⟩ : Icc (0 : ℝ) 1) < ⟨y, hy⟩ from hxy)

/-- Interior probability coordinates give strictly interior spatial nodes. -/
theorem quantile_mem_Ioo {ρ : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hρ : ContinuousOn ρ (Icc a b)) (hpos : ∀ x ∈ Icc a b, 0 < ρ x)
    (hmass : ∫ t in a..b, ρ t = 1) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    quantile hab hρ hpos hmass t ∈ Ioo a b := by
  have hmono := quantile_strictMonoOn hab hρ hpos hmass
  constructor
  · simpa only [quantile_zero] using
      hmono (left_mem_Icc.mpr zero_le_one) (Ioo_subset_Icc_self ht) ht.1
  · simpa only [quantile_one] using
      hmono (Ioo_subset_Icc_self ht) (right_mem_Icc.mpr zero_le_one) ht.2

private lemma affine_mem {a b x t : ℝ} (hx : x ∈ Icc a b) (ht : t ∈ Icc (0 : ℝ) 1) :
    (x - a) * t + a ∈ Icc a b := by
  constructor
  · nlinarith [mul_nonneg (sub_nonneg.mpr hx.1) ht.1]
  · have := mul_le_mul_of_nonneg_left ht.2 (sub_nonneg.mpr hx.1)
    nlinarith [hx.2]

private noncomputable def integralUnit (f : C(Icc (0 : ℝ) 1, ℝ)) : ℝ :=
  ∫ t in (0 : ℝ)..1, f (projIcc 0 1 zero_le_one t)

private theorem continuous_integralUnit : Continuous integralUnit := by
  apply LipschitzWith.continuous (K := 1)
  apply LipschitzWith.of_dist_le_mul
  intro f g
  change dist (integralUnit f) (integralUnit g) ≤ (1 : ℝ) * dist f g
  simp only [dist_eq_norm, integralUnit, one_mul]
  have hfi : IntervalIntegrable (fun t => f (projIcc 0 1 zero_le_one t)) volume 0 1 :=
    (f.continuous.comp continuous_projIcc).intervalIntegrable _ _
  have hgi : IntervalIntegrable (fun t => g (projIcc 0 1 zero_le_one t)) volume 0 1 :=
    (g.continuous.comp continuous_projIcc).intervalIntegrable _ _
  rw [← intervalIntegral.integral_sub hfi hgi]
  simpa only [sub_zero, abs_one, mul_one] using
    (intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1)
      (f := fun t => f (projIcc 0 1 zero_le_one t) - g (projIcc 0 1 zero_le_one t))
      (fun t _ => (f - g).norm_coe_le_norm _))

/-- Joint continuity of the actual cumulative integral, including both endpoints.
No compactness assumption on the parameter space is needed. -/
theorem cumulative_joint_continuous {P : Type*} [TopologicalSpace P]
    {a b : ℝ} (density : P → ℝ → ℝ)
    (hdensity : ContinuousOn (Function.uncurry density) (univ ×ˢ Icc a b)) :
    Continuous (fun q : P × Icc a b => ∫ t in a..(q.2 : ℝ), density q.1 t) := by
  let F : (P × Icc a b) → C(Icc (0 : ℝ) 1, ℝ) := fun q =>
    ⟨fun t => density q.1 (((q.2 : ℝ) - a) * (t : ℝ) + a), by
      change Continuous (Function.uncurry density ∘ (fun t : Icc (0 : ℝ) 1 =>
        (q.1, ((q.2 : ℝ) - a) * (t : ℝ) + a)))
      apply hdensity.comp_continuous
      · fun_prop
      · intro t
        exact ⟨mem_univ _, affine_mem q.2.property t.property⟩⟩
  have hF : Continuous F := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    change Continuous (Function.uncurry density ∘ (fun q : (P × Icc a b) × Icc (0 : ℝ) 1 =>
      (q.1.1, ((q.1.2 : ℝ) - a) * (q.2 : ℝ) + a)))
    apply hdensity.comp_continuous
    · fun_prop
    · intro q
      exact ⟨mem_univ _, affine_mem q.1.2.property q.2.property⟩
  have hC : Continuous (fun q : P × Icc a b => ((q.2 : ℝ) - a) * integralUnit (F q)) :=
    ((continuous_subtype_val.comp continuous_snd).sub continuous_const).mul
      (continuous_integralUnit.comp hF)
  convert hC using 1
  ext q
  have heq : integralUnit (F q) = ∫ t in (0 : ℝ)..1,
      density q.1 (((q.2 : ℝ) - a) * t + a) := by
    apply intervalIntegral.integral_congr
    intro t ht
    simp only [uIcc_of_le zero_le_one] at ht
    simp only [F, ContinuousMap.coe_mk, projIcc_of_mem zero_le_one ht]
  rw [heq]
  simpa only [smul_eq_mul, mul_zero, zero_add, mul_one, sub_add_cancel] using
    (intervalIntegral.smul_integral_comp_mul_add (density q.1) ((q.2 : ℝ) - a) a (a := 0) (b := 1)).symm

/-- Restrict a continuous density family to one parameter. -/
theorem density_slice_continuousOn {P : Type*} [TopologicalSpace P]
    {a b : ℝ} {ρ : P → ℝ → ℝ}
    (hρ : ContinuousOn (Function.uncurry ρ) (univ ×ˢ Icc a b)) (p : P) :
    ContinuousOn (ρ p) (Icc a b) :=
  hρ.comp (continuous_const.prodMk continuous_id).continuousOn (fun _ hx => ⟨mem_univ _, hx⟩)

/-- On a compact Hausdorff parameter space, the actual inverse cumulative maps
vary jointly continuously with the parameter and probability coordinate. -/
theorem quantile_joint_continuous {P : Type*} [TopologicalSpace P] [CompactSpace P] [T2Space P]
    {a b : ℝ} {ρ : P → ℝ → ℝ} (hab : a ≤ b)
    (hρ : ContinuousOn (Function.uncurry ρ) (univ ×ˢ Icc a b))
    (hpos : ∀ p x, x ∈ Icc a b → 0 < ρ p x)
    (hmass : ∀ p, ∫ t in a..b, ρ p t = 1) :
    Continuous (fun q : P × ℝ =>
      quantile hab (density_slice_continuousOn hρ q.1) (hpos q.1) (hmass q.1) q.2) := by
  have hC := cumulative_joint_continuous ρ hρ
  let e : P × Icc a b ≃ P × Icc (0 : ℝ) 1 :=
    { toFun := fun q => (q.1, cumulativeOrderIso hab (density_slice_continuousOn hρ q.1)
        (hpos q.1) (hmass q.1) q.2)
      invFun := fun q => (q.1, (cumulativeOrderIso hab (density_slice_continuousOn hρ q.1)
        (hpos q.1) (hmass q.1)).symm q.2)
      left_inv := fun q => by dsimp; simp
      right_inv := fun q => by dsimp; simp }
  have he : Continuous e :=
    continuous_fst.prodMk (hC.subtype_mk (fun q => (e q).2.property))
  let H := e.toHomeomorphOfContinuousClosed he he.isClosedMap
  exact continuous_subtype_val.comp (continuous_snd.comp
    (H.symm.continuous.comp (continuous_fst.prodMk
      ((continuous_projIcc (h := (zero_le_one : (0 : ℝ) ≤ 1))).comp continuous_snd))))


/-- The cumulative integral has derivative equal to the density in the interior. -/
theorem cumulative_hasDerivAt {ρ : ℝ → ℝ} {a b x : ℝ}
    (hρ : ContinuousOn ρ (Icc a b)) (hx : x ∈ Ioo a b) :
    HasDerivAt (cumulative ρ a) (ρ x) x := by
  have hxi : x ∈ Icc a b := Ioo_subset_Icc_self hx
  have hc : ContinuousAt ρ x := hρ.continuousAt (Icc_mem_nhds hx.1 hx.2)
  have hi : IntervalIntegrable ρ volume a x :=
    (hρ.mono (Icc_subset_Icc_right hxi.2)).intervalIntegrable_of_Icc hxi.1
  have hm : StronglyMeasurableAtFilter ρ (𝓝 x) := by
    simpa only [nhdsWithin_eq_nhds.mpr (Icc_mem_nhds hx.1 hx.2)] using
      hρ.stronglyMeasurableAtFilter_nhdsWithin (μ := volume) measurableSet_Icc x
  exact intervalIntegral.integral_hasDerivAt_right hi hm hc

theorem continuous_comp_quantile {ρ f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hρ : ContinuousOn ρ (Icc a b)) (hpos : ∀ x ∈ Icc a b, 0 < ρ x)
    (hmass : ∫ t in a..b, ρ t = 1) (hf : ContinuousOn f (Icc a b)) :
    Continuous (fun t => f (quantile hab hρ hpos hmass t)) :=
  hf.comp_continuous (quantile_continuous hab hρ hpos hmass)
    (quantile_mem hab hρ hpos hmass)

theorem intervalIntegrable_comp_quantile {ρ f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hρ : ContinuousOn ρ (Icc a b)) (hpos : ∀ x ∈ Icc a b, 0 < ρ x)
    (hmass : ∫ t in a..b, ρ t = 1) (hf : ContinuousOn f (Icc a b)) :
    IntervalIntegrable (fun t => f (quantile hab hρ hpos hmass t)) volume 0 1 :=
  (continuous_comp_quantile hab hρ hpos hmass hf).intervalIntegrable 0 1

theorem intervalIntegrable_mul_density {ρ f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hρ : ContinuousOn ρ (Icc a b)) (hf : ContinuousOn f (Icc a b)) :
    IntervalIntegrable (fun x => f x * ρ x) volume a b :=
  (hf.mul hρ).intervalIntegrable_of_Icc hab

/-- Change of variables for the constructed inverse cumulative distribution.
For continuous integrands both sides are integrable by the preceding lemmas. -/
theorem integral_quantile {ρ : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hρ : ContinuousOn ρ (Icc a b)) (hpos : ∀ x ∈ Icc a b, 0 < ρ x)
    (hmass : ∫ t in a..b, ρ t = 1) (f : ℝ → ℝ) :
    (∫ t in (0 : ℝ)..1, f (quantile hab hρ hpos hmass t)) =
      ∫ x in a..b, f x * ρ x := by
  have hc : ContinuousOn (cumulative ρ a) (uIcc a b) := by
    simpa only [uIcc_of_le hab] using cumulative_continuousOn hab hρ
  have hd : ∀ x ∈ Ioo (min a b) (max a b),
      HasDerivAt (cumulative ρ a) (ρ x) x := by
    simpa only [min_eq_left hab, max_eq_right hab] using
      (fun x hx => cumulative_hasDerivAt hρ hx)
  have hn : ∀ x ∈ Ioo (min a b) (max a b), 0 ≤ ρ x := by
    simpa only [min_eq_left hab, max_eq_right hab] using
      (fun x hx => (hpos x (Ioo_subset_Icc_self hx)).le)
  have heq := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
    (g := fun t => f (quantile hab hρ hpos hmass t)) hc hd hn
  have hr : cumulative ρ a b = 1 := hmass
  rw [cumulative_left, hr] at heq
  rw [← heq]
  apply intervalIntegral.integral_congr
  intro x hx
  have hxi : x ∈ Icc a b := by simpa only [uIcc_of_le hab] using hx
  simp only [Function.comp_apply, quantile_cumulative hab hρ hpos hmass hxi]

/-- Midpoint quantiles of an actual positive density have the sharp variation
error measured against integration with that density. -/
theorem quantile_midpoint_error {ρ f : ℝ → ℝ} {a b : ℝ} {n : ℕ} (hab : a ≤ b)
    (hρ : ContinuousOn ρ (Icc a b)) (hpos : ∀ x ∈ Icc a b, 0 < ρ x)
    (hmass : ∫ t in a..b, ρ t = 1) (hn : 0 < n)
    (hf : ContinuousOn f (Icc a b)) (hv : BoundedVariationOn f (Icc a b)) :
    |(1 / (n : ℝ)) * (∑ i ∈ Finset.range n,
        f (quantile hab hρ hpos hmass (((i : ℝ) + 1 / 2) / n))) -
        ∫ x in a..b, f x * ρ x| ≤
      (1 / (2 * (n : ℝ))) * (eVariationOn f (Icc a b)).toReal := by
  have h := monotone_transport_midpoint_error hn hf hv
    (quantile_continuous hab hρ hpos hmass).continuousOn
    ((quantile_monotone hab hρ hpos hmass).monotoneOn _)
    (fun t _ => quantile_mem hab hρ hpos hmass t)
  rw [integral_quantile hab hρ hpos hmass] at h
  exact h

/-- Each normalized midpoint-sample functional varies continuously with the
density parameter on the compact domain used by the fixed-point argument. -/
theorem quantile_midpoint_continuous {P : Type*}
    [TopologicalSpace P] [CompactSpace P] [T2Space P]
    {a b : ℝ} {ρ : P → ℝ → ℝ} {f : ℝ → ℝ} (hab : a ≤ b)
    (hρ : ContinuousOn (Function.uncurry ρ) (univ ×ˢ Icc a b))
    (hpos : ∀ p x, x ∈ Icc a b → 0 < ρ p x)
    (hmass : ∀ p, ∫ t in a..b, ρ p t = 1)
    (hf : ContinuousOn f (Icc a b)) (n : ℕ) :
    Continuous (fun p => (1 / (n : ℝ)) * ∑ i ∈ Finset.range n,
      f (quantile hab (density_slice_continuousOn hρ p) (hpos p) (hmass p)
        (((i : ℝ) + 1 / 2) / n))) := by
  have hsample (i : ℕ) : Continuous (fun p : P =>
      f (quantile hab (density_slice_continuousOn hρ p) (hpos p) (hmass p)
        (((i : ℝ) + 1 / 2) / n))) := by
    have hq := (quantile_joint_continuous (P := P) (ρ := ρ) hab hρ hpos hmass).comp
        (show Continuous (fun p : P => (p, ((i : ℝ) + 1 / 2) / n)) from
          continuous_id.prodMk continuous_const)
    exact hf.comp_continuous hq (fun p =>
      quantile_mem hab (density_slice_continuousOn hρ p) (hpos p) (hmass p) _)
  exact (continuous_finsetSum (Finset.range n) (fun i _ => hsample i)).const_mul _

end GapFamily.Quadrature
