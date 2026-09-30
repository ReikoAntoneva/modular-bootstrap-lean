import GapFamily.Quadrature.MomentMatching
import GapFamily.Quadrature.MomentFunctional
import GapFamily.Quadrature.Quantile
import GapFamily.Quadrature.DensityFamily

/-!
# Unit-node quadrature from the polynomial variation reserve

The moment error is tested in every actual polynomial direction. The final
fixed-point construction retains exactly the prescribed natural number of nodes.
-/

noncomputable section

open Set MeasureTheory Polynomial

namespace GapFamily.Quadrature

theorem unitNodeMoment_dot {k N : ℕ} (node : Fin N → ℝ) (u : MomentVector k) :
    (∑ i, u i * unitNodeMoment k node i) =
      (1 / (N : ℝ)) * ∑ j, (coordinatePolynomial u).eval (node j) := by
  simp only [unitNodeMoment, eval_coordinatePolynomial, momentCurve]
  simp_rw [← mul_div_assoc, Finset.mul_sum]
  rw [← Finset.sum_div, Finset.sum_comm]
  simp only [div_eq_mul_inv, Finset.sum_mul, one_mul]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem integral_coordinatePolynomial_mul_density {k : ℕ} {a b : ℝ}
    (hab : a ≤ b) (u : MomentVector k) {ρ : ℝ → ℝ}
    (hρ : ContinuousOn ρ (Icc a b)) :
    (∫ x in a..b, (coordinatePolynomial u).eval x * ρ x) =
      ∑ i : Fin k, u i * ∫ x in a..b, x ^ (i.val + 1) * ρ x := by
  simp only [eval_coordinatePolynomial, momentCurve, Finset.sum_mul]
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x _
    ring
  · intro i _
    exact ((continuous_const.mul (continuous_id.pow (i.val + 1))).continuousOn.mul hρ).intervalIntegrable_of_Icc hab

/-- Midpoint quantiles retain precisely the index type `Fin N`. -/
def midpointQuantileNode {N : ℕ} {a b : ℝ} {ρ : ℝ → ℝ} (hab : a ≤ b)
    (hρ : ContinuousOn ρ (Icc a b)) (hpos : ∀ x ∈ Icc a b, 0 < ρ x)
    (hmass : (∫ x in a..b, ρ x) = 1) (j : Fin N) : ℝ :=
  quantile hab hρ hpos hmass (((j.val : ℝ) + 1 / 2) / N)

theorem midpointQuantileNode_mem {N : ℕ} {a b : ℝ} {ρ : ℝ → ℝ} (hab : a ≤ b)
    (hρ : ContinuousOn ρ (Icc a b)) (hpos : ∀ x ∈ Icc a b, 0 < ρ x)
    (hmass : (∫ x in a..b, ρ x) = 1) (j : Fin N) :
    midpointQuantileNode hab hρ hpos hmass j ∈ Icc a b :=
  quantile_mem hab hρ hpos hmass _

/-- Midpoint sampling never places a quadrature node at either endpoint. -/
theorem midpointQuantileNode_mem_Ioo {N : ℕ} {a b : ℝ} {ρ : ℝ → ℝ} (hab : a ≤ b)
    (hρ : ContinuousOn ρ (Icc a b)) (hpos : ∀ x ∈ Icc a b, 0 < ρ x)
    (hmass : (∫ x in a..b, ρ x) = 1) (j : Fin N) :
    midpointQuantileNode hab hρ hpos hmass j ∈ Ioo a b := by
  apply quantile_mem_Ioo hab hρ hpos hmass
  have hN : (0 : ℝ) < N := by exact_mod_cast (Nat.zero_lt_of_lt j.isLt)
  have hj : (j.val : ℝ) + 1 ≤ N := by exact_mod_cast j.isLt
  constructor
  · exact div_pos (by positivity) hN
  · rw [div_lt_one hN]
    linarith

theorem midpointQuantileNode_continuous {P : Type*}
    [TopologicalSpace P] [CompactSpace P] [T2Space P]
    {N : ℕ} {a b : ℝ} {ρ : P → ℝ → ℝ} (hab : a ≤ b)
    (hρ : ContinuousOn (Function.uncurry ρ) (univ ×ˢ Icc a b))
    (hpos : ∀ p x, x ∈ Icc a b → 0 < ρ p x)
    (hmass : ∀ p, (∫ x in a..b, ρ p x) = 1) :
    Continuous (fun p : P => midpointQuantileNode (N := N) hab
      (density_slice_continuousOn hρ p) (hpos p) (hmass p)) := by
  apply continuous_pi
  intro j
  change Continuous (fun p : P => quantile hab (density_slice_continuousOn hρ p)
    (hpos p) (hmass p) (((j.val : ℝ) + 1 / 2) / N))
  have hq := (quantile_joint_continuous (P := P) (ρ := ρ) hab hρ hpos hmass).comp
    (show Continuous (fun p : P => (p, ((j.val : ℝ) + 1 / 2) / N)) from
      continuous_id.prodMk continuous_const)
  simpa only [Function.comp_def] using hq

/-- The constructed unit-node tuple has the required error in every polynomial direction. -/
theorem midpointQuantileNode_error {k N : ℕ} (hN : 0 < N) {a b : ℝ} {ρ : ℝ → ℝ}
    (hab : a ≤ b) (hρ : ContinuousOn ρ (Icc a b))
    (hpos : ∀ x ∈ Icc a b, 0 < ρ x) (hmass : (∫ x in a..b, ρ x) = 1)
    (z : MomentVector k)
    (hmoment : ∀ i : Fin k, (∫ x in a..b, x ^ (i.val + 1) * ρ x) = z i) :
    unitNodeMoment k (midpointQuantileNode (N := N) hab hρ hpos hmass) - z ∈
      variationReserveBall k a b (1 / (2 * (N : ℝ))) := by
  intro u
  have h := quantile_midpoint_error hab hρ hpos hmass hN
    (coordinatePolynomial u).continuousOn (polynomial_boundedVariationOn _ hab)
  rw [integral_coordinatePolynomial_mul_density hab u hρ] at h
  simp_rw [hmoment] at h
  change |∑ i, u i * (unitNodeMoment k (midpointQuantileNode hab hρ hpos hmass) i - z i)| ≤ _
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib, unitNodeMoment_dot]
  simp only [midpointQuantileNode]
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => (coordinatePolynomial u).eval
    (quantile hab hρ hpos hmass (((i : ℝ) + 1 / 2) / N)))]
  exact h

/-- Exactly the prescribed number of unit nodes realizes the finite moments.
The hypotheses concern only the original polynomial functional and its reserve;
no density, approximate quadrature, or continuous node family is assumed. -/
theorem exists_interior_unit_nodes_of_variation_reserve {k N : ℕ} {a b β : ℝ}
    (hab : a < b) (hN : 0 < N) (hβ : 1 / 2 < β)
    (L : ℝ[X] →ₗ[ℝ] ℝ) (hL : L 1 = (N : ℝ))
    (hreserve : ∀ p : ℝ[X], p.natDegree ≤ k →
      (∀ x ∈ Icc a b, 0 ≤ p.eval x) →
        β * (eVariationOn p.eval (Icc a b)).toReal ≤ L p) :
    ∃ node : Fin N → ℝ, (∀ j, node j ∈ Ioo a b) ∧
      ∀ p : ℝ[X], p.natDegree ≤ k → ∑ j, p.eval (node j) = L p := by
  let center : MomentVector k := fun i => L (X ^ (i.val + 1)) / N
  let radius : ℝ := 1 / (2 * (N : ℝ))
  let D : Set (MomentVector k) :=
    (fun w => center + w) '' variationReserveBall k a b radius
  have hradius : 0 ≤ radius := by dsimp [radius]; positivity
  have hmassL : 0 < L 1 := by rw [hL]; exact_mod_cast hN
  have hcompact : IsCompact D :=
    (isCompact_variationReserveBall k a b radius).image (by fun_prop)
  let : CompactSpace D := isCompact_iff_compactSpace.mp hcompact
  have hinterior : D ⊆ interior (momentBody k a b) := by
    have hc : normalizedMomentVector (k := k) L = center := by
      ext i
      simp only [normalizedMomentVector, center, hL]
    have hs := translated_variationReserveBall_subset_interior (k := k)
      hab L hmassL hβ hreserve
    rw [hc, hL] at hs
    simpa only [D, radius, div_div] using hs
  obtain ⟨ρ, hρ, hpos, hmom⟩ := exists_positive_density_family_of_mem_interior
    hab (fun z : D => (z : MomentVector k)) continuous_subtype_val
    (fun z => hinterior z.property)
  have hmass (z : D) : (∫ x in a..b, ρ z x) = 1 := by
    have h := congrFun (hmom z) (0 : Fin (k + 1))
    simpa only [densityMoments, probabilityMomentVector, Fin.val_zero, pow_zero,
      one_mul, Fin.cons_zero] using h
  have hmoment (z : D) (i : Fin k) :
      (∫ x in a..b, x ^ (i.val + 1) * ρ z x) = z.val i :=
    congrFun (hmom z) i.succ
  let node : D → Fin N → ℝ := fun z =>
    midpointQuantileNode hab.le (density_slice_continuousOn hρ z) (hpos z) (hmass z)
  have hcontinuous : Continuous node :=
    midpointQuantileNode_continuous (N := N) hab.le hρ hpos hmass
  apply exists_unit_nodes_of_continuous_family_with_property hN a b L hL hradius node
    hcontinuous (fun x => ∀ j, x j ∈ Ioo a b)
  · intro z j
    exact midpointQuantileNode_mem_Ioo hab.le (density_slice_continuousOn hρ z)
      (hpos z) (hmass z) j
  · intro z
    exact midpointQuantileNode_error hN hab.le (density_slice_continuousOn hρ z)
      (hpos z) (hmass z) z.val (hmoment z)

/-- The inherited closed-interval interface follows from strict interior nodes. -/
theorem exists_unit_nodes_of_variation_reserve {k N : ℕ} {a b β : ℝ}
    (hab : a < b) (hN : 0 < N) (hβ : 1 / 2 < β)
    (L : ℝ[X] →ₗ[ℝ] ℝ) (hL : L 1 = (N : ℝ))
    (hreserve : ∀ p : ℝ[X], p.natDegree ≤ k →
      (∀ x ∈ Icc a b, 0 ≤ p.eval x) →
        β * (eVariationOn p.eval (Icc a b)).toReal ≤ L p) :
    ∃ node : Fin N → ℝ, (∀ j, node j ∈ Icc a b) ∧
      ∀ p : ℝ[X], p.natDegree ≤ k → ∑ j, p.eval (node j) = L p := by
  obtain ⟨node, hnode, hmoment⟩ :=
    exists_interior_unit_nodes_of_variation_reserve hab hN hβ L hL hreserve
  exact ⟨node, fun j => Ioo_subset_Icc_self (hnode j), hmoment⟩

end GapFamily.Quadrature
