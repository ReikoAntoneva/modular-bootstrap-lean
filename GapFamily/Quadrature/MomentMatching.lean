import GapFamily.Quadrature.VariationBall
import Mathlib.Algebra.Polynomial.Eval.SMul

/-!
# Exact polynomial matching from a unit-node moment map

The node index is exactly `Fin N`. Equality of the normalized nonconstant
moment coordinates and the prescribed constant mass imply equality for every
polynomial through the requested degree. The fixed-point application keeps the
continuous node family and its error estimate as explicit remaining inputs.
-/

open Polynomial
open scoped BigOperators

namespace GapFamily.Quadrature

/-- The normalized finite moments of exactly `N` unit nodes. -/
noncomputable def unitNodeMoment {N : ℕ} (k : ℕ) (node : Fin N → ℝ) : MomentVector k :=
  fun i => (∑ j, node j ^ (i.val + 1)) / N

/-- Agreement on the monomials through degree `k` implies agreement on every
polynomial of that degree bound. -/
theorem linearMap_polynomial_eq_of_monomial {k : ℕ} (L M : ℝ[X] →ₗ[ℝ] ℝ)
    (h : ∀ j ≤ k, L (X ^ j) = M (X ^ j)) (p : ℝ[X]) (hp : p.natDegree ≤ k) :
    L p = M p := by
  conv_lhs => rw [p.as_sum_range_C_mul_X_pow' (Nat.lt_succ_of_le hp)]
  conv_rhs => rw [p.as_sum_range_C_mul_X_pow' (Nat.lt_succ_of_le hp)]
  simp only [map_sum, ← smul_eq_C_mul, map_smul, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro j hj
  rw [h j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))]

/-- Exactly `N` unit nodes whose normalized moments equal those of a functional
of mass `N` match every polynomial through degree `k`. -/
theorem sum_eval_eq_of_unitNodeMoment {k N : ℕ} (hN : 0 < N)
    (L : ℝ[X] →ₗ[ℝ] ℝ) (hL : L 1 = (N : ℝ)) (node : Fin N → ℝ)
    (hnode : unitNodeMoment k node = fun i => L (X ^ (i.val + 1)) / N)
    (p : ℝ[X]) (hp : p.natDegree ≤ k) :
    ∑ j, p.eval (node j) = L p := by
  let M : ℝ[X] →ₗ[ℝ] ℝ := ∑ j, Polynomial.leval (node j)
  have hm : M p = ∑ j, p.eval (node j) := by simp [M, Polynomial.leval_apply]
  rw [← hm]
  apply linearMap_polynomial_eq_of_monomial M L _ p hp
  intro j hj
  cases j with
  | zero => simp [M, hL]
  | succ j =>
    have hcoord := congrFun hnode (⟨j, Nat.lt_of_succ_le hj⟩ : Fin k)
    have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    have hsum : (∑ m, node m ^ (j + 1)) = L (X ^ (j + 1)) :=
      (div_left_inj' hN').mp hcoord
    simpa [M, Polynomial.leval_apply] using hsum

/-- A continuous exactly-`N` node family with a variation-controlled moment
error yields actual exact polynomial quadrature. Constructing this family from
the polynomial reserve remains a separate analytic task. -/
theorem exists_unit_nodes_of_continuous_family_with_property {k N : ℕ} (hN : 0 < N)
    (a b : ℝ) (L : ℝ[X] →ₗ[ℝ] ℝ) (hL : L 1 = (N : ℝ))
    {ρ : ℝ} (hρ : 0 ≤ ρ)
    (node : ((fun w => (fun i : Fin k => L (X ^ (i.val + 1)) / N) + w) ''
        variationReserveBall k a b ρ) → Fin N → ℝ)
    (hcontinuous : Continuous node)
    (P : (Fin N → ℝ) → Prop) (hproperty : ∀ z, P (node z))
    (herror : ∀ z, unitNodeMoment k (node z) - (z : MomentVector k) ∈
      variationReserveBall k a b ρ) :
    ∃ x : Fin N → ℝ, P x ∧
      ∀ p : ℝ[X], p.natDegree ≤ k → ∑ j, p.eval (x j) = L p := by
  let center : MomentVector k := fun i => L (X ^ (i.val + 1)) / N
  let Q : C((fun w => center + w) '' variationReserveBall k a b ρ, MomentVector k) :=
    ⟨fun z => unitNodeMoment k (node z), by
      unfold unitNodeMoment
      fun_prop⟩
  obtain ⟨z, hz⟩ := exists_eq_center_of_variation_error a b center hρ Q herror
  refine ⟨node z, hproperty z, fun p hp => ?_⟩
  exact sum_eval_eq_of_unitNodeMoment hN L hL (node z) hz p hp

/-- The closed-interval specialization of the property-preserving construction. -/
theorem exists_unit_nodes_of_continuous_family {k N : ℕ} (hN : 0 < N)
    (a b : ℝ) (L : ℝ[X] →ₗ[ℝ] ℝ) (hL : L 1 = (N : ℝ))
    {ρ : ℝ} (hρ : 0 ≤ ρ)
    (node : ((fun w => (fun i : Fin k => L (X ^ (i.val + 1)) / N) + w) ''
        variationReserveBall k a b ρ) → Fin N → ℝ)
    (hcontinuous : Continuous node)
    (hinterval : ∀ z j, node z j ∈ Set.Icc a b)
    (herror : ∀ z, unitNodeMoment k (node z) - (z : MomentVector k) ∈
      variationReserveBall k a b ρ) :
    ∃ x : Fin N → ℝ, (∀ j, x j ∈ Set.Icc a b) ∧
      ∀ p : ℝ[X], p.natDegree ≤ k → ∑ j, p.eval (x j) = L p :=
  exists_unit_nodes_of_continuous_family_with_property hN a b L hL hρ node hcontinuous
    (fun x => ∀ j, x j ∈ Set.Icc a b) hinterval herror

end GapFamily.Quadrature
