import GapFamily.Quadrature.MomentCurve
import GapFamily.Quadrature.Variation
import GapFamily.Quadrature.VariationBall
import Mathlib.Algebra.BigOperators.Field

/-!
# Interior moments from polynomial positivity

A linear functional which is strictly positive on every nonzero nonnegative
polynomial through degree `k` has normalized moments in the interior of the
actual moment body. The supporting margin comes from the nonnegative
polynomial obtained by subtracting a polynomial from its interval maximum.
-/

open Set Polynomial
open scoped BigOperators

namespace GapFamily.Quadrature

/-- The normalized nonconstant moments of a polynomial functional. -/
noncomputable def normalizedMomentVector {k : ℕ} (L : Polynomial ℝ →ₗ[ℝ] ℝ) :
    MomentVector k := fun i => L (Polynomial.X ^ (i.val + 1)) / L 1

theorem linearMap_polynomial_C (L : Polynomial ℝ →ₗ[ℝ] ℝ) (c : ℝ) :
    L (Polynomial.C c) = c * L 1 := by
  have : Polynomial.C c = c • (1 : Polynomial ℝ) := by simp [Polynomial.smul_eq_C_mul]
  rw [this, map_smul]
  rfl

theorem linearMap_coordinatePolynomial {k : ℕ} (L : Polynomial ℝ →ₗ[ℝ] ℝ)
    (u : MomentVector k) :
    L (coordinatePolynomial u) = ∑ i, u i * L (Polynomial.X ^ (i.val + 1)) := by
  simp [coordinatePolynomial, ← Polynomial.smul_eq_C_mul]

theorem normalizedMomentVector_dot {k : ℕ} (L : Polynomial ℝ →ₗ[ℝ] ℝ)
    (u : MomentVector k) :
    ∑ i, u i * normalizedMomentVector L i = L (coordinatePolynomial u) / L 1 := by
  simp_rw [normalizedMomentVector, ← mul_div_assoc]
  rw [← Finset.sum_div, linearMap_coordinatePolynomial]

/-- Positivity includes the constant polynomial and therefore the normalizing mass. -/
theorem strictPositive_one {k : ℕ} {a b : ℝ} (L : Polynomial ℝ →ₗ[ℝ] ℝ)
    (hpos : ∀ p : Polynomial ℝ, p.natDegree ≤ k → p ≠ 0 →
      (∀ x ∈ Set.Icc a b, 0 ≤ p.eval x) → 0 < L p) : 0 < L 1 := by
  apply hpos 1 (by simp) one_ne_zero
  intro x _
  simp

/-- Every nonzero coefficient vector sees a strict supporting margin. -/
theorem normalizedMomentVector_dot_margin {k : ℕ} {a b : ℝ} (hab : a < b)
    (L : Polynomial ℝ →ₗ[ℝ] ℝ)
    (hpos : ∀ p : Polynomial ℝ, p.natDegree ≤ k → p ≠ 0 →
      (∀ x ∈ Set.Icc a b, 0 ≤ p.eval x) → 0 < L p)
    (u : MomentVector k) (hu : u ≠ 0) :
    ∃ x ∈ Set.Icc a b,
      ∑ i, u i * normalizedMomentVector L i < ∑ i, u i * momentCurve k x i := by
  let p := coordinatePolynomial u
  obtain ⟨x, hx, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (Set.nonempty_Icc.mpr hab.le) p.differentiable.continuous.continuousOn
  refine ⟨x, hx, ?_⟩
  have hdeg : (Polynomial.C (p.eval x) - p).natDegree ≤ k :=
    (Polynomial.natDegree_sub_le _ _).trans
      (max_le (by simp) (natDegree_coordinatePolynomial_le u))
  have hne : Polynomial.C (p.eval x) - p ≠ 0 := by
    intro heq
    exact hu (coordinatePolynomial_eq_const_iff.mp (sub_eq_zero.mp heq).symm).1
  have hq := hpos (Polynomial.C (p.eval x) - p) hdeg hne (by
    intro y hy
    simp only [Polynomial.eval_sub, Polynomial.eval_C]
    exact sub_nonneg.mpr (hmax hy))
  rw [map_sub, linearMap_polynomial_C] at hq
  rw [normalizedMomentVector_dot, ← eval_coordinatePolynomial]
  exact (div_lt_iff₀ (strictPositive_one L hpos)).mpr (by linarith)

/-- The concrete normalized moments, with no representing measure assumption,
lie in the interior of the compact interval moment body. -/
theorem normalizedMomentVector_mem_interior {k : ℕ} {a b : ℝ} (hab : a < b)
    (L : Polynomial ℝ →ₗ[ℝ] ℝ)
    (hpos : ∀ p : Polynomial ℝ, p.natDegree ≤ k → p ≠ 0 →
      (∀ x ∈ Set.Icc a b, 0 ≤ p.eval x) → 0 < L p) :
    normalizedMomentVector (k := k) L ∈ interior (momentBody k a b) := by
  apply mem_interior_of_functional_margin (convex_momentBody k a b)
    (momentBody_interior_nonempty k hab)
  intro f hf
  let u : MomentVector k := fun i => f (Pi.single i 1)
  have hu : u ≠ 0 := by
    intro hu
    apply hf
    ext v
    change f.toLinearMap v = 0
    rw [linearMap_apply_eq_sum f.toLinearMap v]
    change (∑ i, u i * v i) = 0
    simp [hu]
  obtain ⟨x, hx, hmargin⟩ := normalizedMomentVector_dot_margin hab L hpos u hu
  refine ⟨momentCurve k x, subset_convexHull ℝ _ ⟨x, hx, rfl⟩, ?_⟩
  change f.toLinearMap _ < f.toLinearMap _
  rw [linearMap_apply_eq_sum, linearMap_apply_eq_sum]
  exact hmargin

/-- Subtracting a polynomial from a constant preserves its partition variation. -/
theorem eVariationOn_polynomial_C_sub (p : Polynomial ℝ) (c a b : ℝ) :
    eVariationOn (Polynomial.C c - p).eval (Set.Icc a b) =
      eVariationOn p.eval (Set.Icc a b) := by
  simp only [eVariationOn, Polynomial.eval_sub, Polynomial.eval_C, edist_dist,
    Real.dist_eq, sub_sub_sub_cancel_left, abs_sub_comm]

/-- A nonzero nonconstant coefficient vector has strictly positive, finite
partition variation on a nondegenerate interval. -/
theorem coordinatePolynomial_variation_pos_of_ne_zero {k : ℕ} {a b : ℝ}
    (hab : a < b) (u : MomentVector k) (hu : u ≠ 0) :
    0 < (eVariationOn (coordinatePolynomial u).eval (Set.Icc a b)).toReal := by
  apply ENNReal.toReal_pos ?_ (polynomial_boundedVariationOn _ hab.le)
  intro hv
  have hc : coordinatePolynomial u = Polynomial.C ((coordinatePolynomial u).eval a) := by
    apply Polynomial.eq_of_infinite_eval_eq
    apply (Set.Icc_infinite hab).mono
    intro x hx
    simp only [Set.mem_ofPred_eq, Polynomial.eval_C]
    have he := (eVariationOn.eq_zero_iff _).mp hv x hx a ⟨le_rfl, hab.le⟩
    exact edist_eq_zero.mp he
  exact hu (coordinatePolynomial_eq_const_iff.mp hc).1

/-- A polynomial variation reserve gives the exact normalized supporting
margin needed by the prescribed-count quadrature argument. -/
theorem normalizedMomentVector_dot_margin_of_variation_reserve
    {k : ℕ} {a b β r : ℝ} (hab : a < b)
    (L : Polynomial ℝ →ₗ[ℝ] ℝ) (hL : 0 < L 1) (hr : r < β)
    (hreserve : ∀ p : Polynomial ℝ, p.natDegree ≤ k →
      (∀ x ∈ Set.Icc a b, 0 ≤ p.eval x) →
        β * (eVariationOn p.eval (Set.Icc a b)).toReal ≤ L p)
    (u : MomentVector k) (hu : u ≠ 0) :
    ∃ x ∈ Set.Icc a b,
      (∑ i, u i * normalizedMomentVector L i) +
          (r / L 1) * (eVariationOn (coordinatePolynomial u).eval (Set.Icc a b)).toReal <
        ∑ i, u i * momentCurve k x i := by
  let p := coordinatePolynomial u
  obtain ⟨x, hx, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (Set.nonempty_Icc.mpr hab.le) p.differentiable.continuous.continuousOn
  refine ⟨x, hx, ?_⟩
  have hdeg : (Polynomial.C (p.eval x) - p).natDegree ≤ k :=
    (Polynomial.natDegree_sub_le _ _).trans
      (max_le (by simp) (natDegree_coordinatePolynomial_le u))
  have hq := hreserve (Polynomial.C (p.eval x) - p) hdeg (by
    intro y hy
    simp only [Polynomial.eval_sub, Polynomial.eval_C]
    exact sub_nonneg.mpr (hmax hy))
  rw [map_sub, linearMap_polynomial_C, eVariationOn_polynomial_C_sub] at hq
  have hrvar := mul_lt_mul_of_pos_right hr
    (coordinatePolynomial_variation_pos_of_ne_zero hab u hu)
  have hstrict : L p + r * (eVariationOn p.eval (Set.Icc a b)).toReal <
      p.eval x * L 1 := by linarith
  rw [normalizedMomentVector_dot, ← eval_coordinatePolynomial]
  convert (div_lt_iff₀ hL).mpr hstrict using 1
  ring

/-- The entire region cut out by the variation bounds of all polynomial
coefficient vectors lies in the moment body's interior. -/
theorem mem_interior_momentBody_of_variation_reserve
    {k : ℕ} {a b β r : ℝ} (hab : a < b)
    (L : Polynomial ℝ →ₗ[ℝ] ℝ) (hL : 0 < L 1) (hr : r < β)
    (hreserve : ∀ p : Polynomial ℝ, p.natDegree ≤ k →
      (∀ x ∈ Set.Icc a b, 0 ≤ p.eval x) →
        β * (eVariationOn p.eval (Set.Icc a b)).toReal ≤ L p)
    (z : MomentVector k)
    (hz : ∀ u : MomentVector k,
      |∑ i, u i * (z i - normalizedMomentVector L i)| ≤
        (r / L 1) * (eVariationOn (coordinatePolynomial u).eval (Set.Icc a b)).toReal) :
    z ∈ interior (momentBody k a b) := by
  apply mem_interior_of_functional_margin (convex_momentBody k a b)
    (momentBody_interior_nonempty k hab)
  intro f hf
  let u : MomentVector k := fun i => f (Pi.single i 1)
  have hu : u ≠ 0 := by
    intro hu
    apply hf
    ext v
    change f.toLinearMap v = 0
    rw [linearMap_apply_eq_sum f.toLinearMap v]
    change (∑ i, u i * v i) = 0
    simp [hu]
  obtain ⟨x, hx, hmargin⟩ :=
    normalizedMomentVector_dot_margin_of_variation_reserve hab L hL hr hreserve u hu
  refine ⟨momentCurve k x, subset_convexHull ℝ _ ⟨x, hx, rfl⟩, ?_⟩
  change f.toLinearMap _ < f.toLinearMap _
  rw [linearMap_apply_eq_sum, linearMap_apply_eq_sum]
  apply lt_of_le_of_lt ?_ hmargin
  have hp := (le_abs_self _).trans (hz u)
  simp_rw [mul_sub] at hp
  rw [Finset.sum_sub_distrib] at hp
  exact (sub_le_iff_le_add.mp hp).trans_eq (add_comm _ _)

/-- The compact translated variation ball used as the fixed-point domain
stays strictly inside the moment body whenever its reserve is smaller than
the functional's reserve. -/
theorem translated_variationReserveBall_subset_interior
    {k : ℕ} {a b β r : ℝ} (hab : a < b)
    (L : Polynomial ℝ →ₗ[ℝ] ℝ) (hL : 0 < L 1) (hr : r < β)
    (hreserve : ∀ p : Polynomial ℝ, p.natDegree ≤ k →
      (∀ x ∈ Set.Icc a b, 0 ≤ p.eval x) →
        β * (eVariationOn p.eval (Set.Icc a b)).toReal ≤ L p) :
    (fun w => normalizedMomentVector (k := k) L + w) ''
        variationReserveBall k a b (r / L 1) ⊆ interior (momentBody k a b) := by
  rintro _ ⟨w, hw, rfl⟩
  apply mem_interior_momentBody_of_variation_reserve hab L hL hr hreserve
  intro u
  simpa only [Pi.add_apply, add_sub_cancel_left] using hw u

end GapFamily.Quadrature
