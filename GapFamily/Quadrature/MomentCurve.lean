import GapFamily.Quadrature.MomentInterior
import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.Algebra.Polynomial.Roots

/-!
# The finite moment curve

On every nondegenerate real interval, the curve `(x, …, x^k)` has full affine
span. Its convex hull consequently has nonempty interior in the actual
`k`-dimensional moment space. The proof uses uniqueness of real polynomials
on an interval, avoiding a choice of Vandermonde nodes.
-/

open Set Polynomial
open scoped BigOperators

namespace GapFamily.Quadrature

/-- The nonconstant coordinates of moments through degree `k`. -/
abbrev MomentVector (k : ℕ) := Fin k → ℝ

/-- The real moment curve without its constant coordinate. -/
def momentCurve (k : ℕ) (x : ℝ) : MomentVector k := fun i => x ^ (i.val + 1)

/-- The convex body of normalized moments of probability measures on `[a,b]`. -/
def momentBody (k : ℕ) (a b : ℝ) : Set (MomentVector k) :=
  convexHull ℝ (momentCurve k '' Icc a b)

/-- The polynomial with the given nonconstant coefficient vector. -/
noncomputable def coordinatePolynomial {k : ℕ} (u : MomentVector k) : ℝ[X] :=
  ∑ i : Fin k, C (u i) * X ^ (i.val + 1)

theorem continuous_momentCurve (k : ℕ) : Continuous (momentCurve k) := by
  exact continuous_pi fun _ => continuous_id.pow _

theorem convex_momentBody (k : ℕ) (a b : ℝ) : Convex ℝ (momentBody k a b) :=
  convex_convexHull ℝ _

theorem eval_coordinatePolynomial {k : ℕ} (u : MomentVector k) (x : ℝ) :
    (coordinatePolynomial u).eval x = ∑ i, u i * momentCurve k x i := by
  simp [coordinatePolynomial, momentCurve, Polynomial.eval_finsetSum]

@[simp] theorem coeff_coordinatePolynomial_succ {k : ℕ} (u : MomentVector k) (i : Fin k) :
    (coordinatePolynomial u).coeff (i.val + 1) = u i := by
  classical
  simp only [coordinatePolynomial, finsetSum_coeff, coeff_C_mul, coeff_X_pow]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    have hij : (i : ℕ) ≠ (j : ℕ) := fun h => hji (Fin.ext h.symm)
    simp [hij]
  · simp

@[simp] theorem coeff_coordinatePolynomial_zero {k : ℕ} (u : MomentVector k) :
    (coordinatePolynomial u).coeff 0 = 0 := by
  simp [coordinatePolynomial]

theorem natDegree_coordinatePolynomial_le {k : ℕ} (u : MomentVector k) :
    (coordinatePolynomial u).natDegree ≤ k := by
  apply natDegree_sum_le_of_forall_le
  intro i _
  exact (natDegree_C_mul_X_pow_le _ _).trans (Nat.succ_le_of_lt i.isLt)

theorem coordinatePolynomial_eq_const_iff {k : ℕ} {u : MomentVector k} {c : ℝ} :
    coordinatePolynomial u = C c ↔ u = 0 ∧ c = 0 := by
  constructor
  · intro h
    constructor
    · ext i
      have hi := congrArg (fun p : ℝ[X] => p.coeff (i.val + 1)) h
      simpa using hi
    · have h0 := congrArg (fun p : ℝ[X] => p.coeff 0) h
      simpa using h0.symm
  · rintro ⟨rfl, rfl⟩
    simp [coordinatePolynomial]

theorem linearMap_apply_eq_sum {k : ℕ} (f : MomentVector k →ₗ[ℝ] ℝ)
    (x : MomentVector k) : f x = ∑ i, f (Pi.single i 1) * x i := by
  classical
  have hx : (∑ i, x i • Pi.single i (1 : ℝ)) = x := by
    exact (pi_eq_sum_univ' x).symm
  conv_lhs => rw [← hx]
  simp [map_sum, mul_comm]

/-- A linear functional constant on the moment curve of an interval is zero. -/
theorem linearMap_eq_zero_of_constant_on_momentCurve {k : ℕ} {a b c : ℝ}
    (hab : a < b) (f : MomentVector k →ₗ[ℝ] ℝ)
    (hf : ∀ x ∈ Icc a b, f (momentCurve k x) = c) : f = 0 := by
  let u : MomentVector k := fun i => f (Pi.single i 1)
  have hp : coordinatePolynomial u = C c := by
    apply Polynomial.eq_of_infinite_eval_eq
    apply (Icc_infinite hab).mono
    intro x hx
    rw [Set.mem_ofPred_eq, eval_C, eval_coordinatePolynomial]
    exact (linearMap_apply_eq_sum f _).symm.trans (hf x hx)
  have hu : u = 0 := (coordinatePolynomial_eq_const_iff.mp hp).1
  apply LinearMap.ext
  intro x
  rw [linearMap_apply_eq_sum]
  change (∑ i, u i * x i) = 0
  simp [hu]

/-- The real moment curve over a nondegenerate interval spans its full affine space. -/
theorem affineSpan_momentCurve_eq_top (k : ℕ) {a b : ℝ} (hab : a < b) :
    affineSpan ℝ (momentCurve k '' Icc a b) = ⊤ := by
  have ha : momentCurve k a ∈ momentCurve k '' Icc a b :=
    ⟨a, ⟨le_rfl, hab.le⟩, rfl⟩
  apply (AffineSubspace.affineSpan_eq_top_iff_vectorSpan_eq_top_of_nonempty ℝ _ _ ⟨_, ha⟩).2
  by_contra hspan
  obtain ⟨f, hf, hmap⟩ :=
    Submodule.exists_dual_map_eq_bot_of_lt_top (lt_top_iff_ne_top.mpr hspan) inferInstance
  apply hf
  apply linearMap_eq_zero_of_constant_on_momentCurve hab f (c := f (momentCurve k a))
  intro x hx
  have hv := vsub_mem_vectorSpan ℝ (show momentCurve k x ∈ momentCurve k '' Icc a b from
    ⟨x, hx, rfl⟩) ha
  have hz : f (momentCurve k x - momentCurve k a) = 0 := by
    apply (Submodule.mem_bot ℝ).mp
    rw [← hmap]
    exact Submodule.mem_map.mpr ⟨_, hv, rfl⟩
  simpa only [map_sub, sub_eq_zero] using hz

/-- The moment convex hull has interior even when `k = 0`. -/
theorem momentBody_interior_nonempty (k : ℕ) {a b : ℝ} (hab : a < b) :
    (interior (momentBody k a b)).Nonempty := by
  exact interior_convexHull_nonempty_iff_affineSpan_eq_top.mpr
    (affineSpan_momentCurve_eq_top k hab)

end GapFamily.Quadrature
