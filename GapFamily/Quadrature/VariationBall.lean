import GapFamily.Quadrature.MomentCurve
import GapFamily.Quadrature.Variation
import GapFamily.Quadrature.FixedPoint

/-!
# Compact displacement sets for polynomial variation

The sharp midpoint error is naturally bounded by polynomial variation, rather
than by a preselected Euclidean norm. These sets retain those actual inequalities
and provide a compact convex domain for Brouwer without introducing a new norm.
-/

open Set
open scoped BigOperators

namespace GapFamily.Quadrature

/-- All moment displacements bounded, in every polynomial direction, by `ρ`
times the variation of that polynomial on the actual interval. -/
def variationReserveBall (k : ℕ) (a b ρ : ℝ) : Set (MomentVector k) :=
  {w | ∀ u : MomentVector k, |∑ i, u i * w i| ≤
    ρ * (eVariationOn (coordinatePolynomial u).eval (Icc a b)).toReal}

theorem zero_mem_variationReserveBall (k : ℕ) (a b : ℝ) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    0 ∈ variationReserveBall k a b ρ := by
  intro u
  simpa only [Pi.zero_apply, mul_zero, Finset.sum_const_zero, abs_zero] using
    mul_nonneg hρ (ENNReal.toReal_nonneg (a := eVariationOn
      (coordinatePolynomial u).eval (Icc a b)))

theorem neg_mem_variationReserveBall_iff {k : ℕ} {a b ρ : ℝ} {w : MomentVector k} :
    -w ∈ variationReserveBall k a b ρ ↔ w ∈ variationReserveBall k a b ρ := by
  simp only [variationReserveBall, mem_ofPred_eq, Pi.neg_apply, mul_neg,
    Finset.sum_neg_distrib, abs_neg]

theorem variationReserveBall_mono (k : ℕ) (a b : ℝ) {ρ σ : ℝ} (h : ρ ≤ σ) :
    variationReserveBall k a b ρ ⊆ variationReserveBall k a b σ := by
  intro w hw u
  exact (hw u).trans (mul_le_mul_of_nonneg_right h ENNReal.toReal_nonneg)

theorem isClosed_variationReserveBall (k : ℕ) (a b ρ : ℝ) :
    IsClosed (variationReserveBall k a b ρ) := by
  simp only [variationReserveBall, ofPred_forall]
  apply isClosed_iInter
  intro u
  exact isClosed_le (by fun_prop) continuous_const

theorem convex_variationReserveBall (k : ℕ) (a b ρ : ℝ) :
    Convex ℝ (variationReserveBall k a b ρ) := by
  intro w hw z hz s t hs ht hst u
  have heq : (∑ i, u i * (s • w + t • z) i) =
      s * (∑ i, u i * w i) + t * (∑ i, u i * z i) := by
    simp [mul_add, Finset.sum_add_distrib, Finset.mul_sum, mul_left_comm]
  rw [heq]
  calc
    _ ≤ |s * (∑ i, u i * w i)| + |t * (∑ i, u i * z i)| := abs_add_le _ _
    _ = s * |∑ i, u i * w i| + t * |∑ i, u i * z i| := by
      rw [abs_mul, abs_mul, abs_of_nonneg hs, abs_of_nonneg ht]
    _ ≤ s * (ρ * (eVariationOn (coordinatePolynomial u).eval (Icc a b)).toReal) +
        t * (ρ * (eVariationOn (coordinatePolynomial u).eval (Icc a b)).toReal) :=
      add_le_add (mul_le_mul_of_nonneg_left (hw u) hs)
        (mul_le_mul_of_nonneg_left (hz u) ht)
    _ = ρ * (eVariationOn (coordinatePolynomial u).eval (Icc a b)).toReal := by
      rw [← add_mul, hst, one_mul]

/-- Coordinate directions bound each coordinate, so the variation reserve set
is compact in the finite moment space. -/
theorem isCompact_variationReserveBall (k : ℕ) (a b ρ : ℝ) :
    IsCompact (variationReserveBall k a b ρ) := by
  classical
  let R : MomentVector k := fun i =>
    ρ * (eVariationOn (coordinatePolynomial (Pi.single i 1)).eval (Icc a b)).toReal
  have hsub : variationReserveBall k a b ρ ⊆ Icc (-R) R := by
    intro w hw
    constructor
    · intro i
      have hi := (abs_le.mp (hw (Pi.single i 1))).1
      simpa [R, Pi.single_apply] using hi
    · intro i
      have hi := (abs_le.mp (hw (Pi.single i 1))).2
      simpa [R, Pi.single_apply] using hi
  exact isCompact_Icc.of_isClosed_subset (isClosed_variationReserveBall k a b ρ) hsub

/-- Correct an approximate identity on a translated variation reserve set.
The error uses the same actual polynomial inequalities as the midpoint bound. -/
theorem exists_eq_center_of_variation_error {k : ℕ} (a b : ℝ) (center : MomentVector k)
    {ρ : ℝ} (hρ : 0 ≤ ρ)
    (Q : C((fun w => center + w) '' variationReserveBall k a b ρ, MomentVector k))
    (herror : ∀ z, Q z - (z : MomentVector k) ∈ variationReserveBall k a b ρ) :
    ∃ z, Q z = center := by
  let D := (fun w => center + w) '' variationReserveBall k a b ρ
  have hDconv : Convex ℝ D := (convex_variationReserveBall k a b ρ).translate center
  have hDcompact : IsCompact D :=
    (isCompact_variationReserveBall k a b ρ).image (by fun_prop)
  have hDnonempty : D.Nonempty :=
    ⟨center + 0, ⟨0, zero_mem_variationReserveBall k a b hρ, rfl⟩⟩
  let F : C(D, D) := ⟨fun z => ⟨center + (z : MomentVector k) - Q z, by
    refine ⟨(z : MomentVector k) - Q z, ?_, ?_⟩
    · rw [← neg_sub]
      exact neg_mem_variationReserveBall_iff.mpr (herror z)
    · abel_nf⟩, by fun_prop⟩
  obtain ⟨z, hz⟩ := brouwer_fixed_point D hDconv hDcompact hDnonempty F
  refine ⟨z, ?_⟩
  have heq : center + (z : MomentVector k) - Q z = (z : MomentVector k) :=
    congrArg Subtype.val hz
  have heq' : center + (z : MomentVector k) = Q z + (z : MomentVector k) :=
    (sub_eq_iff_eq_add.mp heq).trans (add_comm _ _)
  exact (add_right_cancel heq').symm

end GapFamily.Quadrature
