import BTZEntropy.Comparison.DensityError

/-!
# Patching finite cell errors

Disjoint cells in each spin row allow a single density envelope to control
their union. The corresponding full packet integral is exactly the sum of
the local cell integrals.
-/

noncomputable section

open Set MeasureTheory Real
open GapFamily.Analytic
open scoped BigOperators

namespace BTZEntropy.Comparison

variable {ι : Type*}

/-- Extend each cell error by zero and group the finite cell family by spin. -/
def patchedDensityError (S : Finset ι) (spin : ι → ℤ) (left right : ι → ℝ)
    (error : ι → ℝ → ℝ) (j : ℤ) (e : ℝ) : ℝ :=
  ∑ i ∈ S, if spin i = j then (Ioo (left i) (right i)).indicator (error i) e else 0

/-- A point meeting one cell in its spin row receives exactly that cell's
error, since all other cells in the same row are disjoint. -/
theorem patchedDensityError_eq_of_mem (S : Finset ι) (spin : ι → ℤ)
    (left right : ι → ℝ) (error : ι → ℝ → ℝ)
    (hdisjoint : ∀ i ∈ S, ∀ k ∈ S, i ≠ k → spin i = spin k →
      Disjoint (Ioo (left i) (right i)) (Ioo (left k) (right k)))
    {i : ι} (hi : i ∈ S) {e : ℝ} (he : e ∈ Ioo (left i) (right i)) :
    patchedDensityError S spin left right error (spin i) e = error i e := by
  classical
  rw [patchedDensityError, Finset.sum_eq_single i]
  · simp [he]
  · intro k hk hki
    by_cases hs : spin k = spin i
    · have hknot : e ∉ Ioo (left k) (right k) := by
        intro hke
        exact Set.disjoint_left.mp (hdisjoint i hi k hk hki.symm hs.symm) he hke
      simp [hs, hknot]
    · simp [hs]
  · exact fun hnot => (hnot hi).elim

/-- The finite patch vanishes away from every cell belonging to the row. -/
theorem patchedDensityError_eq_zero (S : Finset ι) (spin : ι → ℤ)
    (left right : ι → ℝ) (error : ι → ℝ → ℝ) (j : ℤ) (e : ℝ)
    (h : ∀ i ∈ S, spin i = j → e ∉ Ioo (left i) (right i)) :
    patchedDensityError S spin left right error j e = 0 := by
  apply Finset.sum_eq_zero
  intro i hi
  by_cases hs : spin i = j
  · simp [hs, h i hi hs]
  · simp [hs]

/-- Disjoint cells retain their common pointwise envelope without a factor
equal to the number of cells. -/
theorem patchedDensityError_abs_le (S : Finset ι) (spin : ι → ℤ)
    (left right : ι → ℝ) (error : ι → ℝ → ℝ) (M : ℝ → ℝ)
    (hdisjoint : ∀ i ∈ S, ∀ k ∈ S, i ≠ k → spin i = spin k →
      Disjoint (Ioo (left i) (right i)) (Ioo (left k) (right k)))
    (hM : ∀ e, 0 ≤ M e)
    (herror : ∀ i ∈ S, ∀ e ∈ Ioo (left i) (right i), |error i e| ≤ M e)
    (j : ℤ) (e : ℝ) :
    |patchedDensityError S spin left right error j e| ≤ M e := by
  classical
  by_cases hcell : ∃ i ∈ S, spin i = j ∧ e ∈ Ioo (left i) (right i)
  · obtain ⟨i, hi, hij, he⟩ := hcell
    subst j
    rw [patchedDensityError_eq_of_mem S spin left right error hdisjoint hi he]
    exact herror i hi e he
  · rw [patchedDensityError_eq_zero S spin left right error j e (by
      intro i hi hij he
      exact hcell ⟨i, hi, hij, he⟩), abs_zero]
    exact hM e

/-- The physical exponential envelope is unchanged by a disjoint cell patch. -/
theorem patchedDensityError_abs_le_exp (S : Finset ι) (spin : ι → ℤ)
    (left right : ι → ℝ) (error : ι → ℝ → ℝ) (a : ℝ)
    (hdisjoint : ∀ i ∈ S, ∀ k ∈ S, i ≠ k → spin i = spin k →
      Disjoint (Ioo (left i) (right i)) (Ioo (left k) (right k)))
    (herror : ∀ i ∈ S, ∀ e ∈ Ioo (left i) (right i),
      |error i e| ≤ exp (7 * sqrt (a * e))) (j : ℤ) (e : ℝ) :
    |patchedDensityError S spin left right error j e| ≤ exp (7 * sqrt (a * e)) :=
  patchedDensityError_abs_le S spin left right error _ hdisjoint
    (fun _ => (exp_pos _).le) herror j e

private theorem patchedDensityError_mul (S : Finset ι) (spin : ι → ℤ)
    (left right : ι → ℝ) (error : ι → ℝ → ℝ) (f : ℝ → ℝ) (j : ℤ) (e : ℝ) :
    patchedDensityError S spin left right error j e * f e =
      ∑ i ∈ S, if spin i = j then
        (Ioo (left i) (right i)).indicator (fun e => error i e * f e) e else 0 := by
  rw [patchedDensityError, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hs : spin i = j <;> by_cases he : e ∈ Ioo (left i) (right i) <;>
    simp [hs, he]

/-- Row integration of the patch agrees with the finite sum of actual cell
integrals. Integrability is assumed only on each cell itself. -/
theorem integral_patchedDensityError (S : Finset ι) (spin : ι → ℤ)
    (left right : ι → ℝ) (error : ι → ℝ → ℝ) (f : ℝ → ℝ) (lower : ℤ → ℝ)
    (hlower : ∀ i ∈ S, lower (spin i) ≤ left i)
    (hint : ∀ i ∈ S, IntegrableOn (fun e => error i e * f e)
      (Ioo (left i) (right i)) (referenceMeasure (spin i))) (j : ℤ) :
    (∫ e in Ici (lower j), patchedDensityError S spin left right error j e * f e
      ∂referenceMeasure j) =
      ∑ i ∈ S, if spin i = j then
        ∫ e in Ioo (left i) (right i), error i e * f e ∂referenceMeasure (spin i)
        else 0 := by
  simp_rw [patchedDensityError_mul]
  rw [integral_finsetSum S]
  · apply Finset.sum_congr rfl
    intro i hi
    by_cases hs : spin i = j
    · subst j
      simp only [ite_true]
      rw [integral_indicator measurableSet_Ioo, Measure.restrict_restrict measurableSet_Ioo]
      rw [inter_eq_left.mpr (show Ioo (left i) (right i) ⊆ Ici (lower (spin i)) from
        fun e he => (hlower i hi).trans he.1.le)]
    · simp [hs]
  · intro i hi
    by_cases hs : spin i = j
    · subst j
      simpa only [ite_true] using ((hint i hi).integrable_indicator measurableSet_Ioo).restrict
    · simp [hs]

/-- The full sum over integer spins is exactly the finite sum of local cell
tests. No coverage of the rest of the physical half-line is required. -/
theorem densityErrorFullPacket_patchedDensityError (φ : SmoothKernel) (E : ℝ)
    (F : Finset (ℕ × ℕ)) (S : Finset ι) (spin : ι → ℤ) (left right : ι → ℝ)
    (error : ι → ℝ → ℝ) (lower : ℤ → ℝ)
    (hlower : ∀ i ∈ S, lower (spin i) ≤ left i)
    (hint : ∀ i ∈ S, IntegrableOn
      (fun e => error i e * primaryDescendantTest φ E F e)
      (Ioo (left i) (right i)) (referenceMeasure (spin i))) :
    densityErrorFullPacket φ E F (patchedDensityError S spin left right error) lower =
      ∑ i ∈ S, ∫ e in Ioo (left i) (right i),
        error i e * primaryDescendantTest φ E F e ∂referenceMeasure (spin i) := by
  classical
  simp only [densityErrorFullPacket,
    integral_patchedDensityError S spin left right error _ lower hlower hint]
  rw [Summable.tsum_finsetSum]
  · apply Finset.sum_congr rfl
    intro i hi
    simp
  · intro i hi
    exact (hasSum_ite_eq (spin i)
      (∫ e in Ioo (left i) (right i),
        error i e * primaryDescendantTest φ E F e ∂referenceMeasure (spin i))).summable.congr
      (by intro j; simp [eq_comm])

end BTZEntropy.Comparison
