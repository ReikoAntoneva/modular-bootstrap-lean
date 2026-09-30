import GapFamily.Analytic.Transform.LaplaceWeight

/-!
# Simultaneous finite-spin Laplace approximation

The actual adjacent-height Laplace tests approximate every finite family of
weighted energy-row vectors. Each residual has finite L² norm, and the sum of
these norms can be made arbitrarily small. The empty spin family is allowed.
-/

open MeasureTheory
open scoped BigOperators ENNReal

namespace GapFamily.Analytic

/-- An actual finite linear combination of adjacent-height Laplace tests. -/
noncomputable def finiteLaplaceSum {n : ℕ} (c : Fin n → ℂ) (E : ℝ) : ℂ :=
  ∑ k, c k * (laplaceTest k.val E : ℂ)

/-- Every finite test retains the cancellation at the scalar origin. -/
@[simp] theorem finiteLaplaceSum_zero {n : ℕ} (c : Fin n → ℂ) :
    finiteLaplaceSum c 0 = 0 := by
  simp [finiteLaplaceSum]

theorem finiteLaplaceSum_continuous {n : ℕ} (c : Fin n → ℂ) :
    Continuous (finiteLaplaceSum c) := by
  unfold finiteLaplaceSum laplaceTest
  fun_prop

/-- Finite families are approximated simultaneously by actual finite Laplace
sums. The approximants and residuals belong to the physical weighted L² row;
the explicit finite-norm field makes the use of `ENNReal.toReal` unambiguous.
The spin map may have repeats and the finite index type may be empty. -/
theorem exists_finite_spin_laplace_approximation {ι : Type*} [Fintype ι]
    (j : ι → ℤ) (f : ι → ℝ → ℂ)
    (hf : ∀ i, MemLp (f i) 2 (energySpaceMeasure (j i)))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (n : ι → ℕ) (c : ∀ i, Fin (n i) → ℂ),
      (∀ i, MemLp (finiteLaplaceSum (c i)) 2 (energySpaceMeasure (j i)) ∧
        MemLp (fun E => f i E - finiteLaplaceSum (c i) E) 2 (energySpaceMeasure (j i)) ∧
        eLpNorm (fun E => f i E - finiteLaplaceSum (c i) E) 2 (energySpaceMeasure (j i)) < ∞) ∧
      (∑ i, (eLpNorm (fun E => f i E - finiteLaplaceSum (c i) E) 2
        (energySpaceMeasure (j i))).toReal) < ε ∧
      (∀ i, finiteLaplaceSum (c i) 0 = 0) := by
  classical
  let δ := ε / ((Fintype.card ι : ℝ) + 1)
  have hden : 0 < (Fintype.card ι : ℝ) + 1 := by positivity
  have hδ : 0 < δ := div_pos hε hden
  choose n c hc herr using fun i => exists_finite_laplaceTest_eLpNorm_sub_lt (j i) (hf i) hδ
  have hmem (i : ι) : MemLp (finiteLaplaceSum (c i)) 2 (energySpaceMeasure (j i)) := hc i
  have hres (i : ι) : MemLp (fun E => f i E - finiteLaplaceSum (c i) E) 2
      (energySpaceMeasure (j i)) := (hf i).sub (hmem i)
  refine ⟨n, c, fun i => ⟨hmem i, hres i, (hres i).eLpNorm_lt_top⟩, ?_,
    fun i => finiteLaplaceSum_zero (c i)⟩
  have hrow (i : ι) : (eLpNorm (fun E => f i E - finiteLaplaceSum (c i) E) 2
      (energySpaceMeasure (j i))).toReal < δ := by
    have h := (ENNReal.toReal_lt_toReal (hres i).eLpNorm_ne_top ENNReal.ofReal_ne_top).mpr
      (herr i)
    simpa only [ENNReal.toReal_ofReal hδ.le] using h
  calc
    _ ≤ ∑ _i : ι, δ := Finset.sum_le_sum (fun i _ => (hrow i).le)
    _ = (Fintype.card ι : ℝ) * δ := by simp [nsmul_eq_mul]
    _ = (Fintype.card ι : ℝ) * ε / ((Fintype.card ι : ℝ) + 1) := by dsimp [δ]; ring
    _ < ε := (div_lt_iff₀ hden).mpr (by nlinarith)

end GapFamily.Analytic
