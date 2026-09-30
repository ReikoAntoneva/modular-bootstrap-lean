import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Analysis.Normed.Operator.Compact.FredholmAlternative

/-!
# Strict norm gap for a compact positive contraction

A compact positive contraction without a nonzero fixed vector has norm strictly
less than one. The Fredholm alternative excludes one from its spectrum. The
Rayleigh-quotient estimate on the resolvent set then excludes norm one, without
an additional spectral decomposition or a norm-attainment hypothesis.
-/

noncomputable section

namespace GapFamily.Analytic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- A compact positive contraction with trivial fixed space has a strict norm gap. -/
theorem norm_lt_one_of_isCompact_isPositive_no_fixed (R : E →L[ℂ] E)
    (hcompact : IsCompactOperator R) (hpositive : R.IsPositive)
    (hcontract : ‖R‖ ≤ 1) (hfixed : ∀ x, R x = x → x = 0) :
    ‖R‖ < 1 := by
  nontriviality E
  by_contra! hnot
  have hnorm : ‖R‖ = 1 := le_antisymm hcontract hnot
  have hnoEigen : ¬ Module.End.HasEigenvalue (R : E →ₗ[ℂ] E) 1 := by
    intro heigen
    obtain ⟨x, hx⟩ := heigen.exists_hasEigenvector
    exact hx.2 (hfixed x (by simpa using hx.apply_eq_smul))
  have hres : (1 : ℂ) ∈ resolventSet ℂ R :=
    (hcompact.hasEigenvalue_or_mem_resolventSet one_ne_zero).resolve_left hnoEigen
  have hnormres : algebraMap ℝ ℂ ‖R‖ ∈ resolventSet ℂ R := by
    simpa only [hnorm, map_one] using hres
  obtain ⟨ε, hεpos, hε⟩ := R.rayleighQuotient_le_of_norm_mem_resolventSet hnormres
  have hquot (x : E) : 0 ≤ R.rayleighQuotient x :=
    div_nonneg (hpositive.re_inner_nonneg_left x) (sq_nonneg _)
  have hbound : ‖R‖ ≤ ‖R‖ - ε := calc
    ‖R‖ = ⨆ x, |R.rayleighQuotient x| :=
      R.norm_eq_iSup_rayleighQuotient hpositive.isSymmetric
    _ ≤ ‖R‖ - ε := ciSup_le fun x => by
      rw [abs_of_nonneg (hquot x)]
      exact hε x
  linarith

/-- The complementary operator is invertible once compactness and positivity
turn the trivial fixed space into a strict contraction estimate. -/
theorem isUnit_one_sub_of_isCompact_isPositive_no_fixed (R : E →L[ℂ] E)
    (hcompact : IsCompactOperator R) (hpositive : R.IsPositive)
    (hcontract : ‖R‖ ≤ 1) (hfixed : ∀ x, R x = x → x = 0) :
    IsUnit (1 - R) :=
  isUnit_one_sub_of_norm_lt_one
    (norm_lt_one_of_isCompact_isPositive_no_fixed R hcompact hpositive hcontract hfixed)

end GapFamily.Analytic
