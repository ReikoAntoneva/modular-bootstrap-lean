import GapFamily.Analytic.Cusp.MeanZero.CuspMeanZeroGapNorm
import GapFamily.Analytic.Cusp.MeanZero.CuspMeanZeroPencilWeak

/-!
# Quarter-parameter consequences of an explicit constrained mass bound

These theorems keep the geometric mass estimate as an explicit premise.
They concern the existing actual constrained response and weak solution.
The quarter pencil is a unit by its strict Neumann bound, and its response
is positive by the actual test-first weak energy identity.
-/

noncomputable section
namespace GapFamily.Analytic

open scoped ComplexOrder

variable (hgap : ∀ v : cuspMeanZeroForm,
  ‖meanZeroCuspEmbedding v‖ ^ 2 ≤ (5 / 2 : ℝ) * ‖cuspMeanZeroGradient v‖ ^ 2)

include hgap

theorem cuspMeanZero_quarter_energy_coercive_of_mass_le (v : cuspMeanZeroForm) :
    (3 / 28 : ℝ) * ‖v‖ ^ 2 ≤
      ‖cuspMeanZeroGradient v‖ ^ 2 - (1 / 4 : ℝ) * ‖meanZeroCuspEmbedding v‖ ^ 2 := by
  have hg := hgap v
  have hn := cuspMeanZeroForm_norm_sq v
  linarith

/-- The actual quarter pencil has scalar perturbation norm at most 25/28. -/
theorem cuspMeanZero_quarter_scaled_resolvent_norm_le_of_mass_le :
    ‖((1 / 4 : ℂ) + 1) • cuspMeanZeroWeakResolvent‖ ≤ (25 / 28 : ℝ) := by
  rw [norm_smul]
  have hc : ‖((1 / 4 : ℂ) + 1)‖ = (5 / 4 : ℝ) := by norm_num
  rw [hc]
  have hn := cuspMeanZeroWeakResolvent_norm_le_five_sevenths_of_mass_le hgap
  linarith

/-- No compactness argument is needed to exclude the quarter parameter. -/
theorem cuspMeanZeroPencil_isUnit_quarter_of_mass_le :
    IsUnit (cuspMeanZeroPencil (1 / 4)) := by
  change IsUnit (1 - ((1 / 4 : ℂ) + 1) • cuspMeanZeroWeakResolvent)
  exact isUnit_one_sub_of_norm_lt_one
    ((cuspMeanZero_quarter_scaled_resolvent_norm_le_of_mass_le hgap).trans_lt (by norm_num))

/-- The actual quarter response pairing is the real shifted gradient energy. -/
theorem cuspMeanZero_quarter_response_inner_eq_of_mass_le (f : ModularHilbert) :
    inner ℂ (meanZeroCuspEmbedding (cuspMeanZeroPencilSolution (1 / 4) f)) f =
      ((‖cuspMeanZeroGradient (cuspMeanZeroPencilSolution (1 / 4) f)‖ ^ 2 -
        (1 / 4 : ℝ) * ‖meanZeroCuspEmbedding (cuspMeanZeroPencilSolution (1 / 4) f)‖ ^ 2 : ℝ) : ℂ) := by
  have h := cuspMeanZeroPencilSolution_equation
    (cuspMeanZeroPencil_isUnit_quarter_of_mass_le hgap) f (cuspMeanZeroPencilSolution (1 / 4) f)
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
  convert h.symm using 1
  norm_num [Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_div]

/-- The actual ambient constrained response at one quarter is positive. -/
theorem cuspMeanZero_quarter_response_isPositive_of_mass_le :
    (meanZeroCuspEmbedding.comp (cuspMeanZeroPencilSolution (1 / 4))).IsPositive := by
  apply (ContinuousLinearMap.isPositive_iff_complex _).mpr
  intro f
  change (((inner ℂ (meanZeroCuspEmbedding (cuspMeanZeroPencilSolution (1 / 4) f)) f).re : ℝ) : ℂ) =
      inner ℂ (meanZeroCuspEmbedding (cuspMeanZeroPencilSolution (1 / 4) f)) f ∧
      0 ≤ (inner ℂ (meanZeroCuspEmbedding (cuspMeanZeroPencilSolution (1 / 4) f)) f).re
  rw [cuspMeanZero_quarter_response_inner_eq_of_mass_le hgap f]
  simp only [Complex.ofReal_re]
  refine ⟨trivial, ?_⟩
  have hg := hgap (cuspMeanZeroPencilSolution (1 / 4) f)
  nlinarith [sq_nonneg ‖cuspMeanZeroGradient (cuspMeanZeroPencilSolution (1 / 4) f)‖]

/-- In particular the genuine constant-source pairing is nonnegative. -/
theorem cuspMeanZero_quarter_constant_pairing_nonneg_of_mass_le :
    0 ≤ inner ℂ modularConstant
      (meanZeroCuspEmbedding (cuspMeanZeroPencilSolution (1 / 4) modularConstant)) :=
  (cuspMeanZero_quarter_response_isPositive_of_mass_le hgap).inner_nonneg_right modularConstant

end GapFamily.Analytic
