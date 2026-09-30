import GapFamily.Analytic.Cusp.CuspLowBound
import GapFamily.Analytic.Cusp.CuspLowMeasure
import GapFamily.Analytic.Cusp.MeanZero.CuspMeanZeroGapConsequence

/-!
# An explicit gap on the actual zero-average cusp form space

The upper trace and lower-fiber estimates are applied to actual projected
smooth-core vectors. Their genuine form-norm density then gives the bound on
the completed constrained space. No full-operator eigenfunction premise or
pointwise regularity of an arbitrary completed vector is needed.
-/

noncomputable section
namespace GapFamily.Analytic
open Set Filter ModularGradient
open scoped Topology ComplexOrder

/-- The actual projected core obeys the geometric mass bound. -/
theorem cuspProjected_mass_le_five_halves_energy (F : smoothCore) :
    ‖meanZeroCuspEmbedding (cuspMeanZeroFormPart (coreForm F))‖ ^ 2 ≤
      (5 / 2 : ℝ) * ‖formGradient (cuspMeanZeroFormPart (coreForm F) : FormDomain)‖ ^ 2 := by
  have hm := cuspProjected_mass_decomposition F
  have hl := cuspProjected_low_mass_le_boundary F
  have hb := cuspProjected_boundary_trace_sq_le F
  have he := cuspProjected_low_vertical_energy_le F
  have hh := meanZeroCusp_restrict_energy_bound 1 le_rfl
    (cuspMeanZeroFormPart (coreForm F))
  norm_num only [one_pow, div_self (by norm_num : (1 : ℝ) ≠ 0), one_mul] at hh
  linarith

/-- Every actual constrained form vector satisfies the same explicit estimate. -/
theorem cuspMeanZero_mass_le_five_halves_energy (v : cuspMeanZeroForm) :
    ‖meanZeroCuspEmbedding v‖ ^ 2 ≤ (5 / 2 : ℝ) * ‖cuspMeanZeroGradient v‖ ^ 2 := by
  obtain ⟨F, hF⟩ := exists_cuspMeanZeroFormPart_core_tendsto v
  have hc : IsClosed {u : cuspMeanZeroForm | ‖meanZeroCuspEmbedding u‖ ^ 2 ≤
      (5 / 2 : ℝ) * ‖cuspMeanZeroGradient u‖ ^ 2} :=
    isClosed_le (by fun_prop) (by fun_prop)
  apply hc.mem_of_tendsto hF
  exact Eventually.of_forall (fun n => cuspProjected_mass_le_five_halves_energy (F n))

theorem cuspMeanZeroWeakResolvent_norm_le_five_sevenths :
    ‖cuspMeanZeroWeakResolvent‖ ≤ (5 / 7 : ℝ) :=
  cuspMeanZeroWeakResolvent_norm_le_five_sevenths_of_mass_le
    cuspMeanZero_mass_le_five_halves_energy

/-- The actual constrained quarter pencil is a unit, without a remaining gap premise. -/
theorem cuspMeanZeroPencil_isUnit_quarter : IsUnit (cuspMeanZeroPencil (1 / 4)) :=
  cuspMeanZeroPencil_isUnit_quarter_of_mass_le cuspMeanZero_mass_le_five_halves_energy

theorem cuspMeanZero_quarter_energy_coercive (v : cuspMeanZeroForm) :
    (3 / 28 : ℝ) * ‖v‖ ^ 2 ≤
      ‖cuspMeanZeroGradient v‖ ^ 2 - (1 / 4 : ℝ) * ‖meanZeroCuspEmbedding v‖ ^ 2 :=
  cuspMeanZero_quarter_energy_coercive_of_mass_le cuspMeanZero_mass_le_five_halves_energy v

theorem cuspMeanZero_quarter_response_isPositive :
    (meanZeroCuspEmbedding.comp (cuspMeanZeroPencilSolution (1 / 4))).IsPositive :=
  cuspMeanZero_quarter_response_isPositive_of_mass_le cuspMeanZero_mass_le_five_halves_energy

theorem cuspMeanZero_quarter_constant_pairing_nonneg :
    0 ≤ inner ℂ modularConstant
      (meanZeroCuspEmbedding (cuspMeanZeroPencilSolution (1 / 4) modularConstant)) :=
  cuspMeanZero_quarter_constant_pairing_nonneg_of_mass_le cuspMeanZero_mass_le_five_halves_energy

end GapFamily.Analytic
