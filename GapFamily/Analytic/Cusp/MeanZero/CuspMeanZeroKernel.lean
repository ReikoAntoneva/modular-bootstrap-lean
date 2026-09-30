import GapFamily.Analytic.Cusp.MeanZero.CuspMeanZeroConstant
import GapFamily.Analytic.Cusp.MeanZero.CuspMeanZeroResolvent
import GapFamily.Analytic.Modular.ModularGradientKernelClosed

/-!
# The zero-energy kernel of the constrained cusp form

The actual closed-gradient kernel consists of constants. Ordinary horizontal
averaging fixes those constants, and the cusp has positive measure, so the
zero-average form subspace contains no nonzero zero-energy vector. The weak
energy equation then excludes nonzero fixed vectors of its compact response.
-/

noncomputable section

namespace GapFamily.Analytic

open ModularGradient

/-- Zero actual closed-gradient energy vanishes in the zero-average cusp form space. -/
theorem meanZeroCusp_formGradient_eq_zero (u : cuspMeanZeroForm)
    (hu : formGradient (u : FormDomain) = 0) : u = 0 := by
  have hz : closedGradient
      ⟨formEmbedding (u : FormDomain),
        Dirichlet.gradientEmbedding_mem_domain closedGradient (u : FormDomain)⟩ = 0 :=
    (Dirichlet.gradientValue_apply closedGradient (u : FormDomain)).symm.trans hu
  have hconst := mem_constantSpace_of_closedGradient_eq_zero
    ⟨formEmbedding (u : FormDomain),
      Dirichlet.gradientEmbedding_mem_domain closedGradient (u : FormDomain)⟩ hz
  change meanZeroCuspEmbedding u ∈ modularConstantSpace at hconst
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hconst
  have hzero := meanZeroCusp_average_eq_zero 1 le_rfl u
  rw [← hc, map_smul, map_smul, cuspAverage_modularConstant] at hzero
  have hc0 : c = 0 :=
    (smul_eq_zero.mp hzero).resolve_right cuspRestrict_modularConstant_ne_zero
  apply meanZeroCuspEmbedding_injective
  rw [map_zero, ← hc, hc0, zero_smul]

theorem cuspMeanZeroGradient_eq_zero_iff (u : cuspMeanZeroForm) :
    cuspMeanZeroGradient u = 0 ↔ u = 0 := by
  constructor
  · exact meanZeroCusp_formGradient_eq_zero u
  · rintro rfl
    exact map_zero cuspMeanZeroGradient

theorem cuspMeanZeroGradient_injective : Function.Injective cuspMeanZeroGradient := by
  intro u v huv
  apply sub_eq_zero.mp
  apply (cuspMeanZeroGradient_eq_zero_iff (u - v)).mp
  rw [map_sub, huv, sub_self]

/-- The actual constrained weak response has no nonzero fixed vector. -/
theorem cuspMeanZeroWeakResolvent_eq_self_iff (f : ModularHilbert) :
    cuspMeanZeroWeakResolvent f = f ↔ f = 0 := by
  constructor
  · intro hf
    have h := cuspMeanZeroWeakSolution_equation f (cuspMeanZeroWeakSolution f)
    rw [hf] at h
    have he : inner ℂ (cuspMeanZeroGradient (cuspMeanZeroWeakSolution f))
        (cuspMeanZeroGradient (cuspMeanZeroWeakSolution f)) = 0 :=
      add_eq_right.mp h
    have hg : cuspMeanZeroGradient (cuspMeanZeroWeakSolution f) = 0 :=
      inner_self_eq_zero.mp he
    have hu := (cuspMeanZeroGradient_eq_zero_iff (cuspMeanZeroWeakSolution f)).mp hg
    rw [← hf, cuspMeanZeroWeakResolvent_apply, hu, map_zero]
  · rintro rfl
    exact map_zero cuspMeanZeroWeakResolvent

end GapFamily.Analytic
