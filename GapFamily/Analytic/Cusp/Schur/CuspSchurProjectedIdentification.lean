import GapFamily.Analytic.Modular.ModularFullProjectedResolvent
import GapFamily.Analytic.Cusp.Schur.CuspSchurNearThreshold
import GapFamily.Analytic.Cusp.Schur.CuspLocalSchurPhysical

noncomputable section
namespace GapFamily.Analytic.CuspSchurLocal
open ModularGradient ModularProjected Filter
open scoped Topology

/-- Two independently constructed actual inverses agree whenever their proved
regularity hypotheses hold. -/
theorem fullResolvent_eq_actualSchurResolvent_of_units {z : ℂ}
    (hQ : IsUnit (projectedPencil z)) (hz : z ≠ 0)
    (hV : IsUnit (cuspMeanZeroPencil z)) (hW : IsUnit (cuspScalarPencil z))
    (hD : CuspSchur.actualSchurDenominator z ≠ 0) :
    fullResolvent z = CuspSchur.actualSchurResolvent z := by
  apply ContinuousLinearMap.ext
  intro f
  let x : laplacian.domain := ⟨CuspSchur.actualSchurResolvent z f,
    CuspSchur.actualSchurResolvent_mem_domain_of_units hV hW hD f⟩
  have hright : laplacian x - z • (x : ModularHilbert) = f :=
    CuspSchur.actualSchurResolvent_rightInverse_of_units hV hW hD f
  have hleft := fullResolvent_leftInverse_of_isUnit hQ hz x
  rw [hright] at hleft
  exact hleft

/-- The actual full inverse and the actual Schur inverse agree throughout a
sufficiently small physical neighborhood, excluding the unrelated zero mode. -/
theorem fullResolvent_eventually_eq_actualSchur_near_zero :
    ∀ᶠ κ in 𝓝 (0 : ℂ), 0 < κ.re → κ ≠ 1 / 2 →
      fullResolvent (parameter κ) = CuspSchur.actualSchurResolvent (parameter κ) := by
  filter_upwards [CuspSchur.actualSchur_eventually_regular_near_zero]
    with κ hreg hκ hhalf
  obtain ⟨hV, hW, hD⟩ := hreg hκ
  exact fullResolvent_eq_actualSchurResolvent_of_units
    (projectedPencil_isUnit_physical hκ) (physical_parameter_ne_zero hκ hhalf) hV hW hD

/-- The correction precisely removes the constant-channel term of the full inverse. -/
theorem fullResolvent_constant_correction (z : ℂ) :
    fullResolvent z + z⁻¹ • modularConstantProjection =
      projectedWeakResolvent.comp (Ring.inverse (projectedPencil z)) := by
  unfold fullResolvent
  exact sub_add_cancel _ _

end GapFamily.Analytic.CuspSchurLocal
