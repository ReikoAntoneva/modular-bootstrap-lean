import GapFamily.Analytic.Modular.ModularMeanZeroResolventBasic
import GapFamily.Analytic.Modular.ModularPositiveResolventBasic
import Mathlib.Algebra.GroupWithZero.Commute

noncomputable section
namespace GapFamily.Analytic.ModularMeanZeroResolvent
open ModularProjected ModularPositiveResolvent

/-- Commutation survives the totalized inverse: the nonunit branch is zero. -/
private theorem commute_ring_inverse_right {M : Type*} [MonoidWithZero M]
    {a b : M} (h : Commute a b) : Commute a (Ring.inverse b) := by
  classical
  by_cases hb : IsUnit b
  · obtain ⟨u, rfl⟩ := hb
    simpa only [Ring.inverse_unit] using h.units_inv_right
  · rw [Ring.inverse_non_unit _ hb]
    exact Commute.zero_right _

/-- The literal projected response commutes with the literal full resolvent
candidate. This algebraic equality also holds at totalized nonunit parameters;
it makes no inverse or positivity claim there. -/
theorem meanZeroResolvent_fullResolvent_commute (lam : ℝ) (z : ℂ) :
    Commute (meanZeroResolvent lam) (fullResolvent z) := by
  have hBC : Commute projectedWeakResolvent modularConstantProjection := by
    change projectedWeakResolvent * modularConstantProjection =
      modularConstantProjection * projectedWeakResolvent
    apply ContinuousLinearMap.ext
    intro f
    change projectedWeakResolvent (modularConstantProjection f) =
      modularConstantProjection (projectedWeakResolvent f)
    rw [constantProjection_projectedWeakResolvent, modularConstantProjection_apply,
      map_smul, projectedWeakResolvent_constant, smul_zero]
  have hBP (w : ℂ) : Commute projectedWeakResolvent (projectedPencil w) := by
    exact (Commute.one_right projectedWeakResolvent).sub_right
      ((Commute.refl projectedWeakResolvent).smul_right (w + 1))
  have hPC : Commute (projectedPencil (lam : ℂ)) modularConstantProjection := by
    exact (Commute.one_left modularConstantProjection).sub_left
      (hBC.smul_left ((lam : ℂ) + 1))
  have hPP : Commute (projectedPencil (lam : ℂ)) (projectedPencil z) := by
    exact (Commute.one_left (projectedPencil z)).sub_left
      ((hBP z).smul_left ((lam : ℂ) + 1))
  have hIB : Commute (Ring.inverse (projectedPencil (lam : ℂ))) projectedWeakResolvent :=
    (commute_ring_inverse_right (hBP (lam : ℂ))).symm
  have hIC : Commute (Ring.inverse (projectedPencil (lam : ℂ))) modularConstantProjection :=
    (commute_ring_inverse_right hPC.symm).symm
  have hII : Commute (Ring.inverse (projectedPencil (lam : ℂ)))
      (Ring.inverse (projectedPencil z)) := hPP.ringInverse_ringInverse
  have hBI : Commute projectedWeakResolvent (Ring.inverse (projectedPencil z)) :=
    commute_ring_inverse_right (hBP z)
  change Commute
    (projectedWeakResolvent * Ring.inverse (projectedPencil (lam : ℂ)))
    (projectedWeakResolvent * Ring.inverse (projectedPencil z) -
      z⁻¹ • modularConstantProjection)
  exact (((Commute.refl projectedWeakResolvent).mul_left hIB).mul_right
    (hBI.mul_left hII)).sub_right ((hBC.mul_left hIC).smul_right z⁻¹)

/-- The actual projected response commutes with every negative-shift candidate. -/
theorem meanZeroResolvent_shiftedResolvent_commute (lam r : ℝ) :
    Commute (meanZeroResolvent lam) (shiftedResolvent r) :=
  meanZeroResolvent_fullResolvent_commute lam (-(r : ℂ))

/-- The actual projected response commutes with every normalized factor.
The physical application uses lam < 1/4 and r > 0, but this identity needs no bound. -/
theorem meanZeroResolvent_resolventFactor_commute (lam r : ℝ) :
    Commute (meanZeroResolvent lam) (resolventFactor r) :=
  (meanZeroResolvent_shiftedResolvent_commute lam r).smul_right (r : ℂ)

end GapFamily.Analytic.ModularMeanZeroResolvent
