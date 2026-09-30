import GapFamily.Analytic.Modular.Geometry.ModularCoordinate
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# Local Lebesgue integrability of modular coordinate vectors

The actual hyperbolic measure restricts to the same inverse-square density
on each compact subset of the open fundamental region. Multiplication by the
bounded factor `y²` therefore transfers local integrability to Lebesgue measure.
-/

noncomputable section

namespace GapFamily.Analytic

open Set MeasureTheory

/-- Restricting the actual coordinate measure gives the literal local density. -/
theorem restrict_modularCoordinateMeasure {K : Set ℂ}
    (hK : MeasurableSet K) (hKU : K ⊆ modularInterior) :
    modularCoordinateMeasure.restrict K = Dirichlet.localHyperbolicMeasure K := by
  rw [modularCoordinateMeasure, Dirichlet.localHyperbolicMeasure,
    restrict_withDensity hK, Measure.restrict_restrict hK,
    inter_eq_left.mpr hKU]
  rfl

/-- Every modular `L²` representative is Lebesgue integrable on each compact
subset of the actual open fundamental region. -/
theorem modularCoordinate_integrableOn_compact (f : ModularCoordinateHilbert)
    {K : Set ℂ} (hK : IsCompact K) (hKU : K ⊆ modularInterior) :
    IntegrableOn (fun z => f z) K volume := by
  have hf : Integrable (fun z => f z) modularCoordinateMeasure :=
    (Lp.memLp f).integrable (by norm_num)
  have hweighted : IntegrableOn (fun z => (z.im : ℂ) ^ 2 * f z) K
      modularCoordinateMeasure :=
    hf.integrableOn.continuousOn_mul (by fun_prop) hK
  rw [IntegrableOn, restrict_modularCoordinateMeasure hK.measurableSet hKU] at hweighted
  exact (Dirichlet.localHyperbolic_integrable_im_sq_mul_iff hK.measurableSet
    (fun z hz => im_pos_of_mem_modularInterior (hKU hz)) (fun z => f z)).mp hweighted

/-- The actual coordinate representative of a modular `L²` vector is locally
Lebesgue integrable in the interior. -/
theorem modularCoordinate_locallyIntegrableOn (f : ModularCoordinateHilbert) :
    LocallyIntegrableOn (fun z => f z) modularInterior volume := by
  rw [locallyIntegrableOn_iff isOpen_modularInterior.isLocallyClosed]
  exact fun K hKU hK => modularCoordinate_integrableOn_compact f hK hKU

/-- Dividing an actual modular `L²` component by height remains locally
Lebesgue integrable in the interior. -/
theorem modularCoordinate_div_im_locallyIntegrableOn (f : ModularCoordinateHilbert) :
    LocallyIntegrableOn (fun z => f z / (z.im : ℂ)) modularInterior volume := by
  have hc : ContinuousOn (fun z : ℂ => (z.im : ℂ)⁻¹) modularInterior := by
    apply ContinuousOn.inv₀
    · fun_prop
    · intro z hz
      exact_mod_cast (im_pos_of_mem_modularInterior hz).ne'
  simpa only [div_eq_mul_inv] using
    (modularCoordinate_locallyIntegrableOn f).mul_continuousOn hc
      isOpen_modularInterior.isLocallyClosed

end GapFamily.Analytic
