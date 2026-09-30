import GapFamily.Analytic.Foundation.SpectralScattering
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# The ordinary zeta reciprocal at its removable zero

The completed-zeta reciprocal requires the real Gamma factor to give the
ordinary reciprocal used by Kloosterman Dirichlet series. This normalization
has derivative one at the pole of the ordinary Riemann zeta function.
-/

noncomputable section

namespace GapFamily.Analytic

open Complex Filter
open scoped Topology

/-- The ordinary zeta reciprocal with its zero at one filled analytically. -/
def ordinaryZetaReciprocal (z : ℂ) : ℂ :=
  Complex.Gammaℝ z * spectralZetaReciprocal z

@[simp] theorem ordinaryZetaReciprocal_one : ordinaryZetaReciprocal 1 = 0 := by
  simp [ordinaryZetaReciprocal]

theorem ordinaryZetaReciprocal_eq_inv {z : ℂ} (hz0 : z ≠ 0) (hz1 : z ≠ 1) :
    ordinaryZetaReciprocal z = (riemannZeta z)⁻¹ := by
  rw [ordinaryZetaReciprocal, spectralZetaReciprocal_eq_inv hz0 hz1,
    riemannZeta_def_of_ne_zero hz0, inv_div, div_eq_mul_inv]

theorem gammaReal_analyticAt_of_re_pos {z : ℂ} (hz : 0 < z.re) :
    AnalyticAt ℂ Complex.Gammaℝ z := by
  have h := (Complex.differentiable_Gammaℝ_inv.analyticAt z).inv
    (inv_ne_zero (Complex.Gammaℝ_ne_zero_of_re_pos hz))
  convert h using 1
  ext w
  exact (inv_inv (Complex.Gammaℝ w)).symm

theorem ordinaryZetaReciprocal_analyticAt {z : ℂ} (hz : 1 ≤ z.re) :
    AnalyticAt ℂ ordinaryZetaReciprocal z :=
  (gammaReal_analyticAt_of_re_pos (by linarith)).mul
    (spectralZetaReciprocal_analyticAt hz)

/-- The ordinary zeta pole has residue one. -/
theorem ordinaryZetaReciprocal_hasDerivAt_one :
    HasDerivAt ordinaryZetaReciprocal 1 1 := by
  have hg := (gammaReal_analyticAt_of_re_pos (z := 1) (by norm_num)).differentiableAt.hasDerivAt
  convert hg.mul spectralZetaReciprocal_hasDerivAt_one using 1 <;> first | rfl | simp

theorem ordinaryZetaReciprocal_two_mul_analyticAt {s : ℂ} (hs : 1 / 2 ≤ s.re) :
    AnalyticAt ℂ (fun z : ℂ => ordinaryZetaReciprocal (2 * z)) s := by
  have harg : AnalyticAt ℂ (fun z : ℂ => 2 * z) s := analyticAt_const.mul analyticAt_id
  exact (ordinaryZetaReciprocal_analyticAt (z := 2 * s) (by
    simp only [mul_re]; norm_num; linarith)).comp harg

theorem ordinaryZetaReciprocal_two_mul_hasDerivAt_half :
    HasDerivAt (fun z : ℂ => ordinaryZetaReciprocal (2 * z)) 2 (1 / 2) := by
  have harg : HasDerivAt (fun s : ℂ => 2 * s) 2 (1 / 2) := by
    simpa using (hasDerivAt_id (1 / 2 : ℂ)).const_mul 2
  have hrec : HasDerivAt ordinaryZetaReciprocal 1 (2 * (1 / 2 : ℂ)) := by
    norm_num
    exact ordinaryZetaReciprocal_hasDerivAt_one
  convert hrec.comp (1 / 2 : ℂ) harg using 1 <;> first | rfl | norm_num

end GapFamily.Analytic
