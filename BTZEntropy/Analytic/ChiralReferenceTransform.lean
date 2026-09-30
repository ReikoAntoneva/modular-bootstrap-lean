import GapFamily.Analytic.Foundation.Vacuum
import GapFamily.Analytic.Transform.CosRootHalfLaplace
import BTZEntropy.Analytic.ChiralGaussianNormalization

/-! The real chiral reference density and its ordinary half-line Laplace transform. -/

noncomputable section

namespace BTZEntropy

open Set MeasureTheory
open GapFamily.Analytic GapFamily.Analytic.CosRootLaplace

/-- The denominator-one chiral vacuum factor, with its threshold weight. -/
def chiralReferenceDensity (a u : ℝ) : ℝ := vacuumDifference a u / Real.sqrt u

theorem chiralReferenceDensity_nonneg {a : ℝ} (ha : 2 ≤ a) (u : ℝ) :
    0 ≤ chiralReferenceDensity a u :=
  div_nonneg (vacuumDifference_nonneg ha) (Real.sqrt_nonneg u)

@[simp] theorem chiralReferenceDensity_zero (a : ℝ) :
    chiralReferenceDensity a 0 = 0 := by simp [chiralReferenceDensity]

/-- A single hyperbolic-cosine term of the chiral Laplace integrand. -/
def chiralCoshLaplace (a β u : ℝ) : ℝ :=
  Real.exp (-β * u / 2) * Real.cosh (2 * Real.pi * Real.sqrt (a * u)) / Real.sqrt u

theorem cosRootHalfLaplaceIntegrand_eq_chiralCoshLaplace {a u : ℝ}
    (ha : 0 ≤ a) (hu : 0 < u) (β : ℝ) :
    cosRootHalfLaplaceIntegrand ((-4 * Real.pi ^ 2 * a : ℝ) : ℂ)
      ((β / 2 : ℝ) : ℂ) u = (chiralCoshLaplace a β u : ℂ) := by
  have hp : u ^ (-(1 / 2 : ℝ)) = (Real.sqrt u)⁻¹ := by
    rw [Real.rpow_neg hu.le, ← Real.sqrt_eq_rpow]
  have hc : ((-4 * Real.pi ^ 2 * a : ℝ) : ℂ) * (u : ℂ) =
      -4 * (Real.pi : ℂ) ^ 2 * ((a * u : ℝ) : ℂ) := by push_cast; ring
  have he : -((β / 2 : ℝ) : ℂ) * (u : ℂ) = ((-β * u / 2 : ℝ) : ℂ) := by
    push_cast
    ring
  rw [cosRootHalfLaplaceIntegrand, hp, hc,
    cosRoot_neg_four_pi_sq_mul (mul_nonneg ha hu.le), he, ← Complex.ofReal_exp]
  unfold chiralCoshLaplace
  push_cast
  ring

theorem integrableOn_chiralCoshLaplace {a β : ℝ} (ha : 0 ≤ a) (hβ : 0 < β) :
    IntegrableOn (chiralCoshLaplace a β) (Ioi (0 : ℝ)) := by
  have hi := integrableOn_cosRootHalfLaplaceIntegrand
    ((-4 * Real.pi ^ 2 * a : ℝ) : ℂ) (z := ((β / 2 : ℝ) : ℂ))
    (by simpa using half_pos hβ)
  have hir := hi.re
  apply hir.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  rw [cosRootHalfLaplaceIntegrand_eq_chiralCoshLaplace ha hu β]
  rfl

theorem integral_chiralCoshLaplace_complex {a β : ℝ} (ha : 0 ≤ a) (hβ : 0 < β) :
    (((∫ u : ℝ in Ioi 0, chiralCoshLaplace a β u) : ℝ) : ℂ) =
      (Real.sqrt Real.pi : ℂ) * ((β / 2 : ℝ) : ℂ) ^ (-(1 / 2 : ℂ)) *
        Complex.exp (-((-4 * Real.pi ^ 2 * a : ℝ) : ℂ) /
          (4 * ((β / 2 : ℝ) : ℂ))) := by
  rw [← integral_complex_ofReal]
  calc
    _ = ∫ u : ℝ in Ioi 0, cosRootHalfLaplaceIntegrand
        ((-4 * Real.pi ^ 2 * a : ℝ) : ℂ) ((β / 2 : ℝ) : ℂ) u := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro u hu
      exact (cosRootHalfLaplaceIntegrand_eq_chiralCoshLaplace ha hu β).symm
    _ = _ := integral_cosRootHalfLaplaceIntegrand _ (by simpa using half_pos hβ)

theorem integral_chiralCoshLaplace {a β : ℝ} (ha : 0 ≤ a) (hβ : 0 < β) :
    (∫ u : ℝ in Ioi 0, chiralCoshLaplace a β u) =
      Real.sqrt (2 * Real.pi / β) * Real.exp (2 * Real.pi ^ 2 * a / β) := by
  apply Complex.ofReal_injective
  rw [integral_chiralCoshLaplace_complex ha hβ, chiralGaussianNormalization a hβ]

theorem chiralReferenceDensity_exp_eq (a β u : ℝ) :
    Real.exp (-β * u / 2) * chiralReferenceDensity a u =
      chiralCoshLaplace a β u - chiralCoshLaplace (a - 2) β u := by
  unfold chiralReferenceDensity vacuumDifference chiralCoshLaplace
  ring

theorem integrableOn_chiralReferenceDensity_exp {a β : ℝ}
    (ha : 2 ≤ a) (hβ : 0 < β) :
    IntegrableOn (fun u => Real.exp (-β * u / 2) * chiralReferenceDensity a u)
      (Ioi (0 : ℝ)) := by
  simp_rw [chiralReferenceDensity_exp_eq]
  exact (integrableOn_chiralCoshLaplace (by linarith : 0 ≤ a) hβ).sub
    (integrableOn_chiralCoshLaplace (by linarith : 0 ≤ a - 2) hβ)

/-- Exact chiral reference transform, retaining the finite vacuum null subtraction. -/
theorem integral_chiralReferenceDensity_exp {a β : ℝ}
    (ha : 2 ≤ a) (hβ : 0 < β) :
    (∫ u : ℝ in Ioi 0, Real.exp (-β * u / 2) * chiralReferenceDensity a u) =
      Real.sqrt (2 * Real.pi / β) * Real.exp (2 * Real.pi ^ 2 * a / β) *
        (1 - Real.exp (-4 * Real.pi ^ 2 / β)) := by
  simp_rw [chiralReferenceDensity_exp_eq]
  rw [integral_sub (integrableOn_chiralCoshLaplace (by linarith : 0 ≤ a) hβ)
    (integrableOn_chiralCoshLaplace (by linarith : 0 ≤ a - 2) hβ),
    integral_chiralCoshLaplace (by linarith : 0 ≤ a) hβ,
    integral_chiralCoshLaplace (by linarith : 0 ≤ a - 2) hβ]
  rw [show 2 * Real.pi ^ 2 * (a - 2) / β =
    2 * Real.pi ^ 2 * a / β + (-4 * Real.pi ^ 2 / β) by ring, Real.exp_add]
  ring

end BTZEntropy
