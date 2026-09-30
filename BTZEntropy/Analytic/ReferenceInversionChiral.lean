import BTZEntropy.Analytic.ChiralReferenceTransform

/-! Exact complex chiral reference transforms on the open right half-plane. -/

noncomputable section

namespace BTZEntropy

open Set MeasureTheory
open GapFamily.Analytic GapFamily.Analytic.CosRootLaplace

/-- One hyperbolic-cosine term of the chiral reference transform. -/
def complexChiralCoshLaplace (a : ℝ) (z : ℂ) (u : ℝ) : ℂ :=
  Complex.exp (-z * (u : ℂ) / 2) *
    (Real.cosh (2 * Real.pi * Real.sqrt (a * u)) : ℂ) / (Real.sqrt u : ℂ)

theorem cosRootHalfLaplaceIntegrand_eq_complexChiralCoshLaplace {a u : ℝ}
    (ha : 0 ≤ a) (hu : 0 < u) (z : ℂ) :
    cosRootHalfLaplaceIntegrand ((-4 * Real.pi ^ 2 * a : ℝ) : ℂ)
      (z / 2) u = complexChiralCoshLaplace a z u := by
  have hp : u ^ (-(1 / 2 : ℝ)) = (Real.sqrt u)⁻¹ := by
    rw [Real.rpow_neg hu.le, ← Real.sqrt_eq_rpow]
  have hc : ((-4 * Real.pi ^ 2 * a : ℝ) : ℂ) * (u : ℂ) =
      -4 * (Real.pi : ℂ) ^ 2 * ((a * u : ℝ) : ℂ) := by push_cast; ring
  have he : -(z / 2) * (u : ℂ) = -z * (u : ℂ) / 2 := by ring
  rw [cosRootHalfLaplaceIntegrand, hp, hc,
    cosRoot_neg_four_pi_sq_mul (mul_nonneg ha hu.le), he]
  unfold complexChiralCoshLaplace
  push_cast
  ring

theorem integrableOn_complexChiralCoshLaplace {a : ℝ} {z : ℂ}
    (ha : 0 ≤ a) (hz : 0 < z.re) :
    IntegrableOn (complexChiralCoshLaplace a z) (Ioi (0 : ℝ)) := by
  have hi := integrableOn_cosRootHalfLaplaceIntegrand
    ((-4 * Real.pi ^ 2 * a : ℝ) : ℂ) (z := z / 2)
    (by simpa using half_pos hz)
  apply hi.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  exact cosRootHalfLaplaceIntegrand_eq_complexChiralCoshLaplace ha hu z

/-- Ordinary Bochner transform of one chiral hyperbolic-cosine term. -/
theorem integral_complexChiralCoshLaplace {a : ℝ} {z : ℂ}
    (ha : 0 ≤ a) (hz : 0 < z.re) :
    (∫ u : ℝ in Ioi 0, complexChiralCoshLaplace a z u) =
      (Real.sqrt Real.pi : ℂ) * (z / 2) ^ (-(1 / 2 : ℂ)) *
        Complex.exp (2 * (Real.pi : ℂ) ^ 2 * (a : ℂ) / z) := by
  calc
    _ = ∫ u : ℝ in Ioi 0, cosRootHalfLaplaceIntegrand
        ((-4 * Real.pi ^ 2 * a : ℝ) : ℂ) (z / 2) u := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro u hu
      exact (cosRootHalfLaplaceIntegrand_eq_complexChiralCoshLaplace ha hu z).symm
    _ = _ := by
      rw [integral_cosRootHalfLaplaceIntegrand _ (by simpa using half_pos hz)]
      congr 2
      push_cast
      ring

/-- Complex thermal weighting of the actual chiral vacuum reference density. -/
def complexChiralReferenceLaplace (a : ℝ) (z : ℂ) (u : ℝ) : ℂ :=
  Complex.exp (-z * (u : ℂ) / 2) * (chiralReferenceDensity a u : ℂ)

theorem complexChiralReferenceLaplace_eq (a : ℝ) (z : ℂ) (u : ℝ) :
    complexChiralReferenceLaplace a z u =
      complexChiralCoshLaplace a z u - complexChiralCoshLaplace (a - 2) z u := by
  unfold complexChiralReferenceLaplace chiralReferenceDensity vacuumDifference
    complexChiralCoshLaplace
  push_cast
  ring

theorem integrableOn_complexChiralReferenceLaplace {a : ℝ} {z : ℂ}
    (ha : 2 ≤ a) (hz : 0 < z.re) :
    IntegrableOn (complexChiralReferenceLaplace a z) (Ioi (0 : ℝ)) := by
  change IntegrableOn (fun u => complexChiralReferenceLaplace a z u) _
  simp_rw [complexChiralReferenceLaplace_eq]
  exact (integrableOn_complexChiralCoshLaplace (by linarith : 0 ≤ a) hz).sub
    (integrableOn_complexChiralCoshLaplace (by linarith : 0 ≤ a - 2) hz)

/-- The complex chiral reference transform, including the exact vacuum subtraction. -/
theorem integral_complexChiralReferenceLaplace {a : ℝ} {z : ℂ}
    (ha : 2 ≤ a) (hz : 0 < z.re) :
    (∫ u : ℝ in Ioi 0, complexChiralReferenceLaplace a z u) =
      (Real.sqrt Real.pi : ℂ) * (z / 2) ^ (-(1 / 2 : ℂ)) *
        Complex.exp (2 * (Real.pi : ℂ) ^ 2 * (a : ℂ) / z) *
        (1 - Complex.exp (-4 * (Real.pi : ℂ) ^ 2 / z)) := by
  simp_rw [complexChiralReferenceLaplace_eq]
  rw [integral_sub (integrableOn_complexChiralCoshLaplace (by linarith : 0 ≤ a) hz)
    (integrableOn_complexChiralCoshLaplace (by linarith : 0 ≤ a - 2) hz),
    integral_complexChiralCoshLaplace (by linarith : 0 ≤ a) hz,
    integral_complexChiralCoshLaplace (by linarith : 0 ≤ a - 2) hz]
  push_cast
  rw [show 2 * (Real.pi : ℂ) ^ 2 * ((a : ℂ) - 2) / z =
    2 * (Real.pi : ℂ) ^ 2 * (a : ℂ) / z + (-4 * (Real.pi : ℂ) ^ 2 / z) by ring,
    Complex.exp_add]
  ring

end BTZEntropy
