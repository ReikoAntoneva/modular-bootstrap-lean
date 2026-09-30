import BTZEntropy.Analytic.ReferenceDensity
import BTZEntropy.Analytic.ReferenceCoordinate
import BTZEntropy.Analytic.ReferenceInversionChiral

/-!
# Complex Laplace transform of the continuous primary reference

The transform is the actual absolutely convergent cone integral throughout the
right half-plane.  The lightcone Jacobian and the two chiral transforms retain
the complete null-state subtraction.
-/

noncomputable section

open Set MeasureTheory

namespace BTZEntropy

/-- The ordinary complex Laplace transform of the primary reference. -/
def complexReferencePrimaryTransform (a : ℝ) (z : ℂ) : ℂ :=
  ∫ p : ℝ × ℝ in referenceCone,
    Complex.exp (-z * p.1) * (referencePrimaryDensity a p.1 p.2 : ℂ)

/-- The complex thermal weight separates in the lightcone coordinates. -/
theorem complexReferencePrimaryThermal_lightcone (a u v : ℝ) (z : ℂ) (hu : 0 ≤ u) :
    Complex.exp (-z * (((u + v) / 2 : ℝ) : ℂ)) *
        (referencePrimaryDensity a ((u + v) / 2) ((u - v) / 2) : ℂ) =
      2 * (complexChiralReferenceLaplace a z u * complexChiralReferenceLaplace a z v) := by
  rw [referencePrimaryDensity_lightcone a u v hu]
  have hexp : -z * (((u + v) / 2 : ℝ) : ℂ) =
      -z * (u : ℂ) / 2 + -z * (v : ℂ) / 2 := by push_cast; ring
  rw [hexp, Complex.exp_add]
  unfold complexChiralReferenceLaplace chiralReferenceDensity
  push_cast
  ring

/-- Absolute integrability on the full physical cone in the right half-plane. -/
theorem integrableOn_complexReferencePrimaryThermal {a : ℝ} {z : ℂ}
    (ha : 2 ≤ a) (hz : 0 < z.re) :
    IntegrableOn (fun p : ℝ × ℝ =>
      Complex.exp (-z * p.1) * (referencePrimaryDensity a p.1 p.2 : ℂ)) referenceCone := by
  let f : ℝ × ℝ → ℂ := fun p =>
    Complex.exp (-z * p.1) * (referencePrimaryDensity a p.1 p.2 : ℂ)
  let g : ℝ → ℂ := complexChiralReferenceLaplace a z
  have hg : IntegrableOn g (Ioi 0) := integrableOn_complexChiralReferenceLaplace ha hz
  have hprod : IntegrableOn (fun p : ℝ × ℝ => 2 * (g p.1 * g p.2)) lightconeQuadrant := by
    simpa only [IntegrableOn, lightconeQuadrant, Measure.volume_eq_prod,
      ← Measure.prod_restrict] using (hg.mul_prod hg).const_mul (2 : ℂ)
  have hcomp : Integrable (fun p => f (lightconeEquiv p))
      (volume.restrict lightconeQuadrant) := by
    apply hprod.congr
    filter_upwards [ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Ioi)] with p hp
    simpa only [f, g, lightconeEquiv_apply] using
      (complexReferencePrimaryThermal_lightcone a p.1 p.2 z hp.1.le).symm
  exact (integrable_lightconeQuadrant_iff f).mp hcomp

/-- The complex cone transform factors into two identical chiral integrals. -/
theorem complexReferencePrimaryTransform_eq_square (a : ℝ) (z : ℂ) :
    complexReferencePrimaryTransform a z =
      (∫ u in Ioi (0 : ℝ), complexChiralReferenceLaplace a z u) ^ 2 := by
  unfold complexReferencePrimaryTransform
  change (∫ p in energySpinCone,
    Complex.exp (-z * p.1) * (referencePrimaryDensity a p.1 p.2 : ℂ)) = _
  rw [integral_energySpinCone]
  have heq : (∫ p in lightconeQuadrant,
      Complex.exp (-z * (lightconeEquiv p).1) *
        (referencePrimaryDensity a (lightconeEquiv p).1 (lightconeEquiv p).2 : ℂ)) =
      ∫ p in lightconeQuadrant,
        2 * (complexChiralReferenceLaplace a z p.1 *
          complexChiralReferenceLaplace a z p.2) := by
    apply setIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioi)
    intro p hp
    simpa only [lightconeEquiv_apply] using
      complexReferencePrimaryThermal_lightcone a p.1 p.2 z hp.1.le
  rw [heq, integral_const_mul, lightconeQuadrant, Measure.volume_eq_prod,
    setIntegral_prod_mul (complexChiralReferenceLaplace a z)
      (complexChiralReferenceLaplace a z)]
  simp only [Complex.real_smul, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
  ring

/-- The two branch-dependent square-root factors combine to the rational Jacobian. -/
theorem complexChiralGaussian_sq (z : ℂ) :
    ((Real.sqrt Real.pi : ℂ) * (z / 2) ^ (-(1 / 2 : ℂ))) ^ 2 =
      2 * (Real.pi : ℂ) / z := by
  rw [mul_pow, ← Complex.ofReal_pow, Real.sq_sqrt Real.pi_pos.le,
    ← Complex.cpow_nat_mul]
  norm_num
  rw [Complex.cpow_neg_one]
  simp only [inv_div]
  ring

/-- Exact complex primary-reference transform on the right half-plane. -/
theorem complexReferencePrimaryTransform_eq {a : ℝ} {z : ℂ}
    (ha : 2 ≤ a) (hz : 0 < z.re) :
    complexReferencePrimaryTransform a z =
      (2 * (Real.pi : ℂ) / z) * Complex.exp (4 * (Real.pi : ℂ) ^ 2 * a / z) *
        (1 - Complex.exp (-4 * (Real.pi : ℂ) ^ 2 / z)) ^ 2 := by
  rw [complexReferencePrimaryTransform_eq_square,
    integral_complexChiralReferenceLaplace ha hz, mul_pow, mul_pow,
    complexChiralGaussian_sq]
  rw [sq, ← Complex.exp_add,
    show 2 * (Real.pi : ℂ) ^ 2 * a / z + 2 * (Real.pi : ℂ) ^ 2 * a / z =
      4 * (Real.pi : ℂ) ^ 2 * a / z by ring]

end BTZEntropy
