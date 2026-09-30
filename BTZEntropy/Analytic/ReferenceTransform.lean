import BTZEntropy.Analytic.ReferenceDensity
import BTZEntropy.Analytic.ReferenceCoordinate
import BTZEntropy.Analytic.ChiralReferenceTransform

/-!
# Exact primary reference transform

This is the ordinary thermal transform of the actual continuous-spin extension
of `vacuumLeading`, not a definition by its answer. The proof uses the literal
lightcone Jacobian and two absolutely convergent chiral Gaussian integrals.
-/

noncomputable section

open Set MeasureTheory
open scoped ENNReal

namespace BTZEntropy

/-- Absolute integrability of the primary reference on its full energy-spin cone. -/
theorem integrableOn_referencePrimaryThermal {a β : ℝ} (ha : 2 ≤ a) (hβ : 0 < β) :
    IntegrableOn (fun p : ℝ × ℝ =>
      Real.exp (-β * p.1) * referencePrimaryDensity a p.1 p.2) referenceCone := by
  let f : ℝ × ℝ → ℝ := fun p =>
    Real.exp (-β * p.1) * referencePrimaryDensity a p.1 p.2
  let g : ℝ → ℝ := fun u => Real.exp (-β * u / 2) * chiralReferenceDensity a u
  have hg : IntegrableOn g (Ioi 0) := integrableOn_chiralReferenceDensity_exp ha hβ
  have hprod : IntegrableOn (fun p : ℝ × ℝ => 2 * (g p.1 * g p.2)) lightconeQuadrant := by
    simpa only [IntegrableOn, lightconeQuadrant, Measure.volume_eq_prod,
      ← Measure.prod_restrict] using (hg.mul_prod hg).const_mul (2 : ℝ)
  have hcomp : Integrable (f ∘ lightconeEquiv) (volume.restrict lightconeQuadrant) := by
    apply hprod.congr
    filter_upwards [ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Ioi)] with p hp
    simpa only [f, g, Function.comp_apply, lightconeEquiv_apply,
      chiralReferenceDensity, mul_assoc] using
      (referencePrimaryThermal_lightcone a β p.1 p.2 hp.1.le).symm
  have hmap : Integrable f (Measure.map lightconeEquiv (volume.restrict lightconeQuadrant)) :=
    (integrable_map_equiv lightconeEquiv.toHomeomorph.toMeasurableEquiv f).mpr hcomp
  rw [map_lightconeQuadrant] at hmap
  exact (integrable_smul_measure (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (by norm_num : (2 : ℝ≥0∞) ≠ ∞)).mp hmap

/-- The cone integral is the square of one genuine chiral reference integral. -/
theorem referencePrimaryTransform_eq_square (a β : ℝ) :
    referencePrimaryTransform a β =
      (∫ u in Ioi (0 : ℝ), Real.exp (-β * u / 2) * chiralReferenceDensity a u) ^ 2 := by
  unfold referencePrimaryTransform
  change (∫ p in energySpinCone,
    Real.exp (-β * p.1) * referencePrimaryDensity a p.1 p.2) = _
  rw [integral_energySpinCone]
  have heq : (∫ p in lightconeQuadrant,
      Real.exp (-β * (lightconeEquiv p).1) *
        referencePrimaryDensity a (lightconeEquiv p).1 (lightconeEquiv p).2) =
      ∫ p in lightconeQuadrant,
        2 * ((Real.exp (-β * p.1 / 2) * chiralReferenceDensity a p.1) *
          (Real.exp (-β * p.2 / 2) * chiralReferenceDensity a p.2)) := by
    apply setIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioi)
    intro p hp
    simpa only [lightconeEquiv_apply, chiralReferenceDensity, mul_assoc] using
      referencePrimaryThermal_lightcone a β p.1 p.2 hp.1.le
  rw [heq, integral_const_mul]
  rw [lightconeQuadrant, Measure.volume_eq_prod,
    setIntegral_prod_mul
      (fun u : ℝ => Real.exp (-β * u / 2) * chiralReferenceDensity a u)
      (fun u : ℝ => Real.exp (-β * u / 2) * chiralReferenceDensity a u)]
  simp only [smul_eq_mul]
  ring

/-- Section 6.2's exact primary reference transform, with both null-state factors. -/
theorem referencePrimaryTransform_eq {a β : ℝ} (ha : 2 ≤ a) (hβ : 0 < β) :
    referencePrimaryTransform a β =
      (2 * Real.pi / β) * Real.exp (4 * Real.pi ^ 2 * a / β) *
        (1 - Real.exp (-4 * Real.pi ^ 2 / β)) ^ 2 := by
  rw [referencePrimaryTransform_eq_square, integral_chiralReferenceDensity_exp ha hβ,
    mul_pow, mul_pow, Real.sq_sqrt (by positivity : 0 ≤ 2 * Real.pi / β)]
  rw [sq, ← Real.exp_add,
    show 2 * Real.pi ^ 2 * a / β + 2 * Real.pi ^ 2 * a / β =
      4 * Real.pi ^ 2 * a / β by ring]

theorem referencePrimaryTransform_pos {a β : ℝ} (ha : 2 ≤ a) (hβ : 0 < β) :
    0 < referencePrimaryTransform a β := by
  rw [referencePrimaryTransform_eq ha hβ]
  have hnull : 0 < 1 - Real.exp (-4 * Real.pi ^ 2 / β) := by
    apply sub_pos.mpr
    apply Real.exp_lt_one_iff.mpr
    exact div_neg_of_neg_of_pos (by nlinarith [sq_pos_of_pos Real.pi_pos]) hβ
  positivity

/-- The defined transform is exactly the paper's energy-then-spin integral. -/
theorem referencePrimaryTransform_eq_iterated {a β : ℝ} (ha : 2 ≤ a) (hβ : 0 < β) :
    referencePrimaryTransform a β =
      ∫ E in Ioi (0 : ℝ), Real.exp (-β * E) *
        ∫ J in Ioo (-E) E,
          continuousSpinLeading a E J / Real.sqrt (E ^ 2 - J ^ 2) := by
  rw [referencePrimaryTransform,
    integral_referenceCone_eq_iterated _ (integrableOn_referencePrimaryThermal ha hβ)]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro E _
  change (∫ J in Ioo (-E) E, Real.exp (-β * E) * referencePrimaryDensity a E J) = _
  rw [integral_const_mul]
  rfl

/-- The literal nested integral has the claimed closed value. -/
theorem integral_continuousSpinLeading_eq {a β : ℝ} (ha : 2 ≤ a) (hβ : 0 < β) :
    (∫ E in Ioi (0 : ℝ), Real.exp (-β * E) *
      ∫ J in Ioo (-E) E,
        continuousSpinLeading a E J / Real.sqrt (E ^ 2 - J ^ 2)) =
      (2 * Real.pi / β) * Real.exp (4 * Real.pi ^ 2 * a / β) *
        (1 - Real.exp (-4 * Real.pi ^ 2 / β)) ^ 2 := by
  rw [← referencePrimaryTransform_eq_iterated ha hβ, referencePrimaryTransform_eq ha hβ]

end BTZEntropy
