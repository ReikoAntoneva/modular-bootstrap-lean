import BTZEntropy.Comparison.DensityError
import BTZEntropy.Construction.FixedFamilyData
import GapFamily.Construction.ThermalEnvelopeBound

/-!
# Density-error estimates for the actual finite repair state

The numerator and front below are read from the same stored recurrence state
that supplies the permanent spectrum. The error input is discharged by its
proved envelope invariant; no substitute density or asymptotic assertion is
introduced.
-/

noncomputable section

open Set MeasureTheory Real
open GapFamily GapFamily.Analytic GapFamily.Construction

namespace BTZEntropy.Comparison

/-- The literal difference between a finite state's continuum numerator and
the denominator-one vacuum reference numerator. -/
def finiteStateDensityError (a : ℝ) (s : FiniteRepairState) (j : ℤ) (e : ℝ) : ℝ :=
  s.numerator j e - vacuumLeading a e j

/-- Thermal integrability already present in the construction supplies the
measurability needed for ordinary compact-test integration. -/
theorem finiteStateNumerator_aestronglyMeasurable (s : FiniteRepairState)
    (hs : s.ThermalIntegrable) (j : ℤ) :
    AEStronglyMeasurable (s.numerator j) (referenceMeasure j) := by
  have h := continuous_exp.aestronglyMeasurable.mul (hs j 1 (by norm_num)).aestronglyMeasurable
  apply h.congr
  exact Filter.Eventually.of_forall (fun e => by
    simp only [Pi.mul_apply, one_mul, neg_mul]
    rw [← mul_assoc, ← exp_add]
    simp)

theorem continuous_densityErrorReference (a : ℝ) (j : ℤ) :
    Continuous (fun e => vacuumLeading a e j) := by
  have h := (continuous_tailEnvelopeNumerator a j).sub
    (show Continuous (fun e : ℝ => exp (7 * sqrt (a * e))) by fun_prop)
  apply h.congr
  intro e
  simp [tailEnvelopeNumerator]

theorem finiteStateDensityError_aestronglyMeasurable (a : ℝ) (s : FiniteRepairState)
    (hs : s.ThermalIntegrable) (j : ℤ) :
    AEStronglyMeasurable (finiteStateDensityError a s j) (referenceMeasure j) :=
  (finiteStateNumerator_aestronglyMeasurable s hs j).sub
    (continuous_densityErrorReference a j).aestronglyMeasurable

namespace FixedFamilyDatum

variable {B : ℝ} {g : BTZEntropy.Construction.FixedFamilyGeometry B}
  {a : ℝ} {δ : ℝ} (d : BTZEntropy.Construction.FixedFamilyDatum g a δ)

theorem state_front_one (n : ℕ) (j : ℤ) : 1 ≤ (d.state n).front j := by
  have h := (d.state_spec n).2.2.2.1 j
  have ht : (1 : ℝ) ≤ (g.start : ℝ) := by exact_mod_cast g.start_pos
  exact ht.trans ((show (g.start : ℝ) ≤ ((g.start + n : ℕ) : ℝ) by
    exact_mod_cast Nat.le_add_right g.start n).trans
    ((le_max_left _ _).trans h))

theorem state_front_spin (n : ℕ) (j : ℤ) : |(j : ℝ)| ≤ (d.state n).front j :=
  (le_max_right _ _).trans ((d.state_spec n).2.2.2.1 j)

/-- The genuine recurrence envelope bounds the same stored density used in
the complete modular and permanent-spectrum construction. -/
theorem state_densityError_bound (n : ℕ) (j : ℤ) :
    ∀ᵐ e ∂referenceMeasure j, (d.state n).front j ≤ e →
      |finiteStateDensityError (shift (gapFamilyCharge a)) (d.state n) j e| ≤
        exp (7 * sqrt (shift (gapFamilyCharge a) * e)) :=
  Filter.Eventually.of_forall (fun e he => (d.state_spec n).2.2.2.2 j e he)

/-- Every ordinary finite-state density-error row is integrable when tested
by any of the actual descendant packets. -/
theorem state_densityErrorRow_integrable (φ : SmoothKernel) (n : ℕ)
    (F : Finset (ℕ × ℕ)) {c x U R H V : ℝ}
    (hc : 1 ≤ c) (hx : x ≤ U) (hR0 : 0 ≤ R) (hH : 0 ≤ H)
    (hR : ∀ u, φ u ≠ 0 → u ≤ R) (hφ : ∀ u, φ u ≤ H) (j : ℤ) :
    IntegrableOn (fun e =>
      finiteStateDensityError (shift (gapFamilyCharge a)) (d.state n) j e *
        primaryDescendantTest φ (x * c) F e)
      (Ioo ((d.state n).front j) V) (referenceMeasure j) := by
  apply densityErrorRow_integrable φ (x * c) R (shift (gapFamilyCharge a))
    (H * exp ((U + R + 1 / 12 + 4) * sqrt c)) F
    (finiteStateDensityError (shift (gapFamilyCharge a)) (d.state n))
    (d.state n).front V j
    (by linarith [d.charge_large]) (by positivity) (state_front_one d n j)
    (state_front_spin d n j) hR
    (fun e he => primaryDescendantTest_le_sqrt φ F he hc hx hR0 hH hR hφ)
    (finiteStateDensityError_aestronglyMeasurable _ _ (d.state_spec n).2.1 j)
  filter_upwards [ae_restrict_of_ae (state_densityError_bound d n j),
    ae_restrict_mem measurableSet_Ioo] with e he heV
  exact he heV.1.le

/-- The explicit quadratic/root-exponential bound is instantiated on the
actual old numerator at every finite stage, uniformly in the marker and
node selector retained by the datum. -/
theorem state_densityErrorFullPacket_abs_le (φ : SmoothKernel) (n : ℕ)
    (F : Finset (ℕ × ℕ)) {x U R H : ℝ}
    (hx0 : 0 ≤ x) (hx : x ≤ U) (hR0 : 0 ≤ R) (hH : 0 ≤ H)
    (hR : ∀ u, φ u ≠ 0 → u ≤ R) (hφ : ∀ u, φ u ≤ H) :
    |densityErrorFullPacket φ (x * gapFamilyCharge a) F
      (finiteStateDensityError (shift (gapFamilyCharge a)) (d.state n))
        (d.state n).front| ≤
      ((2 * (U + R + 3) + 1) * (U + R + 3) * H) * (1 + gapFamilyCharge a) ^ 2 *
        exp (7 * sqrt (shift (gapFamilyCharge a) *
          (x * gapFamilyCharge a + R + 1 / 12)) +
            (U + R + 1 / 12 + 4) * sqrt (gapFamilyCharge a)) := by
  have hc : 1 ≤ gapFamilyCharge a := by
    have h := d.charge_large
    unfold shift at h
    linarith
  exact densityErrorFullPacket_abs_le_polynomial φ F
    (finiteStateDensityError (shift (gapFamilyCharge a)) (d.state n))
    (d.state n).front (by linarith [d.charge_large]) hc hx0 hx hR0 hH
    (state_front_one d n) (state_front_spin d n) hR hφ (state_densityError_bound d n)

end FixedFamilyDatum

end BTZEntropy.Comparison
