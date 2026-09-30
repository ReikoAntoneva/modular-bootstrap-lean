import BTZEntropy.Construction.FixedFamilyReference

/-!
# Uniform charge bounds for the initial packet mass

The constants depend only on the fixed family geometry. The estimate retains
the actual initial node count, including repeated nodes selected by the cells.
-/

noncomputable section

namespace BTZEntropy.Construction

open GapFamily GapFamily.Construction Real

/-- A fixed coefficient accounting for every initial spin row. -/
def fixedFamilyPacketMassCoefficient {B : ℝ} (g : FixedFamilyGeometry B) : ℝ :=
  ((realInitialRows g.radius).card : ℝ) *
    |fixedCutoffReferenceCompactMassCoefficient (g.upper / g.clearing + 1)|

/-- The square-root charge rate determined by the common initial upper endpoint. -/
def fixedFamilyPacketMassExponent {B : ℝ} (g : FixedFamilyGeometry B) : ℝ :=
  fixedCutoffReferenceCompactMassExponent 2 * sqrt g.upper

theorem fixedFamilyPacketMassCoefficient_nonneg {B : ℝ} (g : FixedFamilyGeometry B) :
    0 ≤ fixedFamilyPacketMassCoefficient g := by
  unfold fixedFamilyPacketMassCoefficient
  positivity

theorem fixedFamilyPacketMassExponent_nonneg {B : ℝ} (g : FixedFamilyGeometry B) :
    0 ≤ fixedFamilyPacketMassExponent g :=
  mul_nonneg (fixedCutoffReferenceCompactMassExponent_pos 2).le (sqrt_nonneg _)

/-- Convert the exact shifted-charge mass budget into a bound using the charge. -/
theorem fixedFamilyInitialMassBound_le_charge {B : ℝ} (g : FixedFamilyGeometry B)
    (a : ℝ) (ha : 0 ≤ a) :
    fixedFamilyInitialMassBound g a ≤
      |fixedCutoffReferenceCompactMassCoefficient (g.upper / g.clearing + 1)| *
        (1 + gapFamilyCharge a) ^ 9 *
        exp (fixedFamilyPacketMassExponent g * sqrt (gapFamilyCharge a)) := by
  have ha' : 0 ≤ shift (gapFamilyCharge a) := by
    simpa using ha
  have hc : 0 ≤ gapFamilyCharge a := by
    unfold gapFamilyCharge
    positivity
  have hac : shift (gapFamilyCharge a) ≤ gapFamilyCharge a := by
    unfold shift at *
    linarith
  have hp : (1 + shift (gapFamilyCharge a)) ^ 9 ≤ (1 + gapFamilyCharge a) ^ 9 := by
    gcongr
  have hsqrt : sqrt (shift (gapFamilyCharge a) * g.upper) ≤
      sqrt g.upper * sqrt (gapFamilyCharge a) := by
    calc
      _ ≤ sqrt (gapFamilyCharge a * g.upper) :=
        sqrt_le_sqrt (mul_le_mul_of_nonneg_right hac g.upper_nonneg)
      _ = _ := by rw [sqrt_mul hc]; ring
  have hE := (fixedCutoffReferenceCompactMassExponent_pos 2).le
  have hexp : exp (fixedCutoffReferenceCompactMassExponent 2 *
      sqrt (shift (gapFamilyCharge a) * g.upper)) ≤
      exp (fixedFamilyPacketMassExponent g * sqrt (gapFamilyCharge a)) := by
    apply exp_le_exp.mpr
    calc
      _ ≤ fixedCutoffReferenceCompactMassExponent 2 *
          (sqrt g.upper * sqrt (gapFamilyCharge a)) :=
        mul_le_mul_of_nonneg_left hsqrt hE
      _ = _ := by unfold fixedFamilyPacketMassExponent; ring
  unfold fixedFamilyInitialMassBound
  exact mul_le_mul
    (mul_le_mul (le_abs_self _) hp (by positivity) (abs_nonneg _))
    hexp (exp_pos _).le (by positivity)

namespace FixedFamilyDatum

variable {B : ℝ} {g : FixedFamilyGeometry B} {a : ℝ} {δ : ℝ}

/-- The actual initial list obeys the common square-root charge mass bound. -/
theorem initial_nodes_length_le_charge (d : FixedFamilyDatum g a δ)
    (hbound : d.HasBounds (fixedFamilyBounds g)) :
    (d.initialState.nodes.length : ℝ) ≤
      fixedFamilyPacketMassCoefficient g * (1 + gapFamilyCharge a) ^ 9 *
        exp (fixedFamilyPacketMassExponent g * sqrt (gapFamilyCharge a)) := by
  have hcount : (d.initialState.nodes.length : ℝ) ≤
      ((realInitialRows g.radius).card : ℝ) * fixedFamilyInitialMassBound g a := by
    simpa [fixedFamilyBounds] using hbound.initial_nodes_length_le
  calc
    _ ≤ ((realInitialRows g.radius).card : ℝ) * fixedFamilyInitialMassBound g a := hcount
    _ ≤ ((realInitialRows g.radius).card : ℝ) *
        (|fixedCutoffReferenceCompactMassCoefficient (g.upper / g.clearing + 1)| *
          (1 + gapFamilyCharge a) ^ 9 *
          exp (fixedFamilyPacketMassExponent g * sqrt (gapFamilyCharge a))) :=
      mul_le_mul_of_nonneg_left
        (fixedFamilyInitialMassBound_le_charge g a (by
          have ha := d.charge_large
          rw [shift_gapFamilyCharge] at ha
          linarith)) (by positivity)
    _ = _ := by unfold fixedFamilyPacketMassCoefficient; ring

end FixedFamilyDatum

end BTZEntropy.Construction
