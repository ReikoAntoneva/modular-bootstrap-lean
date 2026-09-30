import BTZEntropy.Construction.FixedFamilyBound
import BTZEntropy.Construction.FixedBandInitialMass
import BTZEntropy.Construction.FixedBandDegree
import GapFamily.Construction.RealTailMomentSchedule
import GapFamily.Construction.CanonicalTailParameterConstant
import GapFamily.Construction.FixedCutoffReferenceOutput

/-!
# Common bounds for the fixed reference model

The reference density and modular output are the actual fixed-cutoff
construction. The quantitative bounds are fixed functions of the common
geometry and charge, independent of the marker and selected nodes.
-/

noncomputable section

open Set MeasureTheory Real

namespace BTZEntropy.Construction

open GapFamily GapFamily.Construction GapFamily.Analytic

/-- The uniform mass bound for each initial spin row. -/
def fixedFamilyInitialMassBound {B : ℝ} (g : FixedFamilyGeometry B) (a : ℝ) : ℝ :=
  fixedCutoffReferenceCompactMassCoefficient (g.upper / g.clearing + 1) *
    (1 + shift (gapFamilyCharge a)) ^ 9 *
    exp (fixedCutoffReferenceCompactMassExponent 2 *
      sqrt (shift (gapFamilyCharge a) * g.upper))

/-- Explicit common count, variation and degree bounds for the fixed model. -/
def fixedFamilyBounds {B : ℝ} (g : FixedFamilyGeometry B) : FixedFamilyBounds where
  initialCount a _ := fixedFamilyInitialMassBound g a
  initialVariation a _ := 2 * fixedFamilyInitialMassBound g a
  tailCount a _ _ L := 6 * exp (4 * π * (shift (gapFamilyCharge a) + L))
  tailVariation a _ _ L := 12 * exp (4 * π * (shift (gapFamilyCharge a) + L))
  initialDegree a := fixedBandDegree (shift (gapFamilyCharge a)) g.upper
  tailDegree a := realTailMomentDegree canonicalTailMomentMultiplier (shift (gapFamilyCharge a))

namespace FixedFamilyDatum

variable {B : ℝ} {g : FixedFamilyGeometry B} {a : ℝ} {δ : ℝ}
  (d : FixedFamilyDatum g a δ)

/-- The datum uses the prescribed fixed-cutoff reference and degree
schedules, while its actual moment-matched nodes remain free to vary. -/
structure UsesFixedReference (hb : 1 ≤ g.clearing) : Prop where
  initial_degree : d.initialDegree = fixedBandDegree (shift (gapFamilyCharge a)) g.upper
  tail_degree : d.tailDegree =
    realTailMomentDegree canonicalTailMomentMultiplier (shift (gapFamilyCharge a))
  density_eq : d.density = fixedCutoffReferenceDensity (shift (gapFamilyCharge a))
    g.clearing δ ((by norm_num : (2 : ℝ) ≤ 100).trans d.charge_large) hb
  reference_eq : d.reference = ReferenceOutput.fixedCutoff (shift (gapFamilyCharge a))
    g.clearing δ ((by norm_num : (2 : ℝ) ≤ 100).trans d.charge_large) hb
    d.marker_nonneg d.marker_le_clearing

private theorem initial_bounds_of_density_eq
    {a b δ U : ℝ} {j : ℤ} {k : ℕ} {q : ℝ → ℝ}
    {ha : 2 ≤ a} {hb : 1 ≤ b}
    (cell : InitialReferenceCell j (max b |(j : ℝ)|) U k q)
    (hq : q = fixedCutoffReferenceDensity a b δ ha hb j)
    (hδ : 0 ≤ δ) (hδb : δ ≤ b)
    (Q : ℝ) (hQ : 1 ≤ Q) (hba : b ≤ a) (hQU : U = Q * b) :
    (cell.count : ℝ) ≤ fixedCutoffReferenceCompactMassCoefficient (Q + 1) *
        (1 + a) ^ 9 * exp (fixedCutoffReferenceCompactMassExponent 2 * sqrt (a * U)) ∧
      cell.residual.variation.real univ ≤
        2 * (fixedCutoffReferenceCompactMassCoefficient (Q + 1) *
          (1 + a) ^ 9 * exp (fixedCutoffReferenceCompactMassExponent 2 * sqrt (a * U))) := by
  subst q
  exact ⟨fixedBand_initial_count_le cell hδ hδb Q hQ hba hQU,
    cell.variation_le_twice_abs_mass.trans
      (mul_le_mul_of_nonneg_left
        (fixedBand_initial_abs_mass_le cell hδ hδb Q hQ hba hQU) (by norm_num))⟩

/-- The explicit fixed reference has the common bounds for every choice
of its actual cells. The only charge condition beyond the datum is that
the fixed clearing cutoff lies below the charge. -/
theorem hasBounds_of_usesFixedReference (hb : 1 ≤ g.clearing)
    (huses : d.UsesFixedReference hb) (hQ : 1 ≤ g.upper / g.clearing)
    (hba : g.clearing ≤ shift (gapFamilyCharge a)) :
    d.HasBounds (fixedFamilyBounds g) := by
  have hQU : g.upper = g.upper / g.clearing * g.clearing := by
    rw [div_mul_cancel₀ _ (by linarith : g.clearing ≠ 0)]
  have hcell (J : realInitialRows g.radius) :=
    initial_bounds_of_density_eq (d.initialCell J) (congrFun huses.density_eq J)
      d.marker_nonneg d.marker_le_clearing (g.upper / g.clearing) hQ hba hQU
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro J
    exact (hcell J).1
  · intro J
    exact (hcell J).2
  · exact huses.initial_degree.ge
  · intro state m J h
    exact d.tailCell_count_le state m J h
  · intro state m J h
    exact d.tailCell_variation_le state m J h
  · intro m
    exact (congrFun huses.tail_degree m).ge

end FixedFamilyDatum

end BTZEntropy.Construction
