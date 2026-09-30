import GapFamily.Construction.InitialReferenceCellResidual
import GapFamily.Construction.InitialParameter
import GapFamily.Construction.MarkerReferenceDensityMass

/-!
# Absolute mass and variation of the canonical initial reference cell

The selected cell lies in the compact band `(R+1)b`. Its actual signed
continuum mass bound therefore controls both the node count and residual
variation. At the natural construction parameters the remaining exponent
is at most a fixed constant times the initial degree.
-/

noncomputable section

open Set MeasureTheory Real
open GapFamily.Analytic

namespace GapFamily.Construction

/-- The absolute canonical continuum mass on the selected initial cell is
bounded by the proved compact-band mass coefficient. -/
theorem InitialReferenceCell.abs_mass_le_canonical
    {a b U : ℝ} {j : ℤ} {k : ℕ} {ha : 2 ≤ a} {hb : 1 ≤ b}
    (cell : InitialReferenceCell j (max b |(j : ℝ)|) U k
      (canonicalMarkerReferenceDensity a b ha hb j))
    (R : ℝ) (hR : 1 ≤ R) (hba : b ≤ a) (hU : U = R * b) :
    (∫ E in Ioo (max b |(j : ℝ)|) cell.right,
      |canonicalMarkerReferenceDensity a b ha hb j E| ∂referenceMeasure j) ≤
      markerReferenceCompactMassCoefficient (R + 1) * (1 + a) ^ 9 *
        exp (markerReferenceCompactMassExponent (R + 1) * sqrt (a * b)) := by
  have hright : cell.right ≤ (R + 1) * b := by
    have hr := cell.right_mem.2
    nlinarith
  have hq := canonicalMarkerReferenceDensity_integrable a b ((R + 1) * b) ha hb j
  calc
    _ ≤ ∫ E in Ioo |(j : ℝ)| ((R + 1) * b),
        |canonicalMarkerReferenceDensity a b ha hb j E| ∂referenceMeasure j := by
      apply setIntegral_mono_set hq.abs (Filter.Eventually.of_forall fun _ => abs_nonneg _)
      exact Filter.Eventually.of_forall fun E hE =>
        ⟨(le_max_right b |(j : ℝ)|).trans_lt hE.1, hE.2.trans_le hright⟩
    _ ≤ _ := integral_abs_canonicalMarkerReferenceDensity_le
      (R + 1) a b (by linarith) ha hb hba j

/-- The actual unit-node count has the canonical compact mass budget. -/
theorem InitialReferenceCell.count_le_canonical
    {a b U : ℝ} {j : ℤ} {k : ℕ} {ha : 2 ≤ a} {hb : 1 ≤ b}
    (cell : InitialReferenceCell j (max b |(j : ℝ)|) U k
      (canonicalMarkerReferenceDensity a b ha hb j))
    (R : ℝ) (hR : 1 ≤ R) (hba : b ≤ a) (hU : U = R * b) :
    (cell.count : ℝ) ≤
      markerReferenceCompactMassCoefficient (R + 1) * (1 + a) ^ 9 *
        exp (markerReferenceCompactMassExponent (R + 1) * sqrt (a * b)) :=
  cell.count_le_abs_mass.trans (cell.abs_mass_le_canonical R hR hba hU)

/-- The actual signed residual is bounded by twice the canonical compact
absolute-mass budget. -/
theorem InitialReferenceCell.variation_le_canonical
    {a b U : ℝ} {j : ℤ} {k : ℕ} {ha : 2 ≤ a} {hb : 1 ≤ b}
    (cell : InitialReferenceCell j (max b |(j : ℝ)|) U k
      (canonicalMarkerReferenceDensity a b ha hb j))
    (R : ℝ) (hR : 1 ≤ R) (hba : b ≤ a) (hU : U = R * b) :
    cell.residual.variation.real univ ≤
      2 * markerReferenceCompactMassCoefficient (R + 1) * (1 + a) ^ 9 *
        exp (markerReferenceCompactMassExponent (R + 1) * sqrt (a * b)) := by
  have hm := cell.abs_mass_le_canonical R hR hba hU
  have hv := cell.variation_le_twice_abs_mass
  nlinarith

/-- At the construction's natural parameters the canonical residual
exponent is linear in the actual integer initial degree. -/
theorem InitialReferenceCell.variation_le_canonical_parameter
    (R s n : ℕ) (hR : 1 ≤ R) (hs : 1 ≤ s)
    (ha : 2 ≤ ((R * s ^ 2 * n : ℕ) : ℝ)) (hb : 1 ≤ (n : ℝ))
    (j : ℤ)
    (cell : InitialReferenceCell j (max (n : ℝ) |(j : ℝ)|) ((R * n : ℕ) : ℝ)
      (R * s * n) (canonicalMarkerReferenceDensity ((R * s ^ 2 * n : ℕ) : ℝ)
        (n : ℝ) ha hb j)) :
    cell.residual.variation.real univ ≤
      2 * markerReferenceCompactMassCoefficient ((R : ℝ) + 1) *
        (1 + ((R * s ^ 2 * n : ℕ) : ℝ)) ^ 9 *
        exp (markerReferenceCompactMassExponent ((R : ℝ) + 1) * ((R * s * n : ℕ) : ℝ)) := by
  have hRr : (1 : ℝ) ≤ R := by exact_mod_cast hR
  have hna : n ≤ R * s ^ 2 * n :=
    (Nat.le_mul_of_pos_left n hR).trans (initialParameter_U_le_a R n hs)
  have hba : (n : ℝ) ≤ ((R * s ^ 2 * n : ℕ) : ℝ) := by exact_mod_cast hna
  have hsqrt : sqrt (((R * s ^ 2 * n : ℕ) : ℝ) * (n : ℝ)) ≤
      ((R * s * n : ℕ) : ℝ) := by
    simpa only [one_mul] using initialParameter_negative_exponent_le R s n
      (one_le_sqrt.mpr hRr)
  have hcoeff := markerReferenceCompactMassCoefficient_pos ((R : ℝ) + 1) (by positivity)
  have hexp := markerReferenceCompactMassExponent_pos ((R : ℝ) + 1)
  refine (cell.variation_le_canonical (R : ℝ) hRr hba (by push_cast; rfl)).trans ?_
  gcongr

end GapFamily.Construction
