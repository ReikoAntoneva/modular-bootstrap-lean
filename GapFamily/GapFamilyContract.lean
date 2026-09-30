import GapFamily.Contract
import Mathlib.Topology.Algebra.Order.Field

/-!
# Public statement of the two gap families

The two parts of Theorem 2.2 hold for every sufficiently large real shift
`a`, with central charge `c = 12 * a + 1`. The separate vacuum term and
full character expansion are specified by `Contract`.
-/

noncomputable section

namespace GapFamily

/-- Equal left and right central charge; the total central charge is twice this. -/
def gapFamilyCharge (a : ℝ) : ℝ := 12 * a + 1

/-- The shifted first energy, as opposed to cylinder energy. -/
def firstShiftedEnergy (c : ℝ) (s : Spectrum) : ℝ := firstDimension s - shift c

/-- An attained gap whose first level contains exactly one scalar occurrence.
Multiplicity is the same natural multiplicity used in the character expansion. -/
structure HasUnitScalarGap (s : Spectrum) (d : ℝ) : Prop where
  hasGap : HasGap s d
  scalar_mem : (d / 2, d / 2) ∈ s.support
  multiplicity_one : s.multiplicity (d / 2, d / 2) = 1
  eq_scalar : ∀ p ∈ s.support, dimension p = d → p = (d / 2, d / 2)

/-- An admissible spectrum at the prescribed real shift and shifted gap.
The constructed witness has the stronger property of a unit scalar first level. -/
def RealizesGap (a g : ℝ) (s : Spectrum) : Prop :=
  PureAdmissible (gapFamilyCharge a) s ∧ HasUnitScalarGap s (a + g)

/-- Part (i), for every sufficiently large real shift and every fixed ratio
in one positive interval. The family is total to state its limit; no
admissibility is imposed below the threshold `a₀`. -/
def ProportionalGapFamilyExists : Prop :=
  ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ < κ₀ →
    ∃ a₀ : ℝ, 1 ≤ a₀ ∧ ∃ family : ℝ → Spectrum,
      (∀ a, a₀ ≤ a → RealizesGap a (κ * a) (family a)) ∧
      Filter.Tendsto (fun a => firstDimension (family a) / gapFamilyCharge a)
        Filter.atTop (nhds ((1 + κ) / 12)) ∧ 1 / 12 < (1 + κ) / 12

/-- Part (ii), including the scalar threshold primary at `δ = 0`. -/
def FixedGapFamilyExists : Prop :=
  ∀ δ : ℝ, 0 ≤ δ → ∃ a₀ : ℝ, 1 ≤ a₀ ∧ ∃ family : ℝ → Spectrum,
    (∀ a, a₀ ≤ a → RealizesGap a δ (family a)) ∧
    Filter.Tendsto (fun a => firstShiftedEnergy (gapFamilyCharge a) (family a))
      Filter.atTop (nhds δ) ∧
    Filter.Tendsto
      (fun a => firstShiftedEnergy (gapFamilyCharge a) (family a) / a)
      Filter.atTop (nhds 0)

@[simp] theorem shift_gapFamilyCharge (a : ℝ) :
    shift (gapFamilyCharge a) = a := by
  unfold shift gapFamilyCharge
  ring

theorem gapFamilyCharge_gt_one {a : ℝ} (ha : 0 < a) : 1 < gapFamilyCharge a := by
  unfold gapFamilyCharge
  linarith

theorem RealizesGap.firstDimension_eq {a g : ℝ} {s : Spectrum}
    (h : RealizesGap a g s) : firstDimension s = a + g :=
  h.2.hasGap.firstDimension_eq

theorem RealizesGap.firstShiftedEnergy_eq {a g : ℝ} {s : Spectrum}
    (h : RealizesGap a g s) : firstShiftedEnergy (gapFamilyCharge a) s = g := by
  simp [firstShiftedEnergy, h.firstDimension_eq]

end GapFamily
