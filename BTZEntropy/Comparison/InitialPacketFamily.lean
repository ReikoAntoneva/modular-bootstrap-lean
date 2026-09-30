import BTZEntropy.Comparison.InitialPacketSubexponential
import BTZEntropy.Comparison.InitialPacketFamilyMass
import BTZEntropy.Construction.FixedFamilyActual

/-!
# Initial descendant packets of the admitted fixed family

The packet uses occurrences in the selected datum's literal initial node
list. An optional index adds its distinguished unit marker. In particular,
repeated initial nodes retain their actual multiplicity.
-/

noncomputable section

open Set Real
open scoped BigOperators

namespace BTZEntropy.Comparison

open GapFamily GapFamily.Construction BTZEntropy.Construction

variable {B : ℝ} {g : FixedFamilyGeometry B} {a : ℝ} {δ : ℝ}

/-- The shifted energy of an actual initial-node occurrence. -/
def fixedFamilyInitialEnergy (d : FixedFamilyDatum g a δ)
    (i : Fin d.initialState.nodes.length) : ℝ :=
  (d.initialState.nodes.get i).1

/-- Add the distinguished unit marker to the actual initial node occurrences. -/
def fixedFamilyMarkedInitialEnergy (d : FixedFamilyDatum g a δ) :
    Option (Fin d.initialState.nodes.length) → ℝ
  | none => δ
  | some i => fixedFamilyInitialEnergy d i

/-- The complete descendant count of the datum's actual initial nodes. -/
def fixedFamilyInitialSmoothCount (φ : SmoothKernel) (d : FixedFamilyDatum g a δ)
    (E : ℝ) : ℝ :=
  initialPacketSmoothCount φ (fixedFamilyInitialEnergy d) (fun _ => 1) E

/-- The actual finite initial packet, including its distinguished marker and
all left/right descendants. -/
def fixedFamilyMarkedInitialSmoothCount (φ : SmoothKernel)
    (d : FixedFamilyDatum g a δ) (E : ℝ) : ℝ :=
  initialPacketSmoothCount φ (fixedFamilyMarkedInitialEnergy d) (fun _ => 1) E

theorem fixedFamilyInitialEnergy_nonneg (d : FixedFamilyDatum g a δ)
    (i : Fin d.initialState.nodes.length) : 0 ≤ fixedFamilyInitialEnergy d i :=
  d.marker_nonneg.trans (d.initial_nodes_bounds _ (List.get_mem _ _)).1

theorem fixedFamilyMarkedInitialEnergy_nonneg (d : FixedFamilyDatum g a δ)
    (i : Option (Fin d.initialState.nodes.length)) :
    0 ≤ fixedFamilyMarkedInitialEnergy d i := by
  cases i with
  | none => exact d.marker_nonneg
  | some i => exact fixedFamilyInitialEnergy_nonneg d i

/-- The marker is exactly one extra module; no selector-dependent factor
is introduced in passing to the marked packet. -/
theorem fixedFamilyMarkedInitialSmoothCount_eq (φ : SmoothKernel)
    (d : FixedFamilyDatum g a δ) (E : ℝ) :
    fixedFamilyMarkedInitialSmoothCount φ d E =
      moduleSmoothCount φ (fun n => (partitionCount n : ℝ)) (δ - 1 / 12) E +
        fixedFamilyInitialSmoothCount φ d E := by
  simp [fixedFamilyMarkedInitialSmoothCount, fixedFamilyInitialSmoothCount,
    initialPacketSmoothCount, Fintype.sum_option, fixedFamilyMarkedInitialEnergy]

/-- The marked list in this estimate is precisely the initial permanent
atom list of the same admitted construction. -/
theorem fixedFamily_initial_permanentAtomList (d : FixedFamilyDatum g a δ) :
    d.permanentData.permanentAtomList g.start = (δ, 0) :: d.initialState.nodes := by
  simpa [FixedFamilyDatum.state] using d.permanentAtomList_eq 0

private theorem charge_one_le (d : FixedFamilyDatum g a δ) :
    1 ≤ gapFamilyCharge a := by
  have h := d.charge_large
  unfold shift at h
  linarith

/-- The admitted initial nodes and all descendants obey a charge bound whose
constants depend only on the fixed geometry and kernel bounds. -/
theorem fixedFamilyInitialSmoothCount_le_sqrt (φ : SmoothKernel)
    (d : FixedFamilyDatum g a δ) (hbound : d.HasBounds (fixedFamilyBounds g))
    {x U R H : ℝ} (hx : x ≤ U) (hR0 : 0 ≤ R) (hH : 0 ≤ H)
    (hR : ∀ u, φ u ≠ 0 → u ≤ R) (hφ : ∀ u, φ u ≤ H) :
    fixedFamilyInitialSmoothCount φ d (x * gapFamilyCharge a) ≤
      fixedFamilyPacketMassCoefficient g * H *
        exp ((18 + fixedFamilyPacketMassExponent g + U + R + 1 / 12 + 4) *
          sqrt (gapFamilyCharge a)) := by
  have hm : (∑ _i : Fin d.initialState.nodes.length, (1 : ℝ)) ≤
      fixedFamilyPacketMassCoefficient g * (1 + gapFamilyCharge a) ^ 9 *
        exp (fixedFamilyPacketMassExponent g * sqrt (gapFamilyCharge a)) := by
    simpa using d.initial_nodes_length_le_charge hbound
  convert initialPacketSmoothCount_le_sqrt_of_mass φ (fixedFamilyInitialEnergy d)
    (fun _ => 1) (A := fixedFamilyPacketMassCoefficient g)
    (D := fixedFamilyPacketMassExponent g) 9 (charge_one_le d) hx hR0 hH
    (fixedFamilyPacketMassCoefficient_nonneg g) hR hφ
    (fixedFamilyInitialEnergy_nonneg d) (by simpa using hm) using 1 <;>
      norm_num [fixedFamilyInitialSmoothCount]

/-- The actual initial multiplicity increases by exactly one when the
distinguished marker is included. -/
theorem fixedFamilyMarkedInitial_mass_le (d : FixedFamilyDatum g a δ)
    (hbound : d.HasBounds (fixedFamilyBounds g)) :
    (∑ _i : Option (Fin d.initialState.nodes.length), (1 : ℝ)) ≤
      (fixedFamilyPacketMassCoefficient g + 1) * (1 + gapFamilyCharge a) ^ 9 *
        exp (fixedFamilyPacketMassExponent g * sqrt (gapFamilyCharge a)) := by
  have hc := charge_one_le d
  have hp : 1 ≤ (1 + gapFamilyCharge a) ^ 9 := one_le_pow₀ (by linarith)
  have he : 1 ≤ exp (fixedFamilyPacketMassExponent g * sqrt (gapFamilyCharge a)) :=
    one_le_exp (mul_nonneg (fixedFamilyPacketMassExponent_nonneg g) (sqrt_nonneg _))
  have hprod : 1 ≤ (1 + gapFamilyCharge a) ^ 9 *
      exp (fixedFamilyPacketMassExponent g * sqrt (gapFamilyCharge a)) :=
    one_le_mul_of_one_le_of_one_le hp he
  have hm := d.initial_nodes_length_le_charge hbound
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_option, Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_add, Nat.cast_one, mul_one]
  nlinarith

/-- Including the unit marker preserves the common root-exponential bound,
uniformly in its position throughout the fixed interval. -/
theorem fixedFamilyMarkedInitialSmoothCount_le_sqrt (φ : SmoothKernel)
    (d : FixedFamilyDatum g a δ) (hbound : d.HasBounds (fixedFamilyBounds g))
    {x U R H : ℝ} (hx : x ≤ U) (hR0 : 0 ≤ R) (hH : 0 ≤ H)
    (hR : ∀ u, φ u ≠ 0 → u ≤ R) (hφ : ∀ u, φ u ≤ H) :
    fixedFamilyMarkedInitialSmoothCount φ d (x * gapFamilyCharge a) ≤
      (fixedFamilyPacketMassCoefficient g + 1) * H *
        exp ((18 + fixedFamilyPacketMassExponent g + U + R + 1 / 12 + 4) *
          sqrt (gapFamilyCharge a)) := by
  convert initialPacketSmoothCount_le_sqrt_of_mass φ (fixedFamilyMarkedInitialEnergy d)
    (fun _ => 1) (A := fixedFamilyPacketMassCoefficient g + 1)
    (D := fixedFamilyPacketMassExponent g) 9 (charge_one_le d) hx hR0 hH
    (by have := fixedFamilyPacketMassCoefficient_nonneg g; positivity) hR hφ
    (fixedFamilyMarkedInitialEnergy_nonneg d)
    (by simpa using fixedFamilyMarkedInitial_mass_le d hbound) using 1 <;>
      norm_num [fixedFamilyMarkedInitialSmoothCount]

/-- The same constants work for every admitted selector, every sufficiently
large charge, and every marker in the whole requested fixed interval. -/
theorem fixedFamily_selected_markedInitialSmoothCount_le_sqrt (φ : SmoothKernel)
    {σ : ActualFixedFamilySelector B} (hσ : σ ∈ fixedFamilySelectors B)
    (ha : fixedFamilyThreshold B ≤ a) (hδ : δ ∈ Ico (0 : ℝ) B)
    {x U R H : ℝ} (hx : x ≤ U) (hR0 : 0 ≤ R) (hH : 0 ≤ H)
    (hR : ∀ u, φ u ≠ 0 → u ≤ R) (hφ : ∀ u, φ u ≤ H) :
    fixedFamilyMarkedInitialSmoothCount φ (σ a ha δ hδ) (x * gapFamilyCharge a) ≤
      (fixedFamilyPacketMassCoefficient (fixedFamilyGeometry B) + 1) * H *
        exp ((18 + fixedFamilyPacketMassExponent (fixedFamilyGeometry B) +
          U + R + 1 / 12 + 4) * sqrt (gapFamilyCharge a)) :=
  fixedFamilyMarkedInitialSmoothCount_le_sqrt φ (σ a ha δ hδ)
    (fixedFamily_selected_hasBounds hσ ha hδ) hx hR0 hH hR hφ

/-- Kernel compactness discharges the support and supremum bounds once and
for all. These positive constants work simultaneously for the complete
admitted selector class and the entire marker interval. -/
theorem fixedFamily_markedInitial_uniform_sqrt_bound (B : ℝ) (φ : SmoothKernel)
    (U : ℝ) :
    ∃ A D : ℝ, 0 < A ∧ 0 < D ∧
      ∀ (σ : ActualFixedFamilySelector B), σ ∈ fixedFamilySelectors B →
      ∀ (a : ℝ) (ha : fixedFamilyThreshold B ≤ a)
        (δ : ℝ) (hδ : δ ∈ Ico (0 : ℝ) B) (x : ℝ), x ≤ U →
        fixedFamilyMarkedInitialSmoothCount φ (σ a ha δ hδ)
          (x * gapFamilyCharge a) ≤ A * exp (D * sqrt (gapFamilyCharge a)) := by
  obtain ⟨R, H, hR0, hH, hR, hφ⟩ := exists_kernel_upper_bound φ
  let A₀ := (fixedFamilyPacketMassCoefficient (fixedFamilyGeometry B) + 1) * H
  let D₀ := 18 + fixedFamilyPacketMassExponent (fixedFamilyGeometry B) +
    U + R + 1 / 12 + 4
  have hA₀ : 0 ≤ A₀ := by
    dsimp [A₀]
    have hAg := fixedFamilyPacketMassCoefficient_nonneg (fixedFamilyGeometry B)
    exact mul_nonneg (by linarith) hH
  refine ⟨A₀ + 1, max 0 D₀ + 1, by positivity, by positivity, ?_⟩
  intro σ hσ a ha δ hδ x hx
  calc
    _ ≤ A₀ * exp (D₀ * sqrt (gapFamilyCharge a)) :=
      fixedFamily_selected_markedInitialSmoothCount_le_sqrt φ hσ ha hδ
        hx hR0 hH hR hφ
    _ ≤ (A₀ + 1) * exp ((max 0 D₀ + 1) * sqrt (gapFamilyCharge a)) := by
      apply mul_le_mul (by linarith) _ (exp_pos _).le (by positivity)
      apply exp_le_exp.mpr
      apply mul_le_mul_of_nonneg_right _ (sqrt_nonneg _)
      have := le_max_right 0 D₀
      linarith

/-- The literal finite initial packet, its unit marker, and the vacuum,
including all descendants, have a common subexponential bound. Every
constant is fixed before choosing a selector, charge, marker, or energy
ratio in the prescribed upper range. -/
theorem fixedFamily_initial_vacuum_uniform_sqrt_bound (B : ℝ) (φ : SmoothKernel)
    (U : ℝ) :
    ∃ A D : ℝ, 0 ≤ A ∧ 0 ≤ D ∧
      ∀ (σ : ActualFixedFamilySelector B), σ ∈ fixedFamilySelectors B →
      ∀ (a : ℝ) (ha : fixedFamilyThreshold B ≤ a)
        (δ : ℝ) (hδ : δ ∈ Ico (0 : ℝ) B) (x : ℝ), x ≤ U →
        fixedFamilyMarkedInitialSmoothCount φ (σ a ha δ hδ)
            (x * gapFamilyCharge a) +
          vacuumSmoothCount φ (gapFamilyCharge a) (x * gapFamilyCharge a) ≤
            A * exp (D * sqrt (gapFamilyCharge a)) := by
  obtain ⟨R, H, hR0, hH, hR, hφ⟩ := exists_kernel_upper_bound φ
  let A₀ := fixedFamilyPacketMassCoefficient (fixedFamilyGeometry B)
  let D₀ := 18 + fixedFamilyPacketMassExponent (fixedFamilyGeometry B) +
    max 0 U + R + 1 / 12 + 4
  have hA₀ : 0 ≤ A₀ := fixedFamilyPacketMassCoefficient_nonneg _
  have hD₀ : 0 ≤ D₀ := by
    have := fixedFamilyPacketMassExponent_nonneg (fixedFamilyGeometry B)
    dsimp [D₀]
    positivity
  refine ⟨(A₀ + 2) * H, D₀, by positivity, hD₀, ?_⟩
  intro σ hσ a ha δ hδ x hx
  have hx' : x ≤ max 0 U := hx.trans (le_max_right _ _)
  have hm := fixedFamily_selected_markedInitialSmoothCount_le_sqrt φ hσ ha hδ
    hx' hR0 hH hR hφ
  have hv := vacuumSmoothCount_le_sqrt φ (charge_one_le (σ a ha δ hδ))
    hx' hR0 hH hR hφ
  have hv' : vacuumSmoothCount φ (gapFamilyCharge a) (x * gapFamilyCharge a) ≤
      H * exp (D₀ * sqrt (gapFamilyCharge a)) := by
    apply hv.trans
    apply mul_le_mul_of_nonneg_left _ hH
    apply exp_le_exp.mpr
    apply mul_le_mul_of_nonneg_right _ (sqrt_nonneg _)
    dsimp [D₀]
    have := fixedFamilyPacketMassExponent_nonneg (fixedFamilyGeometry B)
    linarith
  calc
    _ ≤ (A₀ + 1) * H * exp (D₀ * sqrt (gapFamilyCharge a)) +
        H * exp (D₀ * sqrt (gapFamilyCharge a)) := add_le_add hm hv'
    _ = (A₀ + 2) * H * exp (D₀ * sqrt (gapFamilyCharge a)) := by ring

end BTZEntropy.Comparison
