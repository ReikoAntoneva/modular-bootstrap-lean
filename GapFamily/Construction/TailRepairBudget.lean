import GapFamily.Construction.TailExteriorAbsorption

/-! The short-cell exterior estimate, the ordinary residual TV bound, and the
literal moment schedule imply the actual rational allowance for every slot. -/

noncomputable section
namespace GapFamily.Construction

/-- The fixed exponential cost after the polynomial output-energy loss has
been absorbed into the thermal-independent vacuum envelope. -/
def tailRepairExponent (A C V : ℝ) (p : ℕ) : ℝ :=
  V + |A| + 4 * (C + p) + 2 * p

/-- An exterior numerator satisfying the actual C2 estimate pays its literal
slot budget. All cutoff, variation, and charge premises are numerical bounds;
the resulting estimate is uniform over unbounded output energies. -/
theorem tail_repair_error_le_slotBudget {A C D V B tv q e : ℝ} {a m K p : ℕ}
    (hA : 0 ≤ A) (hC : 0 ≤ C) (hB : 0 ≤ B)
    (hBupper : B ≤ 4 * ((a : ℝ) + m + 1))
    (htvbound : tv ≤ Real.exp (V * ((a : ℝ) + m + 1))) (he : 1 ≤ e)
    (hcharge : D + 2 * p ≤ 7 * Real.sqrt a)
    (hK : tailRepairExponent A C V p + 16 ≤ (K : ℝ) * Real.log 2)
    (hq : |q| ≤ A * tv * (1 + B + e)^p *
      Real.exp (C * B + D * Real.sqrt e - (tailMomentDegree K a m : ℝ) * Real.log 2)) :
    |q| ≤ Layer.slotBudget m * Real.exp (7 * Real.sqrt ((a : ℝ) * e)) := by
  let X : ℝ := (a : ℝ) + m + 1
  let d : ℝ := (tailMomentDegree K a m : ℝ) * Real.log 2
  have hX : 1 ≤ X := by
    dsimp [X]
    linarith [Nat.cast_nonneg (α := ℝ) a, Nat.cast_nonneg (α := ℝ) m]
  have hpoly := tail_exterior_polynomial_absorption (A := A) (C := C)
    (D := D) (a := (a : ℝ)) p hB he (Nat.cast_nonneg _) hcharge
  have hcost : V * X + (|A| + (C + p) * B + 2 * p) ≤
      tailRepairExponent A C V p * X := by
    have h1 := mul_le_mul_of_nonneg_left hBupper
      (by positivity : 0 ≤ C + (p : ℝ))
    have h2 := mul_le_mul_of_nonneg_left hX
      (by positivity : 0 ≤ |A| + 2 * (p : ℝ))
    dsimp [tailRepairExponent]
    change B ≤ 4 * X at hBupper
    change (C + (p : ℝ)) * B ≤ (C + (p : ℝ)) * (4 * X) at h1
    nlinarith
  calc
    |q| ≤ A * tv * (1 + B + e)^p *
        Real.exp (C * B + D * Real.sqrt e - d) := hq
    _ = tv * (A * (1 + B + e)^p * Real.exp (C * B + D * Real.sqrt e)) *
        Real.exp (-d) := by rw [sub_eq_add_neg, Real.exp_add]; ring
    _ ≤ Real.exp (V * X) *
        (Real.exp (|A| + (C + p) * B + 2 * p) *
          Real.exp (7 * Real.sqrt ((a : ℝ) * e))) * Real.exp (-d) := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
      exact mul_le_mul htvbound hpoly (by positivity) (Real.exp_nonneg _)
    _ = Real.exp (V * X + (|A| + (C + p) * B + 2 * p) - d) *
        Real.exp (7 * Real.sqrt ((a : ℝ) * e)) := by
      simp only [sub_eq_add_neg, Real.exp_add]
      ring
    _ ≤ Real.exp (tailRepairExponent A C V p * X - d) *
        Real.exp (7 * Real.sqrt ((a : ℝ) * e)) :=
      mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (sub_le_sub_right hcost d))
        (Real.exp_nonneg _)
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (tailMomentDegree_error_le_slotBudget hK a m) (Real.exp_nonneg _)

/-- The literal layer cutoff has the uniform bound used above whenever the
initial scale is at most the charge. -/
theorem tail_layer_cutoff_le_four_scale {U a m : ℕ} (hU : U ≤ a) :
    ((U + m + 4 : ℕ) : ℝ) ≤ 4 * ((a : ℝ) + m + 1) := by
  have hU' : (U : ℝ) ≤ a := by exact_mod_cast hU
  push_cast
  nlinarith [Nat.cast_nonneg (α := ℝ) a, Nat.cast_nonneg (α := ℝ) m]

end GapFamily.Construction
