import GapFamily.Construction.LayerBudgetTail

/-! Absolute summability of the complete correction increments. The direct
residual and exterior output are estimated separately, but only their sum is
used as the correction. The exact two-slot layer budget is retained. -/

noncomputable section
namespace GapFamily.Construction
open Filter
open scoped Topology

theorem summable_slotBudget :
    Summable (fun p : Σ m : ℕ, Layer.Slot m => Layer.slotBudget p.1) := by
  apply (summable_sigma_of_nonneg (fun p => by
    dsimp [Layer.slotBudget]
    positivity)).mpr
  refine ⟨fun _ => Summable.of_finite, ?_⟩
  simpa only [tsum_fintype, Layer.sum_slotBudget] using Layer.summable_layerBudget

section Normed
variable {A : Type*} [NormedAddCommGroup A]

/-- Every actual slot output is included, including the two slots in each
physical spin row. A summable common thermal majorant controls the full family. -/
theorem summable_norm_slotExterior (exterior : (Σ m : ℕ, Layer.Slot m) → A)
    (C : ℝ) (hbound : ∀ p, ‖exterior p‖ ≤ Layer.slotBudget p.1 * C) :
    Summable (fun p => ‖exterior p‖) :=
  (summable_slotBudget.mul_right C).of_nonneg_of_le (fun _ => norm_nonneg _) hbound

theorem norm_layerExterior_le (exterior : (Σ m : ℕ, Layer.Slot m) → A)
    (C : ℝ) (hbound : ∀ p, ‖exterior p‖ ≤ Layer.slotBudget p.1 * C) (m : ℕ) :
    ‖∑ s : Layer.Slot m, exterior ⟨m, s⟩‖ ≤ Layer.layerBudget m * C := by
  calc
    _ ≤ ∑ s : Layer.Slot m, ‖exterior ⟨m, s⟩‖ := norm_sum_le _ _
    _ ≤ ∑ _ : Layer.Slot m, Layer.slotBudget m * C :=
      Finset.sum_le_sum fun s _ => hbound ⟨m, s⟩
    _ = _ := by rw [← Finset.sum_mul, Layer.sum_slotBudget]

/-- Summing direct and exterior pieces preserves absolute convergence of the
complete modular correction, without requiring either piece to be modular. -/
theorem summable_norm_completeCorrection {ι : Type*}
    (complete direct exterior : ι → A)
    (hcomplete : ∀ i, complete i = direct i + exterior i)
    (hdirect : Summable (fun i => ‖direct i‖))
    (hexterior : Summable (fun i => ‖exterior i‖)) :
    Summable (fun i => ‖complete i‖) := by
  apply (hdirect.add hexterior).of_nonneg_of_le (fun _ => norm_nonneg _)
  intro i
  rw [hcomplete]
  exact norm_add_le _ _

/-- The complete correction series has an explicit residual thermal tail plus
the remaining rational exterior allowance. -/
theorem norm_completeCorrection_tail_le
    (complete direct exterior : ℕ → A) (thermal : ℕ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hcomplete : ∀ m, complete m = direct m + exterior m)
    (hthermal : Summable thermal)
    (hdirect : ∀ m, ‖direct m‖ ≤ thermal m)
    (hexterior : ∀ m, ‖exterior m‖ ≤ Layer.layerBudget m * C) (n : ℕ) :
    ‖∑' k : ℕ, complete (n + k)‖ ≤
      (∑' k : ℕ, thermal (n + k)) + ((1 / 256 : ℝ) / ((n : ℝ) + 1)) * C := by
  have hd : Summable (fun m => ‖direct m‖) :=
    hthermal.of_nonneg_of_le (fun _ => norm_nonneg _) hdirect
  have he : Summable (fun m => ‖exterior m‖) :=
    (Layer.summable_layerBudget.mul_right C).of_nonneg_of_le
      (fun _ => norm_nonneg _) hexterior
  have hs := summable_norm_completeCorrection complete direct exterior hcomplete hd he
  have hsn : Summable (fun k => ‖complete (n + k)‖) := by
    simpa only [Nat.add_comm] using (summable_nat_add_iff n).mpr hs
  have htn : Summable (fun k => thermal (n + k)) := by
    simpa only [Nat.add_comm] using (summable_nat_add_iff n).mpr hthermal
  have hen := (summable_layerBudget_add n).mul_right C
  calc
    _ ≤ ∑' k : ℕ, ‖complete (n + k)‖ := norm_tsum_le_tsum_norm hsn
    _ ≤ ∑' k : ℕ, (thermal (n + k) + Layer.layerBudget (n + k) * C) := by
      apply hsn.tsum_le_tsum _ (htn.add hen)
      intro k
      rw [hcomplete]
      exact (norm_add_le _ _).trans (add_le_add (hdirect _) (hexterior _))
    _ = (∑' k : ℕ, thermal (n + k)) + (∑' k : ℕ, Layer.layerBudget (n + k)) * C := by
      rw [htn.tsum_add hen, tsum_mul_right]
    _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_right (tsum_layerBudget_add_le n) hC)

variable [CompleteSpace A]

/-- The complete series converges, with the omitted complete outputs tending
to zero as an ordinary absolutely convergent series. -/
theorem tendsto_completeCorrection_tail_zero
    (complete direct exterior : ℕ → A) (thermal : ℕ → ℝ) (C : ℝ)
    (hcomplete : ∀ m, complete m = direct m + exterior m)
    (hthermal : Summable thermal)
    (hdirect : ∀ m, ‖direct m‖ ≤ thermal m)
    (hexterior : ∀ m, ‖exterior m‖ ≤ Layer.layerBudget m * C) :
    Tendsto (fun n => ∑' k : ℕ, complete (n + k)) atTop (𝓝 0) := by
  have hd := hthermal.of_nonneg_of_le (fun _ => norm_nonneg _) hdirect
  have he := (Layer.summable_layerBudget.mul_right C).of_nonneg_of_le
    (fun _ => norm_nonneg _) hexterior
  have hs := (summable_norm_completeCorrection complete direct exterior hcomplete hd he).of_norm
  have heq (n : ℕ) : (∑' k : ℕ, complete (n + k)) =
      (∑' m : ℕ, complete m) - ∑ m ∈ Finset.range n, complete m := by
    have h := hs.sum_add_tsum_nat_add n
    simp only [Nat.add_comm] at h
    exact eq_sub_iff_add_eq.mpr (by simpa only [add_comm] using h)
  simp_rw [heq]
  simpa only [sub_self] using
    (tendsto_const_nhds (x := ∑' m : ℕ, complete m)).sub hs.hasSum.tendsto_sum_nat

end Normed
end GapFamily.Construction
