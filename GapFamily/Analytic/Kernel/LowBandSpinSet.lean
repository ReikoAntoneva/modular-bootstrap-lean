import GapFamily.Analytic.Kernel.HigherKernelSmoothingNorm

/-! The canonical finite family of integer rows meeting an open low band. -/

noncomputable section

namespace GapFamily.Analytic

def lowBandSpinSet (B : ℝ) : Finset ℤ :=
  (Finset.Icc (-⌈|B|⌉) ⌈|B|⌉).filter (fun j => |(j : ℝ)| < B)

@[simp] theorem mem_lowBandSpinSet (B : ℝ) (j : ℤ) :
    j ∈ lowBandSpinSet B ↔ |(j : ℝ)| < B := by
  simp only [lowBandSpinSet, Finset.mem_filter, Finset.mem_Icc]
  refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
  have hceil : |(j : ℝ)| ≤ (⌈|B|⌉ : ℝ) :=
    h.le.trans ((le_abs_self B).trans (Int.le_ceil |B|))
  obtain ⟨hlo, hhi⟩ := abs_le.mp hceil
  exact ⟨by exact_mod_cast hlo, by exact_mod_cast hhi⟩

theorem lowBandSpinSet_mono {b B : ℝ} (h : b ≤ B) :
    lowBandSpinSet b ⊆ lowBandSpinSet B := by
  intro j hj
  exact (mem_lowBandSpinSet B j).mpr (((mem_lowBandSpinSet b j).mp hj).trans_le h)

@[simp] theorem zero_mem_lowBandSpinSet (B : ℝ) : 0 ∈ lowBandSpinSet B ↔ 0 < B := by
  simp

abbrev LowBandSpin (B : ℝ) := ↥(lowBandSpinSet B)

theorem lowBandSpin_injective (B : ℝ) :
    Function.Injective (fun i : LowBandSpin B => (i : ℤ)) := Subtype.val_injective

theorem lowBandSpin_physical (B : ℝ) (i : LowBandSpin B) : |((i : ℤ) : ℝ)| < B :=
  (mem_lowBandSpinSet B i).mp i.property

theorem lowBandSpinSet_card_le (B : ℝ) (hB : 1 ≤ B) :
    ((lowBandSpinSet B).card : ℝ) ≤ 5 * B := by
  simpa only [Fintype.card_coe] using physicalLowBand_card_le
    (fun i : LowBandSpin B => (i : ℤ)) (lowBandSpin_injective B) hB (lowBandSpin_physical B)

end GapFamily.Analytic
