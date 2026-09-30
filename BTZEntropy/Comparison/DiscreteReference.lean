import BTZEntropy.Comparison.DiscreteReferenceDifference
import BTZEntropy.Comparison.DiscreteReferenceQuadrature
import BTZEntropy.Comparison.DiscreteReferencePacket
import BTZEntropy.Comparison.DiscreteReferenceNormalize

/-!
# The actual discrete spectrum and its integer-spin reference

The same admitted cells and permanent spectrum satisfy an all-orders
comparison, uniformly over every admitted selector and marker. Both
descendant towers, the vacuum, and the finite initial band are included.
-/

noncomputable section

set_option maxHeartbeats 600000

open Set Filter MeasureTheory Real
open GapFamily GapFamily.Analytic GapFamily.Construction
open BTZEntropy.Construction
open scoped BigOperators Classical

namespace BTZEntropy.Comparison

/-- The exact decomposition bounds the total discrepancy by four genuine
contributions of the same datum. Its auxiliary finite cutoffs can be chosen
after the observation energy, because all ensuing estimates are uniform in
those cutoffs. -/
theorem fixedFamily_discreteReference_abs_le
    {B : ℝ} {g : FixedFamilyGeometry B} {a : ℝ} {δ : ℝ}
    (d : BTZEntropy.Construction.FixedFamilyDatum g a δ) (φ : SmoothKernel)
    (E R : ℝ) (N k : ℕ)
    (hR : ∀ u, φ u ≠ 0 → u ≤ R)
    (hNv : E + R + gapFamilyCharge a / 12 < (N : ℝ))
    (hNp : E + R + 1 / 12 < (N : ℝ))
    (hk : E + R + 1 / 12 < ((g.start + k : ℕ) : ℝ)) :
    |smoothCount φ (gapFamilyCharge a) d.spectrum E -
      integerLeadingSmoothCount φ (shift (gapFamilyCharge a)) g.start E| ≤
      fixedFamilyMarkedInitialSmoothCount φ d E + vacuumSmoothCount φ (gapFamilyCharge a) E +
      fixedFamilyBoundaryPacket φ d E (descendantLevelCutoff N) +
      |FixedFamilyDatum.activeCellQuadraturePacket d φ E (descendantLevelCutoff N)
        (actualActivePrefix d.tail d.initialState k)| +
      |FixedFamilyDatum.activeCellDensityErrorPacket d φ E (descendantLevelCutoff N)
        (actualActivePrefix d.tail d.initialState k)| := by
  have heq := fixedFamily_smoothCount_sub_integerLeading_decomposed d φ E R N k
    hR hNv hNp hk
  change _ = fixedFamilyFinitePacket φ d E (descendantLevelCutoff N) -
    fixedFamilyBoundaryPacket φ d E (descendantLevelCutoff N) +
    FixedFamilyDatum.activeCellQuadraturePacket d φ E (descendantLevelCutoff N)
      (actualActivePrefix d.tail d.initialState k) +
    FixedFamilyDatum.activeCellDensityErrorPacket d φ E (descendantLevelCutoff N)
      (actualActivePrefix d.tail d.initialState k) at heq
  rw [heq]
  calc
    _ ≤ |fixedFamilyFinitePacket φ d E (descendantLevelCutoff N) -
        fixedFamilyBoundaryPacket φ d E (descendantLevelCutoff N)| +
        |FixedFamilyDatum.activeCellQuadraturePacket d φ E (descendantLevelCutoff N)
          (actualActivePrefix d.tail d.initialState k)| +
        |FixedFamilyDatum.activeCellDensityErrorPacket d φ E (descendantLevelCutoff N)
          (actualActivePrefix d.tail d.initialState k)| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ _ := by
      have htri : |fixedFamilyFinitePacket φ d E (descendantLevelCutoff N) -
          fixedFamilyBoundaryPacket φ d E (descendantLevelCutoff N)| ≤
          |fixedFamilyFinitePacket φ d E (descendantLevelCutoff N)| +
          |fixedFamilyBoundaryPacket φ d E (descendantLevelCutoff N)| := by
        simpa only [sub_eq_add_neg, abs_neg] using
          abs_add_le (fixedFamilyFinitePacket φ d E (descendantLevelCutoff N))
            (-fixedFamilyBoundaryPacket φ d E (descendantLevelCutoff N))
      rw [abs_of_nonneg (fixedFamilyFinitePacket_nonneg φ d E _),
        abs_of_nonneg (fixedFamilyBoundaryPacket_nonneg φ d E _)] at htri
      have hp := fixedFamilyFinitePacket_le_complete φ d E (descendantLevelCutoff N)
      exact add_le_add (add_le_add
        (htri.trans (add_le_add hp le_rfl)) le_rfl) le_rfl

/-- Every inverse power holds at the unnormalized BTZ count scale, with a
single threshold for the complete admitted selector and marker class. -/
theorem fixedFamily_discreteReference_raw_bound (B : ℝ) (φ : SmoothKernel)
    {L U : ℝ} (hL : 0 < L) (hLU : L ≤ U) (P : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ a : ℝ in atTop,
      ∀ σ ∈ fixedFamilySelectors B, ∀ δ ∈ Ico (0 : ℝ) B, ∀ x ∈ Icc L U,
      |smoothCount φ (gapFamilyCharge a) (fixedFamilySpectrum B σ a δ)
          (x * gapFamilyCharge a) -
        integerLeadingSmoothCount φ (shift (gapFamilyCharge a))
          (fixedFamilyGeometry B).start (x * gapFamilyCharge a)| ≤
        C * exp (leadingAction x (gapFamilyCharge a)) /
          (sqrt (gapFamilyCharge a) * gapFamilyCharge a ^ P) := by
  obtain ⟨C, hC, hquad⟩ := exists_fixedFamily_selected_quadrature_btzScale B φ hL hLU P
  obtain ⟨R, H, hR0, hH, hR, hφ⟩ := exists_kernel_upper_bound φ
  refine ⟨C + 3, by linarith, ?_⟩
  filter_upwards [initial_vacuum_eventually_saddle_scale B φ (U := U) hL P,
    fixedFamilyBoundaryPacket_eventually_saddle_scale (fixedFamilyGeometry B) φ
      (U := U) hL P,
    activeCell_densityError_eventually_btzScale φ hL hLU P,
    eventually_ge_atTop (fixedFamilyThreshold B)] with a hinit hboundary hdensity hK
  intro σ hσ δ hδ x hx
  let d := σ a hK δ hδ
  let E := x * gapFamilyCharge a
  obtain ⟨N, hN⟩ := exists_nat_gt (max (E + R + gapFamilyCharge a / 12) (E + R + 1 / 12))
  have hNv : E + R + gapFamilyCharge a / 12 < (N : ℝ) :=
    (le_max_left _ _).trans_lt hN
  have hNp : E + R + 1 / 12 < (N : ℝ) := (le_max_right _ _).trans_lt hN
  obtain ⟨k, hk⟩ := exists_nat_gt (E + R + 1 / 12)
  have hk' : E + R + 1 / 12 < (((fixedFamilyGeometry B).start + k : ℕ) : ℝ) := by
    apply hk.trans_le
    simp only [Nat.cast_add]
    exact le_add_of_nonneg_left (Nat.cast_nonneg _)
  have hb := fixedFamily_discreteReference_abs_le d φ E R N k hR hNv hNp hk'
  have hi := hinit σ hσ hK δ hδ x hx
  have hbd := hboundary δ d (descendantLevelCutoff N) x hx
  have hq := hquad σ hσ a hK δ hδ x hx (descendantLevelCutoff N)
    (actualActivePrefix d.tail d.initialState k)
  have hd := hdensity d (descendantLevelCutoff N)
    (actualActivePrefix d.tail d.initialState k) x hx
  rw [← leadingAction_eq_btz] at hi hbd
  have hs : fixedFamilySpectrum B σ a δ = d.spectrum :=
    FixedFamilySelector.spectrum_eq σ hK hδ
  rw [hs]
  change |smoothCount φ (gapFamilyCharge a) d.spectrum E -
    integerLeadingSmoothCount φ (shift (gapFamilyCharge a)) (fixedFamilyGeometry B).start E| ≤ _
  apply hb.trans
  calc
    _ ≤ exp (leadingAction x (gapFamilyCharge a)) /
          (sqrt (gapFamilyCharge a) * gapFamilyCharge a ^ P) +
        exp (leadingAction x (gapFamilyCharge a)) /
          (sqrt (gapFamilyCharge a) * gapFamilyCharge a ^ P) +
        C * exp (leadingAction x (gapFamilyCharge a)) /
          (sqrt (gapFamilyCharge a) * gapFamilyCharge a ^ P) +
        exp (leadingAction x (gapFamilyCharge a)) /
          (sqrt (gapFamilyCharge a) * gapFamilyCharge a ^ P) :=
      add_le_add (add_le_add (add_le_add hi hbd) hq) hd
    _ = _ := by ring

/-- The actual selected permanent spectrum agrees to every inverse charge
order with the integer-spin leading reference, at the full Gaussian saddle
normalization. No spectral or analytic existence premise remains. -/
theorem fixedFamily_discreteReference_uniformRemainder
    (B : ℝ) (φ : SmoothKernel) (P : ℕ) :
    UniformRemainder B (fixedFamilySelectors B) P
      (fun σ a δ x =>
        (smoothCount φ (gapFamilyCharge a) (fixedFamilySpectrum B σ a δ)
            (x * gapFamilyCharge a) -
          integerLeadingSmoothCount φ (shift (gapFamilyCharge a))
            (fixedFamilyGeometry B).start (x * gapFamilyCharge a)) /
          saddleCountScale φ x (gapFamilyCharge a)) := by
  apply uniformRemainder_div_saddleCountScale_of_raw_bound
  intro L U hL hLU
  exact fixedFamily_discreteReference_raw_bound B φ hL hLU P

end BTZEntropy.Comparison
