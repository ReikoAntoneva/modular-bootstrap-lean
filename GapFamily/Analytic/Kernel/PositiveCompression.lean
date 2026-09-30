import GapFamily.Analytic.Kernel.KernelFormContinuity
import GapFamily.Analytic.Transform.FiniteLaplaceDensity
import GapFamily.Analytic.Kernel.LowBandWeight
import GapFamily.Analytic.Foundation.IdentityFormContinuity
import GapFamily.Analytic.Kernel.LowBandForm
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Positivity transfer from actual finite Laplace tests

The weighted approximation and ordinary-integral error estimates justify
passage from finite tests to arbitrary finite-spin weighted rows.
-/

noncomputable section

open MeasureTheory Real Filter
open scoped Topology BigOperators

namespace GapFamily.Analytic

/-- Ordinary kernel pairings converge along weighted approximants in both inputs. -/
theorem weakKernelPairing_tendsto {j J : ℤ}
    {K : ℝ × ℝ → ℂ} {F G : ℕ → ℝ → ℂ} {f g : ℝ → ℂ} {C : ℝ}
    (hC : 0 ≤ C)
    (hK : AEStronglyMeasurable K ((referenceMeasure j).prod (referenceMeasure J)))
    (hbound : ∀ᵐ p ∂(referenceMeasure j).prod (referenceMeasure J),
      ‖K p‖ ≤ C * (|(j : ℝ)| * |(J : ℝ)| + sqrt p.1 * sqrt p.2))
    (hF : ∀ n, MemLp (F n) 2 (energySpaceMeasure j))
    (hG : ∀ n, MemLp (G n) 2 (energySpaceMeasure J))
    (hf : MemLp f 2 (energySpaceMeasure j))
    (hg : MemLp g 2 (energySpaceMeasure J))
    (herrF : Tendsto (fun n => (eLpNorm (F n - f) 2 (energySpaceMeasure j)).toReal)
      atTop (𝓝 0))
    (herrG : Tendsto (fun n => (eLpNorm (G n - g) 2 (energySpaceMeasure J)).toReal)
      atTop (𝓝 0)) :
    Tendsto (fun n => weakKernelPairing j J K (F n) (G n)) atTop
      (𝓝 (weakKernelPairing j J K f g)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hsize := energy_eLpNorm_toReal_tendsto j hF hf herrF
  have hmajor : Tendsto (fun n => C * weakKernelMomentConstant j J *
      ((eLpNorm (F n) 2 (energySpaceMeasure j)).toReal *
        (eLpNorm (G n - g) 2 (energySpaceMeasure J)).toReal +
      (eLpNorm (F n - f) 2 (energySpaceMeasure j)).toReal *
        (eLpNorm g 2 (energySpaceMeasure J)).toReal)) atTop (𝓝 0) := by
    simpa using ((hsize.mul herrG).add (herrF.mul tendsto_const_nhds)).const_mul
      (C * weakKernelMomentConstant j J)
  exact squeeze_zero (fun n => norm_nonneg _)
    (fun n => weakKernelPairing_sub_norm_le hC hK hbound (hF n) hf (hG n) hg) hmajor

/-- The actual finite-spin identity-plus-kernel quadratic form. -/
def identityPlusKernelQuadratic {ι : Type*} [Fintype ι]
    (j : ι → ℤ) (K : ι → ι → ℝ × ℝ → ℂ) (f : ι → ℝ → ℂ) : ℝ :=
  (∑ i, ∫ E, ‖f i E‖ ^ 2 ∂referenceMeasure (j i)) +
    ∑ i, ∑ l, (weakKernelPairing (j i) (j l) (K i l) (f i) (f l)).re

/-- One sequence of genuine finite Laplace tests approximates all the rows,
with both its total finite-spin error and every individual error tending to zero. -/
theorem exists_finite_spin_laplace_sequence {ι : Type*} [Fintype ι]
    (j : ι → ℤ) (f : ι → ℝ → ℂ)
    (hf : ∀ i, MemLp (f i) 2 (energySpaceMeasure (j i))) :
    ∃ (m : ℕ → ι → ℕ) (c : ∀ n i, Fin (m n i) → ℂ),
      (∀ n i, MemLp (finiteLaplaceSum (c n i)) 2 (energySpaceMeasure (j i))) ∧
      Tendsto (fun n => ∑ i, (eLpNorm (f i - finiteLaplaceSum (c n i)) 2
        (energySpaceMeasure (j i))).toReal) atTop (𝓝 0) ∧
      (∀ i, Tendsto (fun n => (eLpNorm (finiteLaplaceSum (c n i) - f i) 2
        (energySpaceMeasure (j i))).toReal) atTop (𝓝 0)) := by
  classical
  choose m c hmem herr hzero using fun n : ℕ =>
    exists_finite_spin_laplace_approximation j f hf
      (show 0 < (1 : ℝ) / ((n : ℝ) + 1) by positivity)
  have hsum : Tendsto (fun n => ∑ i, (eLpNorm (f i - finiteLaplaceSum (c n i)) 2
      (energySpaceMeasure (j i))).toReal) atTop (𝓝 0) := by
    apply squeeze_zero (fun n => Finset.sum_nonneg (fun _ _ => ENNReal.toReal_nonneg))
      (fun n => (herr n).le)
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  refine ⟨m, c, fun n i => (hmem n i).1, hsum, ?_⟩
  intro i
  have hrow : Tendsto (fun n => (eLpNorm (f i - finiteLaplaceSum (c n i)) 2
      (energySpaceMeasure (j i))).toReal) atTop (𝓝 0) := by
    apply squeeze_zero (fun _ => ENNReal.toReal_nonneg) (g := fun n =>
      ∑ l, (eLpNorm (f l - finiteLaplaceSum (c n l)) 2 (energySpaceMeasure (j l))).toReal) ?_ hsum
    intro n
    exact Finset.single_le_sum (f := fun l => (eLpNorm (f l - finiteLaplaceSum (c n l)) 2
      (energySpaceMeasure (j l))).toReal)
      (fun l _ => ENNReal.toReal_nonneg) (Finset.mem_univ i)
  simpa only [eLpNorm_sub_comm (finiteLaplaceSum _) (f i)] using hrow

/-- Both the identity contribution and the finite kernel sum pass to weighted limits. -/
theorem identityPlusKernelQuadratic_tendsto {ι : Type*} [Fintype ι]
    (j : ι → ℤ) (K : ι → ι → ℝ × ℝ → ℂ) {C : ℝ} (hC : 0 ≤ C)
    (hK : ∀ i l, AEStronglyMeasurable (K i l)
      ((referenceMeasure (j i)).prod (referenceMeasure (j l))))
    (hbound : ∀ i l, ∀ᵐ p ∂(referenceMeasure (j i)).prod (referenceMeasure (j l)),
      ‖K i l p‖ ≤ C * (|(j i : ℝ)| * |(j l : ℝ)| + sqrt p.1 * sqrt p.2))
    {F : ℕ → ι → ℝ → ℂ} {f : ι → ℝ → ℂ}
    (hF : ∀ n i, MemLp (F n i) 2 (energySpaceMeasure (j i)))
    (hf : ∀ i, MemLp (f i) 2 (energySpaceMeasure (j i)))
    (herr : ∀ i, Tendsto (fun n => (eLpNorm (F n i - f i) 2
      (energySpaceMeasure (j i))).toReal) atTop (𝓝 0)) :
    Tendsto (fun n => identityPlusKernelQuadratic j K (F n)) atTop
      (𝓝 (identityPlusKernelQuadratic j K f)) := by
  unfold identityPlusKernelQuadratic
  apply Tendsto.add
  · exact tendsto_finsetSum _ (fun i _ => identityForm_tendsto (j i)
      (fun n => hF n i) (hf i) (herr i))
  · apply tendsto_finsetSum
    intro i hi
    apply tendsto_finsetSum
    intro l hl
    exact Complex.continuous_re.tendsto _ |>.comp
      (weakKernelPairing_tendsto hC (hK i l) (hbound i l)
        (fun n => hF n i) (fun n => hF n l) (hf i) (hf l) (herr i) (herr l))

/-- Positivity on genuine finite Laplace tests extends to every finite family
of weighted energy rows. Finite-test positivity and the weak bound remain explicit. -/
theorem identityPlusKernelQuadratic_nonneg_of_finiteLaplace {ι : Type*} [Fintype ι]
    (j : ι → ℤ) (K : ι → ι → ℝ × ℝ → ℂ) {C : ℝ} (hC : 0 ≤ C)
    (hK : ∀ i l, AEStronglyMeasurable (K i l)
      ((referenceMeasure (j i)).prod (referenceMeasure (j l))))
    (hbound : ∀ i l, ∀ᵐ p ∂(referenceMeasure (j i)).prod (referenceMeasure (j l)),
      ‖K i l p‖ ≤ C * (|(j i : ℝ)| * |(j l : ℝ)| + sqrt p.1 * sqrt p.2))
    (hpositive : ∀ (m : ι → ℕ) (c : ∀ i, Fin (m i) → ℂ),
      0 ≤ identityPlusKernelQuadratic j K (fun i => finiteLaplaceSum (c i)))
    (f : ι → ℝ → ℂ) (hf : ∀ i, MemLp (f i) 2 (energySpaceMeasure (j i))) :
    0 ≤ identityPlusKernelQuadratic j K f := by
  obtain ⟨m, c, hmem, _, herr⟩ := exists_finite_spin_laplace_sequence j f hf
  have hlim := identityPlusKernelQuadratic_tendsto j K hC hK hbound hmem hf herr
  exact ge_of_tendsto' hlim (fun n => hpositive (m n) (c n))

/-- The actual identity-plus-kernel form on the restricted open physical bands. -/
def lowBandIdentityPlusKernelQuadratic {ι : Type*} [Fintype ι]
    (j : ι → ℤ) (B : ℝ) (K : ι → ι → ℝ × ℝ → ℂ) (f : ι → ℝ → ℂ) : ℝ :=
  (∑ i, ∫ E, ‖f i E‖ ^ 2 ∂(referenceMeasure (j i)).restrict (Set.Ioo |(j i : ℝ)| B)) +
    ∑ i, ∑ l, (lowBandKernelPairing (j i) (j l) B (K i l) (f i) (f l)).re

theorem identityPlusKernelQuadratic_lowBand_zeroExtension {ι : Type*} [Fintype ι]
    (j : ι → ℤ) (B : ℝ) (K : ι → ι → ℝ × ℝ → ℂ) (f : ι → ℝ → ℂ) :
    identityPlusKernelQuadratic j K (fun i => (Set.Ioo |(j i : ℝ)| B).indicator (f i)) =
      lowBandIdentityPlusKernelQuadratic j B K f := by
  simp only [identityPlusKernelQuadratic, lowBandIdentityPlusKernelQuadratic,
    integral_norm_sq_lowBand_zeroExtension_eq, weakKernelPairing_lowBand_zeroExtension_eq]

/-- Positivity on actual finite Laplace tests passes to the actual open-band
compression, by the proved zero-extension and weighted-space approximation. -/
theorem lowBandIdentityPlusKernelQuadratic_nonneg_of_finiteLaplace
    {ι : Type*} [Fintype ι] (j : ι → ℤ) (B : ℝ)
    (K : ι → ι → ℝ × ℝ → ℂ) {C : ℝ} (hC : 0 ≤ C)
    (hK : ∀ i l, AEStronglyMeasurable (K i l)
      ((referenceMeasure (j i)).prod (referenceMeasure (j l))))
    (hbound : ∀ i l, ∀ᵐ p ∂(referenceMeasure (j i)).prod (referenceMeasure (j l)),
      ‖K i l p‖ ≤ C * (|(j i : ℝ)| * |(j l : ℝ)| + sqrt p.1 * sqrt p.2))
    (hpositive : ∀ (m : ι → ℕ) (c : ∀ i, Fin (m i) → ℂ),
      0 ≤ identityPlusKernelQuadratic j K (fun i => finiteLaplaceSum (c i)))
    (f : ι → ℝ → ℂ)
    (hf : ∀ i, MemLp (f i) 2 ((referenceMeasure (j i)).restrict (Set.Ioo |(j i : ℝ)| B))) :
    0 ≤ lowBandIdentityPlusKernelQuadratic j B K f := by
  rw [← identityPlusKernelQuadratic_lowBand_zeroExtension]
  exact identityPlusKernelQuadratic_nonneg_of_finiteLaplace j K hC hK hbound hpositive _
    (fun i => memLp_lowBand_zeroExtension (j i) B (hf i))

/-- The compressed positivity endpoint also certifies every ordinary integral
appearing in the form, including the product integrals in scalar rows. -/
theorem lowBand_integrable_and_nonneg_of_finiteLaplace
    {ι : Type*} [Fintype ι] (j : ι → ℤ) (B : ℝ)
    (K : ι → ι → ℝ × ℝ → ℂ) {C : ℝ} (hC : 0 ≤ C)
    (hK : ∀ i l, AEStronglyMeasurable (K i l)
      ((referenceMeasure (j i)).prod (referenceMeasure (j l))))
    (hbound : ∀ i l, ∀ᵐ p ∂(referenceMeasure (j i)).prod (referenceMeasure (j l)),
      ‖K i l p‖ ≤ C * (|(j i : ℝ)| * |(j l : ℝ)| + sqrt p.1 * sqrt p.2))
    (hpositive : ∀ (m : ι → ℕ) (c : ∀ i, Fin (m i) → ℂ),
      0 ≤ identityPlusKernelQuadratic j K (fun i => finiteLaplaceSum (c i)))
    (f : ι → ℝ → ℂ)
    (hf : ∀ i, MemLp (f i) 2 ((referenceMeasure (j i)).restrict (Set.Ioo |(j i : ℝ)| B))) :
    (∀ i, Integrable (fun E => ‖f i E‖ ^ 2)
      ((referenceMeasure (j i)).restrict (Set.Ioo |(j i : ℝ)| B))) ∧
    (∀ i l, Integrable (weakKernelIntegrand (K i l) (f i) (f l))
      (((referenceMeasure (j i)).restrict (Set.Ioo |(j i : ℝ)| B)).prod
        ((referenceMeasure (j l)).restrict (Set.Ioo |(j l : ℝ)| B)))) ∧
    0 ≤ lowBandIdentityPlusKernelQuadratic j B K f := by
  refine ⟨fun i => (hf i).integrable_norm_pow (by norm_num), ?_, ?_⟩
  · exact fun i l => lowBandKernel_integrable hC (hK i l) (hbound i l) (hf i) (hf l)
  · exact lowBandIdentityPlusKernelQuadratic_nonneg_of_finiteLaplace
      j B K hC hK hbound hpositive f hf

end GapFamily.Analytic
