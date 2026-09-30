import GapFamily.Analytic.Elliptic.LocalPoissonEvaluation

/-! A fixed ordinary Euclidean Poisson-jet space gives one point-bound constant.
The field norms are actual Lebesgue L² norms. Translating physical data into one
fixed reference region therefore introduces no height-dependent evaluation norm. -/

noncomputable section
namespace GapFamily.Analytic.FixedPoissonPointBound

open Set MeasureTheory LocalPoisson
open scoped Topology

theorem jet_norm_le_field_sum (U : Set ℂ) (j : JetSpace U) :
    ‖j‖ ≤ ‖valueCLM U j‖ + ‖dxCLM U j‖ + ‖dyCLM U j‖ + ‖sourceCLM U j‖ := by
  change max ‖j.val.1‖ (max ‖j.val.2.1‖ (max ‖j.val.2.2.1‖ ‖j.val.2.2.2‖)) ≤ _
  simp only [valueCLM_apply, dxCLM_apply, dyCLM_apply, sourceCLM_apply]
  simp only [max_le_iff]
  have h0 := norm_nonneg j.val.1
  have hx := norm_nonneg j.val.2.1
  have hy := norm_nonneg j.val.2.2.1
  have hf := norm_nonneg j.val.2.2.2
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

theorem jet_norm_sq_le_field_sq_sum (U : Set ℂ) (j : JetSpace U) :
    ‖j‖ ^ 2 ≤ ‖valueCLM U j‖ ^ 2 + ‖dxCLM U j‖ ^ 2 +
      ‖dyCLM U j‖ ^ 2 + ‖sourceCLM U j‖ ^ 2 := by
  change (max ‖j.val.1‖ (max ‖j.val.2.1‖ (max ‖j.val.2.2.1‖ ‖j.val.2.2.2‖))) ^ 2 ≤ _
  simp only [valueCLM_apply, dxCLM_apply, dyCLM_apply, sourceCLM_apply]
  have h0 := sq_nonneg ‖j.val.1‖
  have hx := sq_nonneg ‖j.val.2.1‖
  have hy := sq_nonneg ‖j.val.2.2.1‖
  have hf := sq_nonneg ‖j.val.2.2.2‖
  rcases le_total ‖j.val.1‖ (max ‖j.val.2.1‖ (max ‖j.val.2.2.1‖ ‖j.val.2.2.2‖)) with h | h
  · rw [max_eq_right h]
    rcases le_total ‖j.val.2.1‖ (max ‖j.val.2.2.1‖ ‖j.val.2.2.2‖) with h' | h'
    · rw [max_eq_right h']
      rcases le_total ‖j.val.2.2.1‖ ‖j.val.2.2.2‖ with h'' | h''
      · rw [max_eq_right h'']; linarith
      · rw [max_eq_left h'']; linarith
    · rw [max_eq_left h']; linarith
  · rw [max_eq_left h]; linarith

/-- For a fixed open reference region and point, actual weak Poisson equations
construct a common bound for every continuous representative of every jet. -/
theorem exists_point_bound (U : Set ℂ) (hU : IsOpen U) (p : ℂ) (hp : p ∈ U) :
    ∃ C : ℝ, 0 < C ∧ ∀ (j : JetSpace U) (g : ℂ → ℂ),
      ContinuousOn g U →
      g =ᵐ[volume.restrict U] (fun w => valueCLM U j w) →
      ‖g p‖ ≤ C * (‖valueCLM U j‖ + ‖dxCLM U j‖ +
        ‖dyCLM U j‖ + ‖sourceCLM U j‖) := by
  let K : Set ℂ := {p}
  have hKU : K ⊆ U := by simpa only [K, singleton_subset_iff] using hp
  obtain ⟨C, hC, hbound⟩ := restriction_bound U hU K hKU
  refine ⟨C, hC, fun j g hg hga => ?_⟩
  have heq := restriction_eq_localRepresentative U hU K hKU ⟨p, rfl⟩ j hU hp
    (Subset.refl U) hg hga
  calc
    ‖g p‖ = ‖restriction U hU K hKU j ⟨p, rfl⟩‖ := congrArg norm heq.symm
    _ ≤ C * ‖j‖ := hbound j ⟨p, rfl⟩
    _ ≤ _ := mul_le_mul_of_nonneg_left (jet_norm_le_field_sum U j) hC.le

/-- Squared ordinary field norms also control the actual point, with one
constant selected before the jet or continuous representative is supplied. -/
theorem exists_point_sq_bound (U : Set ℂ) (hU : IsOpen U) (p : ℂ) (hp : p ∈ U) :
    ∃ C : ℝ, 0 < C ∧ ∀ (j : JetSpace U) (g : ℂ → ℂ),
      ContinuousOn g U →
      g =ᵐ[volume.restrict U] (fun w => valueCLM U j w) →
      ‖g p‖ ^ 2 ≤ C * (‖valueCLM U j‖ ^ 2 + ‖dxCLM U j‖ ^ 2 +
        ‖dyCLM U j‖ ^ 2 + ‖sourceCLM U j‖ ^ 2) := by
  let K : Set ℂ := {p}
  have hKU : K ⊆ U := by simpa only [K, singleton_subset_iff] using hp
  obtain ⟨C, hC, hbound⟩ := restriction_bound U hU K hKU
  refine ⟨C ^ 2, sq_pos_of_pos hC, fun j g hg hga => ?_⟩
  have heq := restriction_eq_localRepresentative U hU K hKU ⟨p, rfl⟩ j hU hp
    (Subset.refl U) hg hga
  have hb : ‖g p‖ ≤ C * ‖j‖ := by rw [← heq]; exact hbound j ⟨p, rfl⟩
  calc
    ‖g p‖ ^ 2 ≤ (C * ‖j‖) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC.le (norm_nonneg _))).mpr hb
    _ = C ^ 2 * ‖j‖ ^ 2 := mul_pow _ _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left (jet_norm_sq_le_field_sq_sum U j) (sq_nonneg C)

/-- The squared field norm is its literal ordinary Lebesgue integral. -/
theorem field_norm_sq_eq_integral (f : Field) :
    ‖f‖ ^ 2 = ∫ w : ℂ, ‖f w‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards with w
  exact real_inner_self_eq_norm_sq (f w)

/-- A single literal square is used for every translated physical point. -/
def referenceSquare : Set ℂ := {w | |w.re| < (1 / 4 : ℝ) ∧ |w.im| < (1 / 4 : ℝ)}

theorem isOpen_referenceSquare : IsOpen referenceSquare :=
  (isOpen_lt Complex.continuous_re.abs continuous_const).inter
    (isOpen_lt Complex.continuous_im.abs continuous_const)

theorem zero_mem_referenceSquare : (0 : ℂ) ∈ referenceSquare := by
  norm_num [referenceSquare]

/-- One constant controls the center of the fixed square by the four actual
ordinary field energies, uniformly over every admissible weak-Poisson jet. -/
theorem exists_reference_point_integral_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (j : JetSpace referenceSquare) (g : ℂ → ℂ),
      ContinuousOn g referenceSquare →
      g =ᵐ[volume.restrict referenceSquare]
        (fun w => valueCLM referenceSquare j w) →
      ‖g 0‖ ^ 2 ≤ C * ((∫ w : ℂ, ‖valueCLM referenceSquare j w‖ ^ 2) +
        (∫ w : ℂ, ‖dxCLM referenceSquare j w‖ ^ 2) +
        (∫ w : ℂ, ‖dyCLM referenceSquare j w‖ ^ 2) +
        (∫ w : ℂ, ‖sourceCLM referenceSquare j w‖ ^ 2)) := by
  obtain ⟨C, hC, hbound⟩ := exists_point_sq_bound referenceSquare
    isOpen_referenceSquare 0 zero_mem_referenceSquare
  refine ⟨C, hC, fun j g hg hga => ?_⟩
  simpa only [field_norm_sq_eq_integral] using hbound j g hg hga

end GapFamily.Analytic.FixedPoissonPointBound
