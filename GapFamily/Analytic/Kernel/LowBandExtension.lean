import GapFamily.Analytic.Kernel.LowBandOperator
import GapFamily.Analytic.Kernel.LowBandNestedForm

/-!
# Isometric extension between nested physical bands

Extension from a smaller open physical band to a larger one is implemented
by the actual indicator function. The finite Hilbert sum keeps the same spin
index set in both bands; a row outside the smaller band has zero measure.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace GapFamily.Analytic

theorem lowBand_subset (j : ℤ) {b B : ℝ} (hbB : b ≤ B) :
    Set.Ioo |(j : ℝ)| b ⊆ Set.Ioo |(j : ℝ)| B :=
  fun _ hE => ⟨hE.1, hE.2.trans_le hbB⟩

/-- Zero extension to the larger physical band has the identical `L²`
seminorm, including rows whose smaller band is empty. -/
theorem eLpNorm_lowBand_extension_eq (j : ℤ) {b B : ℝ} (hbB : b ≤ B)
    (f : ℝ → ℂ) :
    eLpNorm ((Set.Ioo |(j : ℝ)| b).indicator f) 2
      ((referenceMeasure j).restrict (Set.Ioo |(j : ℝ)| B)) =
      eLpNorm f 2 ((referenceMeasure j).restrict (Set.Ioo |(j : ℝ)| b)) := by
  rw [eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_Ioo,
    Measure.restrict_restrict_of_subset (lowBand_subset j hbB)]

theorem memLp_lowBand_extension (j : ℤ) {b B : ℝ} (hbB : b ≤ B)
    {f : ℝ → ℂ}
    (hf : MemLp f 2 ((referenceMeasure j).restrict (Set.Ioo |(j : ℝ)| b))) :
    MemLp ((Set.Ioo |(j : ℝ)| b).indicator f) 2
      ((referenceMeasure j).restrict (Set.Ioo |(j : ℝ)| B)) := by
  rwa [memLp_iff, eLpNorm_lowBand_extension_eq j hbB]

/-- The representative-based construction of low-band zero extension. -/
def lowBandRowExtend (j : ℤ) {b B : ℝ} (hbB : b ≤ B)
    (f : LowBandRow j b) : LowBandRow j B :=
  (memLp_lowBand_extension j hbB (Lp.memLp f)).toLp
    ((Set.Ioo |(j : ℝ)| b).indicator ⇑f)

theorem lowBandRowExtend_coeFn (j : ℤ) {b B : ℝ} (hbB : b ≤ B)
    (f : LowBandRow j b) :
    ⇑(lowBandRowExtend j hbB f) =ᵐ[(referenceMeasure j).restrict (Set.Ioo |(j : ℝ)| B)]
      (Set.Ioo |(j : ℝ)| b).indicator ⇑f :=
  MemLp.coeFn_toLp _

private theorem indicator_lowBand_ae_eq {j : ℤ} {b B : ℝ} (hbB : b ≤ B)
    {f g : ℝ → ℂ}
    (hfg : f =ᵐ[(referenceMeasure j).restrict (Set.Ioo |(j : ℝ)| b)] g) :
    (Set.Ioo |(j : ℝ)| b).indicator f
      =ᵐ[(referenceMeasure j).restrict (Set.Ioo |(j : ℝ)| B)]
        (Set.Ioo |(j : ℝ)| b).indicator g := by
  apply (ae_eq_restrict_iff_indicator_ae_eq measurableSet_Ioo).1
  rwa [Measure.restrict_restrict_of_subset (lowBand_subset j hbB)]

theorem lowBandRowExtend_add (j : ℤ) {b B : ℝ} (hbB : b ≤ B)
    (f g : LowBandRow j b) :
    lowBandRowExtend j hbB (f + g) = lowBandRowExtend j hbB f + lowBandRowExtend j hbB g := by
  apply Lp.ext
  refine (lowBandRowExtend_coeFn j hbB (f + g)).trans ?_
  refine (indicator_lowBand_ae_eq hbB (Lp.coeFn_add f g)).trans ?_
  filter_upwards [lowBandRowExtend_coeFn j hbB f, lowBandRowExtend_coeFn j hbB g,
    Lp.coeFn_add (lowBandRowExtend j hbB f) (lowBandRowExtend j hbB g)] with E hf hg hsum
  rw [hsum, Pi.add_apply, hf, hg]
  by_cases hE : E ∈ Set.Ioo |(j : ℝ)| b <;> simp [Set.indicator, hE]

theorem lowBandRowExtend_smul (j : ℤ) {b B : ℝ} (hbB : b ≤ B)
    (c : ℂ) (f : LowBandRow j b) :
    lowBandRowExtend j hbB (c • f) = c • lowBandRowExtend j hbB f := by
  apply Lp.ext
  refine (lowBandRowExtend_coeFn j hbB (c • f)).trans ?_
  refine (indicator_lowBand_ae_eq hbB (Lp.coeFn_smul c f)).trans ?_
  filter_upwards [lowBandRowExtend_coeFn j hbB f,
    Lp.coeFn_smul c (lowBandRowExtend j hbB f)] with E hf hsmul
  rw [hsmul, Pi.smul_apply, hf]
  by_cases hE : E ∈ Set.Ioo |(j : ℝ)| b <;> simp [Set.indicator, hE]

@[simp]
theorem norm_lowBandRowExtend (j : ℤ) {b B : ℝ} (hbB : b ≤ B)
    (f : LowBandRow j b) : ‖lowBandRowExtend j hbB f‖ = ‖f‖ := by
  rw [lowBandRowExtend, Lp.norm_toLp, eLpNorm_lowBand_extension_eq j hbB, Lp.norm_def]

/-- Inclusion of one physical row into a larger band as a linear isometry. -/
def lowBandRowExtension (j : ℤ) {b B : ℝ} (hbB : b ≤ B) :
    LowBandRow j b →ₗᵢ[ℂ] LowBandRow j B where
  toFun := lowBandRowExtend j hbB
  map_add' := lowBandRowExtend_add j hbB
  map_smul' := lowBandRowExtend_smul j hbB
  norm_map' := norm_lowBandRowExtend j hbB

@[simp]
theorem lowBandRowExtension_apply (j : ℤ) {b B : ℝ} (hbB : b ≤ B)
    (f : LowBandRow j b) : lowBandRowExtension j hbB f = lowBandRowExtend j hbB f := rfl

/-- Isometric low-band extension on a fixed finite set of spin rows. -/
def lowBandHilbertExtension {ι : Type*} [Fintype ι] (j : ι → ℤ)
    {b B : ℝ} (hbB : b ≤ B) : LowBandHilbert j b →ₗᵢ[ℂ] LowBandHilbert j B where
  toFun f := WithLp.toLp 2 (fun i => lowBandRowExtension (j i) hbB (f i))
  map_add' f g := by
    apply PiLp.ext
    intro i
    exact map_add (lowBandRowExtension (j i) hbB) (f i) (g i)
  map_smul' c f := by
    apply PiLp.ext
    intro i
    exact map_smul (lowBandRowExtension (j i) hbB) c (f i)
  norm_map' f := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1
    simp only [PiLp.norm_sq_eq_of_L2]
    apply Finset.sum_congr rfl
    intro i hi
    exact congrArg (fun r : ℝ => r ^ 2) ((lowBandRowExtension (j i) hbB).norm_map (f i))

@[simp]
theorem lowBandHilbertExtension_apply {ι : Type*} [Fintype ι] (j : ι → ℤ)
    {b B : ℝ} (hbB : b ≤ B) (f : LowBandHilbert j b) (i : ι) :
    lowBandHilbertExtension j hbB f i = lowBandRowExtension (j i) hbB (f i) := rfl

theorem lowBandHilbertExtension_coeFn {ι : Type*} [Fintype ι] (j : ι → ℤ)
    {b B : ℝ} (hbB : b ≤ B) (f : LowBandHilbert j b) (i : ι) :
    ⇑(lowBandHilbertExtension j hbB f i)
      =ᵐ[(referenceMeasure (j i)).restrict (Set.Ioo |(j i : ℝ)| B)]
        (Set.Ioo |(j i : ℝ)| b).indicator ⇑(f i) :=
  lowBandRowExtend_coeFn (j i) hbB (f i)

theorem lowBandRowExtension_coeFn_of_notMem (j : ℤ) {b B : ℝ} (hbB : b ≤ B)
    (f : LowBandRow j b) :
    ∀ᵐ E ∂(referenceMeasure j).restrict (Set.Ioo |(j : ℝ)| B),
      E ∉ Set.Ioo |(j : ℝ)| b → lowBandRowExtension j hbB f E = 0 := by
  filter_upwards [lowBandRowExtend_coeFn j hbB f] with E hE hmem
  simp only [lowBandRowExtension_apply, hE, Set.indicator_of_notMem hmem]

/-- Ordinary response integrals are unchanged by extending the input row. -/
theorem integral_mul_lowBandRowExtension_eq (j : ℤ) {b B : ℝ} (hbB : b ≤ B)
    (k : ℝ → ℂ) (f : LowBandRow j b) :
    (∫ E, k E * lowBandRowExtension j hbB f E
      ∂(referenceMeasure j).restrict (Set.Ioo |(j : ℝ)| B)) =
      ∫ E, k E * f E ∂(referenceMeasure j).restrict (Set.Ioo |(j : ℝ)| b) := by
  calc
    _ = ∫ E, (Set.Ioo |(j : ℝ)| b).indicator (fun E => k E * f E) E
        ∂(referenceMeasure j).restrict (Set.Ioo |(j : ℝ)| B) := by
      apply integral_congr_ae
      filter_upwards [lowBandRowExtend_coeFn j hbB f] with E hE
      simp only [lowBandRowExtension_apply, hE]
      by_cases hmem : E ∈ Set.Ioo |(j : ℝ)| b <;> simp [Set.indicator, hmem]
    _ = _ := by
      rw [integral_indicator measurableSet_Ioo,
        Measure.restrict_restrict_of_subset (lowBand_subset j hbB)]

/-- The actual row extension preserves the ordinary product integral. -/
theorem lowBandKernelPairing_extension_eq (j J : ℤ) {b B : ℝ} (hbB : b ≤ B)
    (K : ℝ × ℝ → ℂ) (f : LowBandRow j b) (g : LowBandRow J b) :
    lowBandKernelPairing j J B K (lowBandRowExtension j hbB f)
      (lowBandRowExtension J hbB g) = lowBandKernelPairing j J b K f g := by
  simp only [lowBandRowExtension_apply]
  rw [lowBandKernelPairing_congr_ae (lowBandRowExtend_coeFn j hbB f)
    (lowBandRowExtend_coeFn J hbB g)]
  exact lowBandKernelPairing_nested_zeroExtension_eq j J hbB K f g

/-- Every entry of the finite actual form is preserved by zero extension. -/
theorem lowBandHilbertForm_extension_eq {ι : Type*} [Fintype ι] (j : ι → ℤ)
    {b B : ℝ} (hbB : b ≤ B) (K : ι → ι → ℝ × ℝ → ℂ)
    (f g : LowBandHilbert j b) :
    lowBandHilbertForm j B K (lowBandHilbertExtension j hbB f)
      (lowBandHilbertExtension j hbB g) = lowBandHilbertForm j b K f g := by
  simp only [lowBandHilbertForm, lowBandHilbertExtension_apply,
    lowBandKernelPairing_extension_eq]

/-- The full quadratic form, including the identity term, is unchanged. -/
theorem lowBandHilbertQuadratic_extension_eq {ι : Type*} [Fintype ι] (j : ι → ℤ)
    {b B : ℝ} (hbB : b ≤ B) (K : ι → ι → ℝ × ℝ → ℂ)
    (f : LowBandHilbert j b) :
    ‖lowBandHilbertExtension j hbB f‖ ^ 2 +
      (lowBandHilbertForm j B K (lowBandHilbertExtension j hbB f)
        (lowBandHilbertExtension j hbB f)).re =
      ‖f‖ ^ 2 + (lowBandHilbertForm j b K f f).re := by
  rw [(lowBandHilbertExtension j hbB).norm_map, lowBandHilbertForm_extension_eq]

end GapFamily.Analytic
