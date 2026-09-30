import GapFamily.Analytic.Elliptic.WeakKernelForm
import GapFamily.Analytic.Kernel.LowBandWeight

/-!
# Compression of the physical kernel to an open low band

The low-band pairing is the ordinary integral against the product of the
restricted physical reference measures. Zero extension agrees exactly with
this compression, both for the kernel term and for the identity term. The
weak bound gives actual integrability when the two low-band vectors are in
`L²`; the compression equalities alone do not assert integrability.
-/

noncomputable section

open MeasureTheory Real
open scoped ComplexConjugate ENNReal

namespace GapFamily.Analytic

/-- The physical kernel pairing on two open low-band rows. -/
def lowBandKernelPairing (j J : ℤ) (B : ℝ) (K : ℝ × ℝ → ℂ)
    (f g : ℝ → ℂ) : ℂ :=
  ∫ p, weakKernelIntegrand K f g p
    ∂((referenceMeasure j).restrict (Set.Ioo |(j : ℝ)| B)).prod
      ((referenceMeasure J).restrict (Set.Ioo |(J : ℝ)| B))

theorem weakKernelIntegrand_lowBand_zeroExtension (j J : ℤ) (B : ℝ)
    (K : ℝ × ℝ → ℂ) (f g : ℝ → ℂ) :
    weakKernelIntegrand K ((Set.Ioo |(j : ℝ)| B).indicator f)
      ((Set.Ioo |(J : ℝ)| B).indicator g) =
      ((Set.Ioo |(j : ℝ)| B) ×ˢ (Set.Ioo |(J : ℝ)| B)).indicator
        (weakKernelIntegrand K f g) := by
  funext p
  by_cases hj : p.1 ∈ Set.Ioo |(j : ℝ)| B <;>
    by_cases hJ : p.2 ∈ Set.Ioo |(J : ℝ)| B <;>
      simp [weakKernelIntegrand, Set.indicator, hj, hJ]

/-- Zero extension realizes the actual restricted product-measure pairing.
Integrability, when needed, is supplied by the theorem below. -/
theorem weakKernelPairing_lowBand_zeroExtension_eq (j J : ℤ) (B : ℝ)
    (K : ℝ × ℝ → ℂ) (f g : ℝ → ℂ) :
    weakKernelPairing j J K ((Set.Ioo |(j : ℝ)| B).indicator f)
      ((Set.Ioo |(J : ℝ)| B).indicator g) =
      lowBandKernelPairing j J B K f g := by
  unfold weakKernelPairing lowBandKernelPairing
  rw [weakKernelIntegrand_lowBand_zeroExtension, Measure.prod_restrict,
    integral_indicator (measurableSet_Ioo.prod measurableSet_Ioo)]

/-- Compression of the identity term is compatible with zero extension. -/
theorem integral_norm_sq_lowBand_zeroExtension_eq (j : ℤ) (B : ℝ) (f : ℝ → ℂ) :
    (∫ E, ‖(Set.Ioo |(j : ℝ)| B).indicator f E‖ ^ 2 ∂referenceMeasure j) =
      ∫ E, ‖f E‖ ^ 2 ∂(referenceMeasure j).restrict (Set.Ioo |(j : ℝ)| B) := by
  have heq : (fun E => ‖(Set.Ioo |(j : ℝ)| B).indicator f E‖ ^ 2) =
      (Set.Ioo |(j : ℝ)| B).indicator (fun E => ‖f E‖ ^ 2) := by
    funext E
    by_cases hE : E ∈ Set.Ioo |(j : ℝ)| B <;> simp [Set.indicator, hE]
  rw [heq, integral_indicator measurableSet_Ioo]

/-- The compressed identity term is integrable for every low-band vector. -/
theorem integrable_norm_sq_lowBand_zeroExtension (j : ℤ) (B : ℝ) {f : ℝ → ℂ}
    (hf : MemLp f 2 ((referenceMeasure j).restrict (Set.Ioo |(j : ℝ)| B))) :
    Integrable (fun E => ‖(Set.Ioo |(j : ℝ)| B).indicator f E‖ ^ 2)
      (referenceMeasure j) := by
  have heq : (fun E => ‖(Set.Ioo |(j : ℝ)| B).indicator f E‖ ^ 2) =
      (Set.Ioo |(j : ℝ)| B).indicator (fun E => ‖f E‖ ^ 2) := by
    funext E
    by_cases hE : E ∈ Set.Ioo |(j : ℝ)| B <;> simp [Set.indicator, hE]
  rw [heq, integrable_indicator_iff measurableSet_Ioo]
  exact hf.integrable_norm_pow (by norm_num)

/-- The weak joint bound makes the compressed kernel form an ordinary
integrable pairing of low-band Hilbert vectors. -/
theorem lowBandKernel_integrable {j J : ℤ} {B C : ℝ}
    {K : ℝ × ℝ → ℂ} {f g : ℝ → ℂ} (hC : 0 ≤ C)
    (hK : AEStronglyMeasurable K ((referenceMeasure j).prod (referenceMeasure J)))
    (hbound : ∀ᵐ p ∂(referenceMeasure j).prod (referenceMeasure J),
      ‖K p‖ ≤ C * (|(j : ℝ)| * |(J : ℝ)| + sqrt p.1 * sqrt p.2))
    (hf : MemLp f 2 ((referenceMeasure j).restrict (Set.Ioo |(j : ℝ)| B)))
    (hg : MemLp g 2 ((referenceMeasure J).restrict (Set.Ioo |(J : ℝ)| B))) :
    Integrable (weakKernelIntegrand K f g)
      (((referenceMeasure j).restrict (Set.Ioo |(j : ℝ)| B)).prod
        ((referenceMeasure J).restrict (Set.Ioo |(J : ℝ)| B))) := by
  have hi := (weakKernel_integrable_and_norm_bound hC hK hbound
    (memLp_lowBand_zeroExtension j B hf) (memLp_lowBand_zeroExtension J B hg)).1
  rw [weakKernelIntegrand_lowBand_zeroExtension,
    integrable_indicator_iff (measurableSet_Ioo.prod measurableSet_Ioo)] at hi
  rwa [Measure.prod_restrict]

/-- The weighted norm of zero extension is bounded by the low-band norm,
in real-valued form. -/
theorem eLpNorm_lowBand_zeroExtension_toReal_le (j : ℤ) (B : ℝ) {f : ℝ → ℂ}
    (hf : MemLp f 2 ((referenceMeasure j).restrict (Set.Ioo |(j : ℝ)| B))) :
    (eLpNorm ((Set.Ioo |(j : ℝ)| B).indicator f) 2 (energySpaceMeasure j)).toReal ≤
      (1 + |B|) ^ 2 *
        (eLpNorm f 2 ((referenceMeasure j).restrict (Set.Ioo |(j : ℝ)| B))).toReal := by
  have h := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hf.eLpNorm_lt_top.ne)
    (eLpNorm_lowBand_zeroExtension_le j B hf.aestronglyMeasurable)
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (sq_nonneg (1 + |B|))] using h

/-- A quantitative bound on the actual compressed pairing in the low-band
Hilbert norms. The physical reference measure is used on each restricted row. -/
theorem lowBandKernelPairing_norm_le {j J : ℤ} {B C : ℝ}
    {K : ℝ × ℝ → ℂ} {f g : ℝ → ℂ} (hC : 0 ≤ C)
    (hK : AEStronglyMeasurable K ((referenceMeasure j).prod (referenceMeasure J)))
    (hbound : ∀ᵐ p ∂(referenceMeasure j).prod (referenceMeasure J),
      ‖K p‖ ≤ C * (|(j : ℝ)| * |(J : ℝ)| + sqrt p.1 * sqrt p.2))
    (hf : MemLp f 2 ((referenceMeasure j).restrict (Set.Ioo |(j : ℝ)| B)))
    (hg : MemLp g 2 ((referenceMeasure J).restrict (Set.Ioo |(J : ℝ)| B))) :
    ‖lowBandKernelPairing j J B K f g‖ ≤
      C * weakKernelMomentConstant j J * (1 + |B|) ^ 4 *
        (eLpNorm f 2 ((referenceMeasure j).restrict (Set.Ioo |(j : ℝ)| B))).toReal *
        (eLpNorm g 2 ((referenceMeasure J).restrict (Set.Ioo |(J : ℝ)| B))).toReal := by
  rw [← weakKernelPairing_lowBand_zeroExtension_eq]
  refine (weakKernel_integrable_and_norm_bound hC hK hbound
    (memLp_lowBand_zeroExtension j B hf) (memLp_lowBand_zeroExtension J B hg)).2.trans ?_
  calc
    _ ≤ C * weakKernelMomentConstant j J *
        ((1 + |B|) ^ 2 *
          (eLpNorm f 2 ((referenceMeasure j).restrict (Set.Ioo |(j : ℝ)| B))).toReal) *
        ((1 + |B|) ^ 2 *
          (eLpNorm g 2 ((referenceMeasure J).restrict (Set.Ioo |(J : ℝ)| B))).toReal) := by
      have hM := weakKernelMomentConstant_nonneg j J
      gcongr
      · exact eLpNorm_lowBand_zeroExtension_toReal_le j B hf
      · exact eLpNorm_lowBand_zeroExtension_toReal_le J B hg
    _ = _ := by ring

end GapFamily.Analytic
