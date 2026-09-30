import GapFamily.Analytic.Kernel.LowBandForm

/-!
# Hermitian symmetry of the compressed physical form

An almost-everywhere Hermitian physical kernel induces the conjugate symmetry
of the ordinary low-band integral. The final theorem includes integrability
of both pairings under the physical weak bounds.
-/

noncomputable section

open MeasureTheory Real
open scoped ComplexConjugate ENNReal

namespace GapFamily.Analytic

/-- The compressed pairing is independent of the representatives on each
restricted physical row. -/
theorem lowBandKernelPairing_congr_ae {j J : ℤ} {B : ℝ}
    {K : ℝ × ℝ → ℂ} {f f' g g' : ℝ → ℂ}
    (hf : f =ᵐ[(referenceMeasure j).restrict (Set.Ioo |(j : ℝ)| B)] f')
    (hg : g =ᵐ[(referenceMeasure J).restrict (Set.Ioo |(J : ℝ)| B)] g') :
    lowBandKernelPairing j J B K f g = lowBandKernelPairing j J B K f' g' := by
  apply integral_congr_ae
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae hf,
    Measure.quasiMeasurePreserving_snd.ae hg] with p hfp hgp
  simp only [weakKernelIntegrand, hfp, hgp]

/-- Restriction preserves the almost-everywhere Hermitian identity. -/
theorem lowBandKernel_ae_hermitian {j J : ℤ} {B : ℝ}
    {K L : ℝ × ℝ → ℂ}
    (hKL : ∀ᵐ p ∂(referenceMeasure j).prod (referenceMeasure J),
      conj (L p.swap) = K p) :
    ∀ᵐ p ∂((referenceMeasure j).restrict (Set.Ioo |(j : ℝ)| B)).prod
      ((referenceMeasure J).restrict (Set.Ioo |(J : ℝ)| B)),
      conj (L p.swap) = K p := by
  rw [Measure.prod_restrict]
  exact ae_restrict_of_ae hKL

/-- Conjugate symmetry follows from the actual product-measure swap and the
almost-everywhere Hermitian identity. Integrability is certified separately
by `lowBandKernelPairing_hermitian_integrable`. -/
theorem lowBandKernelPairing_conj_swap {j J : ℤ} {B : ℝ}
    {K L : ℝ × ℝ → ℂ} (f g : ℝ → ℂ)
    (hKL : ∀ᵐ p ∂(referenceMeasure j).prod (referenceMeasure J),
      conj (L p.swap) = K p) :
    conj (lowBandKernelPairing J j B L g f) =
      lowBandKernelPairing j J B K f g := by
  unfold lowBandKernelPairing
  rw [← integral_conj, ← integral_prod_swap]
  apply integral_congr_ae
  filter_upwards [lowBandKernel_ae_hermitian (B := B) hKL] with p hp
  simp only [weakKernelIntegrand, map_mul, starRingEnd_self_apply]
  rw [hp]
  change g p.2 * K p * conj (f p.1) = conj (f p.1) * K p * g p.2
  ring

/-- Both compressed pairings are ordinary integrable forms, and the physical
Hermitian relation gives their conjugate symmetry. -/
theorem lowBandKernelPairing_hermitian_integrable {j J : ℤ} {B C : ℝ}
    {K L : ℝ × ℝ → ℂ} {f g : ℝ → ℂ} (hC : 0 ≤ C)
    (hK : AEStronglyMeasurable K ((referenceMeasure j).prod (referenceMeasure J)))
    (hL : AEStronglyMeasurable L ((referenceMeasure J).prod (referenceMeasure j)))
    (hKbound : ∀ᵐ p ∂(referenceMeasure j).prod (referenceMeasure J),
      ‖K p‖ ≤ C * (|(j : ℝ)| * |(J : ℝ)| + sqrt p.1 * sqrt p.2))
    (hLbound : ∀ᵐ p ∂(referenceMeasure J).prod (referenceMeasure j),
      ‖L p‖ ≤ C * (|(J : ℝ)| * |(j : ℝ)| + sqrt p.1 * sqrt p.2))
    (hKL : ∀ᵐ p ∂(referenceMeasure j).prod (referenceMeasure J),
      conj (L p.swap) = K p)
    (hf : MemLp f 2 ((referenceMeasure j).restrict (Set.Ioo |(j : ℝ)| B)))
    (hg : MemLp g 2 ((referenceMeasure J).restrict (Set.Ioo |(J : ℝ)| B))) :
    Integrable (weakKernelIntegrand K f g)
      (((referenceMeasure j).restrict (Set.Ioo |(j : ℝ)| B)).prod
        ((referenceMeasure J).restrict (Set.Ioo |(J : ℝ)| B))) ∧
    Integrable (weakKernelIntegrand L g f)
      (((referenceMeasure J).restrict (Set.Ioo |(J : ℝ)| B)).prod
        ((referenceMeasure j).restrict (Set.Ioo |(j : ℝ)| B))) ∧
    conj (lowBandKernelPairing J j B L g f) =
      lowBandKernelPairing j J B K f g :=
  ⟨lowBandKernel_integrable hC hK hKbound hf hg,
    lowBandKernel_integrable hC hL hLbound hg hf,
    lowBandKernelPairing_conj_swap f g hKL⟩

end GapFamily.Analytic
