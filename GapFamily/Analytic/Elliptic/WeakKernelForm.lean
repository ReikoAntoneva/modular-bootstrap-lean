import GapFamily.Analytic.Foundation.WeightedMoment
import GapFamily.Analytic.Foundation.PhysicalBound
import GapFamily.Analytic.Kernel.KernelAnalytic
import Mathlib.MeasureTheory.Integral.Prod

/-!
# The ordinary integral of a weakly bounded physical kernel

A joint spin/energy bound yields an integrable kernel pairing. The measure is
the actual product of the physical reference measures, including the scalar
`dE/E` row. Every ordinary moment used below has an explicit integrability
proof; no convention for a nonintegrable Bochner integral is used.
-/

noncomputable section

open MeasureTheory Real
open scoped ComplexConjugate

namespace GapFamily.Analytic

/-- The test integrand of a complex physical kernel. -/
def weakKernelIntegrand (K : ℝ × ℝ → ℂ) (f g : ℝ → ℂ) (p : ℝ × ℝ) : ℂ :=
  conj (f p.1) * K p * g p.2

/-- The ordinary product-measure pairing, with integrability certified below. -/
def weakKernelPairing (j J : ℤ) (K : ℝ × ℝ → ℂ) (f g : ℝ → ℂ) : ℂ :=
  ∫ p, weakKernelIntegrand K f g p ∂(referenceMeasure j).prod (referenceMeasure J)

theorem weakKernelIntegrand_aestronglyMeasurable {j J : ℤ}
    {K : ℝ × ℝ → ℂ} {f g : ℝ → ℂ}
    (hK : AEStronglyMeasurable K ((referenceMeasure j).prod (referenceMeasure J)))
    (hf : MemLp f 2 (energySpaceMeasure j))
    (hg : MemLp g 2 (energySpaceMeasure J)) :
    AEStronglyMeasurable (weakKernelIntegrand K f g)
      ((referenceMeasure j).prod (referenceMeasure J)) := by
  have hfm := hf.aestronglyMeasurable.mono_ac (referenceMeasure_absolutelyContinuous_energySpace j)
  have hgm := hg.aestronglyMeasurable.mono_ac (referenceMeasure_absolutelyContinuous_energySpace J)
  exact ((Complex.continuous_conj.comp_aestronglyMeasurable hfm.comp_fst).mul hK).mul
    hgm.comp_snd

/-- A weak physical kernel bound is a true integrability statement and bounds
the complex pairing by products of ordinary moments. -/
theorem weakKernel_integrable_and_moment_bound {j J : ℤ}
    {K : ℝ × ℝ → ℂ} {f g : ℝ → ℂ} {C : ℝ}
    (hK : AEStronglyMeasurable K ((referenceMeasure j).prod (referenceMeasure J)))
    (hbound : ∀ᵐ p ∂(referenceMeasure j).prod (referenceMeasure J),
      ‖K p‖ ≤ C * (|(j : ℝ)| * |(J : ℝ)| + sqrt p.1 * sqrt p.2))
    (hf : MemLp f 2 (energySpaceMeasure j))
    (hg : MemLp g 2 (energySpaceMeasure J))
    (hfspin : Integrable (fun e => |(j : ℝ)| * ‖f e‖) (referenceMeasure j))
    (hgspin : Integrable (fun E => |(J : ℝ)| * ‖g E‖) (referenceMeasure J))
    (hfenergy : Integrable (fun e => sqrt e * ‖f e‖) (referenceMeasure j))
    (hgenergy : Integrable (fun E => sqrt E * ‖g E‖) (referenceMeasure J)) :
    Integrable (weakKernelIntegrand K f g)
      ((referenceMeasure j).prod (referenceMeasure J)) ∧
      ‖weakKernelPairing j J K f g‖ ≤ C *
        ((∫ e, |(j : ℝ)| * ‖f e‖ ∂referenceMeasure j) *
          (∫ E, |(J : ℝ)| * ‖g E‖ ∂referenceMeasure J) +
        (∫ e, sqrt e * ‖f e‖ ∂referenceMeasure j) *
          (∫ E, sqrt E * ‖g E‖ ∂referenceMeasure J)) := by
  let B : ℝ × ℝ → ℝ := fun p => C *
    ((|(j : ℝ)| * ‖f p.1‖) * (|(J : ℝ)| * ‖g p.2‖) +
      (sqrt p.1 * ‖f p.1‖) * (sqrt p.2 * ‖g p.2‖))
  have hB : Integrable B ((referenceMeasure j).prod (referenceMeasure J)) :=
    ((hfspin.mul_prod hgspin).add (hfenergy.mul_prod hgenergy)).const_mul C
  have hnorm : ∀ᵐ p ∂(referenceMeasure j).prod (referenceMeasure J),
      ‖weakKernelIntegrand K f g p‖ ≤ B p := by
    filter_upwards [hbound] with p hp
    simp only [weakKernelIntegrand, norm_mul, Complex.norm_conj]
    calc
      ‖f p.1‖ * ‖K p‖ * ‖g p.2‖ ≤
          ‖f p.1‖ * (C * (|(j : ℝ)| * |(J : ℝ)| + sqrt p.1 * sqrt p.2)) * ‖g p.2‖ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp (norm_nonneg _))
          (norm_nonneg _)
      _ = B p := by dsimp [B]; ring
  have hi := hB.mono' (weakKernelIntegrand_aestronglyMeasurable hK hf hg) hnorm
  refine ⟨hi, ?_⟩
  calc
    ‖weakKernelPairing j J K f g‖ ≤ ∫ p, B p ∂(referenceMeasure j).prod (referenceMeasure J) :=
      norm_integral_le_of_norm_le hB hnorm
    _ = _ := by
      dsimp [B]
      rw [integral_const_mul, integral_add (hfspin.mul_prod hgspin) (hfenergy.mul_prod hgenergy),
        integral_prod_mul (fun e => |(j : ℝ)| * ‖f e‖) (fun E => |(J : ℝ)| * ‖g E‖),
        integral_prod_mul (fun e => sqrt e * ‖f e‖) (fun E => sqrt E * ‖g E‖)]

/-- The finite coefficient of the weak form on a fixed pair of physical rows. -/
def weakKernelMomentConstant (j J : ℤ) : ℝ :=
  sqrt (∫ e, (j : ℝ) ^ 2 / (1 + e) ^ 4 ∂referenceMeasure j) *
    sqrt (∫ E, (J : ℝ) ^ 2 / (1 + E) ^ 4 ∂referenceMeasure J) +
  sqrt (∫ e, e / (1 + e) ^ 4 ∂referenceMeasure j) *
    sqrt (∫ E, E / (1 + E) ^ 4 ∂referenceMeasure J)

theorem weakKernelMomentConstant_nonneg (j J : ℤ) : 0 ≤ weakKernelMomentConstant j J := by
  unfold weakKernelMomentConstant
  positivity

/-- A measurable weakly bounded kernel defines an integrable pairing of any two
weighted `L²` functions and has the required product-norm bound. -/
theorem weakKernel_integrable_and_norm_bound {j J : ℤ}
    {K : ℝ × ℝ → ℂ} {f g : ℝ → ℂ} {C : ℝ} (hC : 0 ≤ C)
    (hK : AEStronglyMeasurable K ((referenceMeasure j).prod (referenceMeasure J)))
    (hbound : ∀ᵐ p ∂(referenceMeasure j).prod (referenceMeasure J),
      ‖K p‖ ≤ C * (|(j : ℝ)| * |(J : ℝ)| + sqrt p.1 * sqrt p.2))
    (hf : MemLp f 2 (energySpaceMeasure j))
    (hg : MemLp g 2 (energySpaceMeasure J)) :
    Integrable (weakKernelIntegrand K f g)
      ((referenceMeasure j).prod (referenceMeasure J)) ∧
      ‖weakKernelPairing j J K f g‖ ≤ C * weakKernelMomentConstant j J *
        (eLpNorm f 2 (energySpaceMeasure j)).toReal *
        (eLpNorm g 2 (energySpaceMeasure J)).toReal := by
  obtain ⟨hfsi, hfs⟩ := spin_moment_cauchy j hf
  obtain ⟨hgsi, hgs⟩ := spin_moment_cauchy J hg
  obtain ⟨hfei, hfe⟩ := sqrtEnergy_moment_cauchy j hf
  obtain ⟨hgei, hge⟩ := sqrtEnergy_moment_cauchy J hg
  obtain ⟨hi, hb⟩ := weakKernel_integrable_and_moment_bound hK hbound hf hg
    hfsi hgsi hfei hgei
  refine ⟨hi, hb.trans ?_⟩
  have hsp := mul_le_mul hfs hgs
    (integral_nonneg fun E => mul_nonneg (abs_nonneg _) (norm_nonneg (g E)))
    (mul_nonneg (sqrt_nonneg _) (sqrt_nonneg _))
  have hen := mul_le_mul hfe hge
    (integral_nonneg fun E => mul_nonneg (sqrt_nonneg _) (norm_nonneg (g E)))
    (mul_nonneg (sqrt_nonneg _) (sqrt_nonneg _))
  have h := mul_le_mul_of_nonneg_left (add_le_add hsp hen) hC
  rw [energy_sqrt_integral_eq_eLpNorm j hf, energy_sqrt_integral_eq_eLpNorm J hg] at h
  convert h using 1
  dsimp [weakKernelMomentConstant]
  ring

/-- The product pairing also equals the iterated ordinary integral. -/
theorem weakKernelPairing_eq_iterated {j J : ℤ}
    {K : ℝ × ℝ → ℂ} {f g : ℝ → ℂ} {C : ℝ} (hC : 0 ≤ C)
    (hK : AEStronglyMeasurable K ((referenceMeasure j).prod (referenceMeasure J)))
    (hbound : ∀ᵐ p ∂(referenceMeasure j).prod (referenceMeasure J),
      ‖K p‖ ≤ C * (|(j : ℝ)| * |(J : ℝ)| + sqrt p.1 * sqrt p.2))
    (hf : MemLp f 2 (energySpaceMeasure j))
    (hg : MemLp g 2 (energySpaceMeasure J)) :
    weakKernelPairing j J K f g =
      ∫ e, ∫ E, conj (f e) * K (e, E) * g E ∂referenceMeasure J ∂referenceMeasure j := by
  exact integral_prod _ (weakKernel_integrable_and_norm_bound hC hK hbound hf hg).1

/-- The actual higher-order arithmetic kernel is measurable on the real energy plane. -/
theorem higherKernel_real_aestronglyMeasurable (j J : ℤ) :
    AEStronglyMeasurable (fun p : ℝ × ℝ => higherKernel j J p.1 p.2)
      ((referenceMeasure j).prod (referenceMeasure J)) := by
  exact ((continuous_higherKernel j J).comp
    (by fun_prop : Continuous (fun p : ℝ × ℝ => ((p.1 : ℂ), (p.2 : ℂ))))).aestronglyMeasurable

/-- The proved physical estimate is an almost-everywhere weak bound for the
actual reference product measure. -/
theorem higherKernel_ae_weak_bound (j J : ℤ) :
    ∀ᵐ p ∂(referenceMeasure j).prod (referenceMeasure J),
      ‖higherKernel j J p.1 p.2‖ ≤
        (64 * π ^ 2) * (|(j : ℝ)| * |(J : ℝ)| + sqrt p.1 * sqrt p.2) := by
  filter_upwards
    [Measure.quasiMeasurePreserving_fst.ae (referenceMeasure_ae_above_edge j),
      Measure.quasiMeasurePreserving_snd.ae (referenceMeasure_ae_above_edge J)] with p hp hP
  have hb := norm_higherKernel_physical_le_sqrt j J p.1 p.2 hp.le hP.le
  rw [sqrt_mul ((abs_nonneg _).trans hp.le)] at hb
  exact hb.trans (mul_le_mul_of_nonneg_left
    (le_add_of_nonneg_left (mul_nonneg (abs_nonneg _) (abs_nonneg _))) (by positivity))

/-- Unconditional weighted-form boundedness of the actual higher kernel.
The separately continued zero-order kernel is not included in this theorem. -/
theorem higherKernel_integrable_and_norm_bound (j J : ℤ) {f g : ℝ → ℂ}
    (hf : MemLp f 2 (energySpaceMeasure j))
    (hg : MemLp g 2 (energySpaceMeasure J)) :
    Integrable (weakKernelIntegrand (fun p => higherKernel j J p.1 p.2) f g)
      ((referenceMeasure j).prod (referenceMeasure J)) ∧
      ‖weakKernelPairing j J (fun p => higherKernel j J p.1 p.2) f g‖ ≤
        (64 * π ^ 2) * weakKernelMomentConstant j J *
          (eLpNorm f 2 (energySpaceMeasure j)).toReal *
          (eLpNorm g 2 (energySpaceMeasure J)).toReal := by
  exact weakKernel_integrable_and_norm_bound (by positivity)
    (higherKernel_real_aestronglyMeasurable j J) (higherKernel_ae_weak_bound j J) hf hg

end GapFamily.Analytic
