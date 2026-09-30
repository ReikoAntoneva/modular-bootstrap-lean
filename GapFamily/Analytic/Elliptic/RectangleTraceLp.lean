import GapFamily.Analytic.Elliptic.RectangleTraceUniform
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Ordinary rectangle energy from strong L² approximation

Continuous fields on a compact rectangle have genuine finite squared-norm
integrals. Fubini identifies their ordinary iterated energy with the squared
L² norm, so strong L² approximation makes the energies of pairwise differences
arbitrarily small. The target field need not be continuous.
-/

noncomputable section
namespace GapFamily.Analytic.RectangleTrace

open Set MeasureTheory Filter
open scoped Topology

/-- The ordinary iterated energy is the genuine squared-norm integral on the
closed rectangle, including degenerate rectangles. -/
theorem energy_eq_setIntegral {F : ℝ × ℝ → ℂ} (hF : Continuous F)
    {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) :
    energy F a b c d = ∫ p in Icc a b ×ˢ Icc c d, ‖F p‖ ^ 2 := by
  have hi : IntegrableOn (fun p : ℝ × ℝ => ‖F p‖ ^ 2)
      (Icc a b ×ˢ Icc c d) (volume.prod volume) :=
    (hF.norm.pow 2).continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  symm
  rw [Measure.volume_eq_prod, setIntegral_prod _ hi]
  simp_rw [integral_Icc_eq_integral_Ioc]
  rw [← intervalIntegral.integral_of_le hab]
  apply intervalIntegral.integral_congr
  intro x _
  exact (intervalIntegral.integral_of_le hcd).symm

/-- A continuous field is actually square-integrable on every closed rectangle. -/
theorem continuous_memLp_rectangle {F : ℝ × ℝ → ℂ} (hF : Continuous F)
    (a b c d : ℝ) : MemLp F 2 (volume.restrict (Icc a b ×ˢ Icc c d)) :=
  (memLp_two_iff_integrable_sq_norm hF.aestronglyMeasurable).2
    ((hF.norm.pow 2).continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc))

private theorem integral_norm_sq_eq_norm_toLp_sq {μ : Measure (ℝ × ℝ)}
    {F : ℝ × ℝ → ℂ} (hF : MemLp F 2 μ) :
    (∫ p, ‖F p‖ ^ 2 ∂μ) = ‖hF.toLp F‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hF.coeFn_toLp] with p hp
  simp only [hp, real_inner_self_eq_norm_sq]

/-- Strong L² approximation of a rough field makes the actual ordinary
rectangle energies of continuous pairwise differences Cauchy. -/
theorem energy_sub_cauchy_of_tendsto_eLpNorm
    (G : ℕ → ℝ × ℝ → ℂ) (hG : ∀ n, Continuous (G n))
    (g : ℝ × ℝ → ℂ) {A B C D : ℝ} (hAB : A ≤ B) (hCD : C ≤ D)
    (hg : MemLp g 2 (volume.restrict (Icc A B ×ˢ Icc C D)))
    (hLp : Tendsto
      (fun n => eLpNorm (G n - g) 2 (volume.restrict (Icc A B ×ˢ Icc C D)))
      atTop (𝓝 0)) :
    ∀ ε > (0 : ℝ), ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N,
      energy (G m - G n) A B C D < ε := by
  have hmem (n : ℕ) := continuous_memLp_rectangle (hG n) A B C D
  have ht := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' G hmem g hg).2 hLp
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp ht.cauchySeq
    (Real.sqrt ε) (Real.sqrt_pos.mpr hε)
  refine ⟨N, fun m hm n hn => ?_⟩
  have hdist := hN m hm n hn
  rw [dist_eq_norm] at hdist
  rw [energy_eq_setIntegral ((hG m).sub (hG n)) hAB hCD,
    integral_norm_sq_eq_norm_toLp_sq ((hmem m).sub (hmem n)),
    MemLp.toLp_sub]
  have hs := (sq_lt_sq₀ (norm_nonneg _) (Real.sqrt_nonneg ε)).2 hdist
  simpa only [Real.sq_sqrt hε.le] using hs

end GapFamily.Analytic.RectangleTrace
