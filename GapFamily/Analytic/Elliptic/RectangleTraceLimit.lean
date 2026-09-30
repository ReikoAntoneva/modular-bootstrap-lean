import GapFamily.Analytic.Elliptic.RectangleTraceUniform
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Topology.UniformSpace.UniformApproximation

/-!
# Continuous rectangular limits and almost-everywhere identification

Actual four-energy Cauchy control gives a continuous uniform limit on the inner
rectangle. Ordinary local L² convergence identifies that limit with the original
value almost everywhere. No weak derivative or smoothing existence is assumed
implicitly by these generic implication theorems.
-/

noncomputable section
namespace GapFamily.Analytic.RectangleTrace

open Set MeasureTheory Filter
open scoped Topology

theorem dx_sub (F G : ℝ × ℝ → ℂ) (hF : ContDiff ℝ 2 F) (hG : ContDiff ℝ 2 G) :
    dx (F - G) = dx F - dx G := by
  funext p
  simp only [dx, fderiv_sub (hF.differentiable (by norm_num) p)
    (hG.differentiable (by norm_num) p), sub_apply, Pi.sub_apply]

theorem dy_sub (F G : ℝ × ℝ → ℂ) (hF : ContDiff ℝ 2 F) (hG : ContDiff ℝ 2 G) :
    dy (F - G) = dy F - dy G := by
  funext p
  simp only [dy, fderiv_sub (hF.differentiable (by norm_num) p)
    (hG.differentiable (by norm_num) p), sub_apply, Pi.sub_apply]

theorem dxy_sub (F G : ℝ × ℝ → ℂ) (hF : ContDiff ℝ 2 F) (hG : ContDiff ℝ 2 G) :
    dxy (F - G) = dxy F - dxy G := by
  have hFx : ContDiff ℝ 1 (dx F) :=
    (hF.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  have hGx : ContDiff ℝ 1 (dx G) :=
    (hG.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  funext p
  simp only [dxy, dx_sub F G hF hG,
    fderiv_sub (hFx.differentiable (by norm_num) p) (hGx.differentiable (by norm_num) p),
    sub_apply, Pi.sub_apply]

/-- The four actual energies construct a continuous uniform limit. -/
theorem exists_continuousOn_limit_of_fourEnergy
    (F : ℕ → ℝ × ℝ → ℂ) (hF : ∀ n, ContDiff ℝ 2 (F n))
    {A B C D h k : ℝ} (hh : 0 < h) (hk : 0 < k)
    (hE : ∀ ε > (0 : ℝ), ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N,
      fourEnergy (F m - F n) A B C D < ε) :
    ∃ g : ℝ × ℝ → ℂ,
      ContinuousOn g (Icc A (B-h) ×ˢ Icc C (D-k)) ∧
      TendstoUniformlyOn F g atTop (Icc A (B-h) ×ˢ Icc C (D-k)) := by
  let g : ℝ × ℝ → ℂ := fun p => limUnder atTop (fun n => F n p)
  have hC := uniformCauchySeqOn_of_fourEnergy F hF hh hk hE
  have hU : TendstoUniformlyOn F g atTop (Icc A (B-h) ×ˢ Icc C (D-k)) :=
    hC.tendstoUniformlyOn_of_tendsto (fun p hp => (hC.cauchySeq hp).tendsto_limUnder)
  exact ⟨g, hU.continuousOn (Eventually.of_forall
    (fun n => (hF n).continuous.continuousOn)).frequently, hU⟩

/-- An actual local L² limit identifies a uniform limit almost everywhere.
The argument uses an almost-everywhere convergent subsequence, not a choice of
pointwise representative for an arbitrary L² class. -/
theorem ae_eq_of_uniformLimit_of_tendsto_eLpNorm
    {F : ℕ → ℝ × ℝ → ℂ} {g f : ℝ × ℝ → ℂ} {s : Set (ℝ × ℝ)}
    (hs : MeasurableSet s) (hU : TendstoUniformlyOn F g atTop s)
    (hL : Tendsto (fun n => eLpNorm (F n - f) 2 (volume.restrict s)) atTop (𝓝 0)) :
    g =ᵐ[volume.restrict s] f := by
  have hm : TendstoInMeasure (volume.restrict s) F atTop f :=
    tendstoInMeasure_of_tendsto_eLpNorm (by norm_num) hL
  obtain ⟨ns, hns, hae⟩ := hm.exists_seq_tendsto_ae
  filter_upwards [ae_restrict_mem hs, hae] with p hp hfp
  exact tendsto_nhds_unique ((hU.tendsto_at hp).comp hns.tendsto_atTop) hfp

/-- Strong L² convergence restricts to every smaller measurable region. -/
theorem tendsto_eLpNorm_restrict_of_subset
    {F : ℕ → ℝ × ℝ → ℂ} {f : ℝ × ℝ → ℂ} {s t : Set (ℝ × ℝ)} (hst : s ⊆ t)
    (hL : Tendsto (fun n => eLpNorm (F n - f) 2 (volume.restrict t)) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (F n - f) 2 (volume.restrict s)) atTop (𝓝 0) := by
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hL
    (fun _ => bot_le) (fun n => eLpNorm_mono_measure (F n - f)
      (Measure.restrict_mono_set volume hst))

/-- A continuous representative of the original value is obtained when the
four energies are Cauchy and the values converge in actual local L². -/
theorem exists_continuousOn_ae_eq_of_fourEnergy
    (F : ℕ → ℝ × ℝ → ℂ) (hF : ∀ n, ContDiff ℝ 2 (F n))
    (f : ℝ × ℝ → ℂ) {A B C D h k : ℝ} (hh : 0 < h) (hk : 0 < k)
    (hE : ∀ ε > (0 : ℝ), ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N,
      fourEnergy (F m - F n) A B C D < ε)
    (hL : Tendsto (fun n => eLpNorm (F n - f) 2
      (volume.restrict (Icc A B ×ˢ Icc C D))) atTop (𝓝 0)) :
    ∃ g : ℝ × ℝ → ℂ,
      ContinuousOn g (Icc A (B-h) ×ˢ Icc C (D-k)) ∧
      TendstoUniformlyOn F g atTop (Icc A (B-h) ×ˢ Icc C (D-k)) ∧
      g =ᵐ[volume.restrict (Icc A (B-h) ×ˢ Icc C (D-k))] f := by
  obtain ⟨g, hg, hU⟩ := exists_continuousOn_limit_of_fourEnergy F hF hh hk hE
  refine ⟨g, hg, hU, ae_eq_of_uniformLimit_of_tendsto_eLpNorm
    (measurableSet_Icc.prod measurableSet_Icc) hU ?_⟩
  apply tendsto_eLpNorm_restrict_of_subset (t := Icc A B ×ˢ Icc C D) ?_ hL
  intro p hp
  exact ⟨⟨hp.1.1, by linarith [hp.1.2]⟩, ⟨hp.2.1, by linarith [hp.2.2]⟩⟩

end GapFamily.Analytic.RectangleTrace
