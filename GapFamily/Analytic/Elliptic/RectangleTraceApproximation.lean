import GapFamily.Analytic.Elliptic.RectangleTraceLp
import GapFamily.Analytic.Elliptic.RectangleTraceLimit

/-!
# Continuous representatives from actual four-field L² approximation

The hypotheses state ordinary strong L² approximation of a value, both first
derivatives, and the mixed derivative by actual derivatives of globally `C²`
functions. These quantitative hypotheses imply uniform convergence to a
continuous representative on each smaller forward rectangle. Existence of the
approximating sequence and its weak-PDE application remain separate obligations.
-/

noncomputable section
namespace GapFamily.Analytic.RectangleTrace

open Set MeasureTheory Filter
open scoped Topology

/-- Four strong L² convergences imply Cauchy control of the actual four
energies of smooth differences. -/
theorem fourEnergy_cauchy_of_tendsto_eLpNorm
    (F : ℕ → ℝ × ℝ → ℂ) (hF : ∀ n, ContDiff ℝ 2 (F n))
    (f fx fy fxy : ℝ × ℝ → ℂ) {A B C D : ℝ} (hAB : A ≤ B) (hCD : C ≤ D)
    (hf : MemLp f 2 (volume.restrict (Icc A B ×ˢ Icc C D)))
    (hfx : MemLp fx 2 (volume.restrict (Icc A B ×ˢ Icc C D)))
    (hfy : MemLp fy 2 (volume.restrict (Icc A B ×ˢ Icc C D)))
    (hfxy : MemLp fxy 2 (volume.restrict (Icc A B ×ˢ Icc C D)))
    (h0 : Tendsto (fun n => eLpNorm (F n - f) 2
      (volume.restrict (Icc A B ×ˢ Icc C D))) atTop (𝓝 0))
    (hx : Tendsto (fun n => eLpNorm (dx (F n) - fx) 2
      (volume.restrict (Icc A B ×ˢ Icc C D))) atTop (𝓝 0))
    (hy : Tendsto (fun n => eLpNorm (dy (F n) - fy) 2
      (volume.restrict (Icc A B ×ˢ Icc C D))) atTop (𝓝 0))
    (hxy : Tendsto (fun n => eLpNorm (dxy (F n) - fxy) 2
      (volume.restrict (Icc A B ×ˢ Icc C D))) atTop (𝓝 0)) :
    ∀ ε > (0 : ℝ), ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N,
      fourEnergy (F m - F n) A B C D < ε := by
  have hdx (n : ℕ) : ContDiff ℝ 1 (dx (F n)) :=
    ((hF n).fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  have hdy (n : ℕ) : Continuous (dy (F n)) :=
    ((hF n).continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hdxy (n : ℕ) : Continuous (dxy (F n)) :=
    ((hdx n).continuous_fderiv (by norm_num)).clm_apply continuous_const
  have H0 := energy_sub_cauchy_of_tendsto_eLpNorm F
    (fun n => (hF n).continuous) f hAB hCD hf h0
  have Hx := energy_sub_cauchy_of_tendsto_eLpNorm (fun n => dx (F n))
    (fun n => (hdx n).continuous) fx hAB hCD hfx hx
  have Hy := energy_sub_cauchy_of_tendsto_eLpNorm (fun n => dy (F n))
    hdy fy hAB hCD hfy hy
  have Hxy := energy_sub_cauchy_of_tendsto_eLpNorm (fun n => dxy (F n))
    hdxy fxy hAB hCD hfxy hxy
  intro ε hε
  have he : 0 < ε / 4 := by positivity
  obtain ⟨N0, hN0⟩ := H0 (ε/4) he
  obtain ⟨Nx, hNx⟩ := Hx (ε/4) he
  obtain ⟨Ny, hNy⟩ := Hy (ε/4) he
  obtain ⟨Nxy, hNxy⟩ := Hxy (ε/4) he
  let N := max N0 (max Nx (max Ny Nxy))
  have h0N : N0 ≤ N := le_max_left _ _
  have hxN : Nx ≤ N := (le_max_left _ _).trans (le_max_right _ _)
  have hyN : Ny ≤ N := (le_max_left _ _).trans
    ((le_max_right _ _).trans (le_max_right _ _))
  have hxyN : Nxy ≤ N := (le_max_right _ _).trans
    ((le_max_right _ _).trans (le_max_right _ _))
  refine ⟨N, fun m hm n hn => ?_⟩
  have he0 := hN0 m (h0N.trans hm) n (h0N.trans hn)
  have hex := hNx m (hxN.trans hm) n (hxN.trans hn)
  have hey := hNy m (hyN.trans hm) n (hyN.trans hn)
  have hexy := hNxy m (hxyN.trans hm) n (hxyN.trans hn)
  rw [fourEnergy, dx_sub (F m) (F n) (hF m) (hF n),
    dy_sub (F m) (F n) (hF m) (hF n), dxy_sub (F m) (F n) (hF m) (hF n)]
  linarith

/-- Actual four-field local L² approximation constructs a continuous
representative on a nondegenerate inner rectangle, with uniform convergence
of the approximants and almost-everywhere agreement with the original value. -/
theorem exists_continuousOn_ae_eq_of_four_eLpNorm
    (F : ℕ → ℝ × ℝ → ℂ) (hF : ∀ n, ContDiff ℝ 2 (F n))
    (f fx fy fxy : ℝ × ℝ → ℂ) {A B C D h k : ℝ}
    (hh : 0 < h) (hk : 0 < k) (hAB : A < B-h) (hCD : C < D-k)
    (hf : MemLp f 2 (volume.restrict (Icc A B ×ˢ Icc C D)))
    (hfx : MemLp fx 2 (volume.restrict (Icc A B ×ˢ Icc C D)))
    (hfy : MemLp fy 2 (volume.restrict (Icc A B ×ˢ Icc C D)))
    (hfxy : MemLp fxy 2 (volume.restrict (Icc A B ×ˢ Icc C D)))
    (h0 : Tendsto (fun n => eLpNorm (F n - f) 2
      (volume.restrict (Icc A B ×ˢ Icc C D))) atTop (𝓝 0))
    (hx : Tendsto (fun n => eLpNorm (dx (F n) - fx) 2
      (volume.restrict (Icc A B ×ˢ Icc C D))) atTop (𝓝 0))
    (hy : Tendsto (fun n => eLpNorm (dy (F n) - fy) 2
      (volume.restrict (Icc A B ×ˢ Icc C D))) atTop (𝓝 0))
    (hxy : Tendsto (fun n => eLpNorm (dxy (F n) - fxy) 2
      (volume.restrict (Icc A B ×ˢ Icc C D))) atTop (𝓝 0)) :
    ∃ g : ℝ × ℝ → ℂ,
      ContinuousOn g (Icc A (B-h) ×ˢ Icc C (D-k)) ∧
      TendstoUniformlyOn F g atTop (Icc A (B-h) ×ˢ Icc C (D-k)) ∧
      g =ᵐ[volume.restrict (Icc A (B-h) ×ˢ Icc C (D-k))] f := by
  apply exists_continuousOn_ae_eq_of_fourEnergy F hF f hh hk
    (fourEnergy_cauchy_of_tendsto_eLpNorm F hF f fx fy fxy
      (by linarith) (by linarith) hf hfx hfy hfxy h0 hx hy hxy) h0

end GapFamily.Analytic.RectangleTrace
