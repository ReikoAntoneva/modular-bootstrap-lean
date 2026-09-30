import BTZEntropy.Analytic.ComplexDeterminant
import BTZEntropy.Analytic.SaddleCauchy

/-!
# Actual amplitude input for the saddle jet

The complex amplitude has the same Taylor jet as the real amplitude defining
the entropy coefficients. Its values on every saddle half disk are bounded
uniformly when the saddle ranges over a compact positive interval.
-/

noncomputable section

open scoped Topology

namespace BTZEntropy

theorem iteratedDeriv_complexAmplitude_ofReal (φ : SmoothKernel) {β : ℝ}
    (hβ : 0 < β) (n : ℕ) :
    iteratedDeriv n (complexAmplitude φ) (β : ℂ) =
      ((iteratedDeriv n (amplitude φ) β : ℝ) : ℂ) := by
  rw [← iteratedDeriv_comp_ofReal_of_analyticAt
    (analyticAt_complexAmplitude φ (by simpa using hβ))]
  have heq : (fun y : ℝ => complexAmplitude φ (y : ℂ)) =ᶠ[𝓝 β]
      (fun y : ℝ => (amplitude φ y : ℂ)) := by
    filter_upwards [isOpen_Ioi.mem_nhds hβ] with y hy
    exact complexAmplitude_ofReal φ hy
  rw [heq.iteratedDeriv_eq n]
  have h := Complex.ofRealCLM.iteratedFDeriv_comp_left
    (contDiffAt_amplitude φ hβ) (i := n) (by simp)
  have hv := congrArg (fun F => F (fun _ : Fin n => (1 : ℝ))) h
  simpa [iteratedDeriv, Function.comp_def] using hv

theorem analyticOnNhd_complexAmplitude_halfDisk (φ : SmoothKernel) {β : ℝ}
    (hβ : 0 < β) :
    AnalyticOnNhd ℂ (complexAmplitude φ) (Metric.closedBall (β : ℂ) (β / 2)) := by
  intro z hz
  exact analyticAt_complexAmplitude φ
    ((half_pos hβ).trans_le (saddle_halfDisk_re_le hβ hz))

theorem complexAmplitude_halfDisk_bounded (φ : SmoothKernel) {βlo βhi : ℝ}
    (hlo : 0 < βlo) :
    ∃ M > 0, ∀ β ∈ Set.Icc βlo βhi,
      ∀ z ∈ Metric.closedBall (β : ℂ) (β / 2), ‖complexAmplitude φ z‖ ≤ M := by
  let K : Set ℂ := Metric.closedBall 0 (3 * βhi / 2) ∩ {z | βlo / 2 ≤ z.re}
  have hK : IsCompact K := (isCompact_closedBall (0 : ℂ) _).inter_right
    (isClosed_le continuous_const Complex.continuous_re)
  have hcont : ContinuousOn (complexAmplitude φ) K := by
    intro z hz
    exact (analyticAt_complexAmplitude φ ((half_pos hlo).trans_le hz.2)).continuousAt.continuousWithinAt
  obtain ⟨M, hM, hb⟩ := (hK.image_of_continuousOn hcont).isBounded.exists_pos_norm_le
  refine ⟨M, hM, ?_⟩
  intro β hβ z hz
  apply hb
  refine ⟨z, ⟨?_, ?_⟩, rfl⟩
  · simp only [Metric.mem_closedBall, dist_zero_right]
    exact (saddle_halfDisk_norm_le (hlo.trans_le hβ.1) hz).trans (by linarith [hβ.2])
  · exact (by linarith [hβ.1] : βlo / 2 ≤ β / 2).trans
      (saddle_halfDisk_re_le (hlo.trans_le hβ.1) hz)

end BTZEntropy
