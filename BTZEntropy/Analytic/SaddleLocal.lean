import BTZEntropy.Analytic.AmplitudeJet
import BTZEntropy.Analytic.IntegralTaylorTail
import BTZEntropy.Analytic.SaddleTailMoment
import BTZEntropy.Analytic.SaddleJetIntegral

/-!
# Local saddle integral with whole-line coefficients

A uniform Gaussian Cauchy bound controls the integrated Taylor remainder.
Polynomial Gaussian moments control the coefficient mass omitted by the
moving contour cutoff.
-/

noncomputable section

open Set MeasureTheory Filter
open scoped Topology BigOperators

namespace BTZEntropy

def saddleLocalDomain (b ε : ℝ) : Set ℝ := {t | |ε * t| ≤ b / 4}

def saddleGaussianWeight (B : ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  (1 + |t|) ^ n * Real.exp (-(2 * phaseConstant / (9 * B ^ 3)) * t ^ 2)

def saddleDerivativeConstant (b M : ℝ) (n : ℕ) : ℝ :=
  n.factorial * M * (4 / b) ^ n

theorem measurableSet_saddleLocalDomain (b ε : ℝ) : MeasurableSet (saddleLocalDomain b ε) :=
  measurableSet_le ((continuous_const.mul continuous_id).abs.measurable) measurable_const

theorem saddleGaussianWeight_nonneg (B : ℝ) (n : ℕ) (t : ℝ) :
    0 ≤ saddleGaussianWeight B n t := by unfold saddleGaussianWeight; positivity

theorem integrable_saddleGaussianWeight {B : ℝ} (hB : 0 < B) (n : ℕ) :
    Integrable (saddleGaussianWeight B n) := by
  have hp := phaseConstant_pos
  convert integrable_one_add_abs_pow_gaussian
    (show 0 < 4 * phaseConstant / (9 * B ^ 3) by positivity) n using 1
  ext t
  unfold saddleGaussianWeight
  congr 2
  ring

theorem saddleDerivativeConstant_nonneg {b M : ℝ} (hb : 0 < b) (hM : 0 ≤ M) (n : ℕ) :
    0 ≤ saddleDerivativeConstant b M n := by unfold saddleDerivativeConstant; positivity

theorem abs_mul_le_of_mem_uIcc {b ε t e : ℝ}
    (ht : t ∈ saddleLocalDomain b ε) (he : e ∈ uIcc 0 ε) : |e * t| ≤ b / 4 := by
  have ha : |e| ≤ |ε| := by simpa using abs_sub_left_of_mem_uIcc he
  have hb : |e * t| ≤ |ε * t| := by
    simpa [abs_mul] using mul_le_mul_of_nonneg_right ha (abs_nonneg t)
  exact hb.trans ht

theorem weighted_jet_le_saddleGaussianWeight {f : ℝ → ℂ} {b B M : ℝ}
    (hb : 0 < b) (hM : 0 ≤ M) {n q : ℕ}
    (hf : ∀ t, ‖f t‖ ≤ saddleDerivativeConstant b M n * saddleGaussianWeight B n t)
    (t : ℝ) :
    |t| ^ q * ‖f t‖ ≤
      saddleDerivativeConstant b M n * saddleGaussianWeight B (q + n) t := by
  calc
    |t| ^ q * ‖f t‖ ≤ |t| ^ q *
        (saddleDerivativeConstant b M n * saddleGaussianWeight B n t) :=
      mul_le_mul_of_nonneg_left (hf t) (by positivity)
    _ ≤ (1 + |t|) ^ q *
        (saddleDerivativeConstant b M n * saddleGaussianWeight B n t) := by
      apply mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (abs_nonneg t) (by linarith) q)
      exact mul_nonneg (saddleDerivativeConstant_nonneg hb hM n)
        (saddleGaussianWeight_nonneg B n t)
    _ = _ := by simp only [saddleGaussianWeight, pow_add]; ring

theorem weighted_jet_moment_le {f : ℝ → ℂ} {b B M : ℝ}
    (hb : 0 < b) (hB : 0 < B) (hM : 0 ≤ M) {n q : ℕ} (hi : Integrable f)
    (hf : ∀ t, ‖f t‖ ≤ saddleDerivativeConstant b M n * saddleGaussianWeight B n t) :
    Integrable (fun t => |t| ^ q * ‖f t‖) ∧
      (∫ t : ℝ, |t| ^ q * ‖f t‖) ≤
        saddleDerivativeConstant b M n * ∫ t : ℝ, saddleGaussianWeight B (q + n) t := by
  have hmaj := (integrable_saddleGaussianWeight hB (q + n)).const_mul
    (saddleDerivativeConstant b M n)
  have hpoint := weighted_jet_le_saddleGaussianWeight (q := q) hb hM hf
  have hiq : Integrable (fun t => |t| ^ q * ‖f t‖) := by
    apply hmaj.mono'
      ((continuous_abs.pow q).aestronglyMeasurable.mul hi.aestronglyMeasurable.norm)
    filter_upwards [] with t
    change ‖|t| ^ q * ‖f t‖‖ ≤ _
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (pow_nonneg (abs_nonneg t) q) (norm_nonneg (f t)))]
    exact hpoint t
  refine ⟨hiq, ?_⟩
  rw [← integral_const_mul]
  exact integral_mono hiq hmaj hpoint

theorem saddle_tail_term_le {f : ℝ → ℂ} {b B M ε : ℝ}
    (hb : 0 < b) (hB : 0 < B) (hM : 0 ≤ M) {n N : ℕ} (hn : n ≤ N)
    (hi : Integrable f)
    (hf : ∀ t, ‖f t‖ ≤ saddleDerivativeConstant b M n * saddleGaussianWeight B n t) :
    (|ε| ^ n / (n.factorial : ℝ)) *
        (∫ t in (saddleLocalDomain b ε)ᶜ, ‖f t‖) ≤
      |ε| ^ (N + 1) *
        (saddleDerivativeConstant b M n /
          ((n.factorial : ℝ) * (b / 4) ^ (N + 1 - n))) *
        ∫ t : ℝ, saddleGaussianWeight B (N + 1) t := by
  let q := N + 1 - n
  have hq : q + n = N + 1 := by dsimp [q]; omega
  have hm := weighted_jet_moment_le (q := q) hb hB hM hi hf
  have hs : (saddleLocalDomain b ε)ᶜ ⊆ {t : ℝ | b / 4 ≤ |ε * t|} := by
    intro t ht
    simp only [saddleLocalDomain, mem_compl_iff, Set.mem_ofPred_eq, not_le] at ht
    exact ht.le
  have ht : (∫ t in (saddleLocalDomain b ε)ᶜ, ‖f t‖) ≤
      |ε| ^ q / (b / 4) ^ q *
        (saddleDerivativeConstant b M n * ∫ t : ℝ, saddleGaussianWeight B (N + 1) t) := by
    calc
      _ ≤ ∫ t in {t : ℝ | b / 4 ≤ |ε * t|}, ‖f t‖ :=
        setIntegral_mono_set hi.norm.integrableOn
          (Eventually.of_forall (fun t => norm_nonneg _)) (Eventually.of_forall hs)
      _ ≤ |ε| ^ q / (b / 4) ^ q * ∫ t : ℝ, |t| ^ q * ‖f t‖ :=
        integral_norm_outside_scaled_le_moment (by positivity) hi q hm.1
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        simpa only [hq] using hm.2
  calc
    _ ≤ (|ε| ^ n / (n.factorial : ℝ)) *
        (|ε| ^ q / (b / 4) ^ q *
          (saddleDerivativeConstant b M n * ∫ t : ℝ, saddleGaussianWeight B (N + 1) t)) :=
      mul_le_mul_of_nonneg_left ht (by positivity)
    _ = _ := by
      have hp : |ε| ^ n * |ε| ^ q = |ε| ^ (N + 1) := by
        rw [← pow_add]
        congr 1
        omega
      calc
        _ = (|ε| ^ n * |ε| ^ q) *
            (saddleDerivativeConstant b M n / ((n.factorial : ℝ) * (b / 4) ^ q)) *
              ∫ t : ℝ, saddleGaussianWeight B (N + 1) t := by ring
        _ = _ := by rw [hp]

def saddleLocalErrorConstant (b B M : ℝ) (N : ℕ) : ℝ :=
  (saddleDerivativeConstant b M (N + 1) / ((N + 1).factorial : ℝ) +
    ∑ n ∈ Finset.range (N + 1), saddleDerivativeConstant b M n /
      ((n.factorial : ℝ) * (b / 4) ^ (N + 1 - n))) *
    ∫ t : ℝ, saddleGaussianWeight B (N + 1) t

/-- Local Taylor integration for an actual holomorphic amplitude on the saddle
disk. Every omitted coefficient tail is bounded by a common Gaussian moment. -/
theorem norm_localSaddleIntegral_sub_taylor_le {A : ℂ → ℂ} {b B β M ε : ℝ}
    (hb : 0 < b) (hβ : β ∈ Icc b B) (hM : 0 ≤ M) (N : ℕ)
    (hA : AnalyticOnNhd ℂ A (Metric.closedBall (β : ℂ) (β / 2)))
    (hbound : ∀ w ∈ Metric.closedBall (β : ℂ) (β / 2), ‖A w‖ ≤ M)
    (hmeas : AEStronglyMeasurable
      (fun t : ℝ => rescaledSaddleIntegrand A β t (ε : ℂ))
      (volume.restrict (saddleLocalDomain b ε)))
    (hjet : ∀ n ≤ N, Integrable
      (fun t : ℝ => iteratedDeriv n (fun e : ℝ => rescaledSaddleIntegrand A β t (e : ℂ)) 0)) :
    IntegrableOn (fun t : ℝ => rescaledSaddleIntegrand A β t (ε : ℂ))
        (saddleLocalDomain b ε) ∧
      ‖(∫ t in saddleLocalDomain b ε, rescaledSaddleIntegrand A β t (ε : ℂ)) -
        Analytic.integralTaylorPolynomial volume
          (fun e t => rescaledSaddleIntegrand A β t (e : ℂ)) N ε‖ ≤
        saddleLocalErrorConstant b B M N * |ε| ^ (N + 1) := by
  have hβp : 0 < β := hb.trans_le hβ.1
  have hB : 0 < B := hβp.trans_le hβ.2
  let maj : ℝ → ℝ := fun t =>
    saddleDerivativeConstant b M (N + 1) * saddleGaussianWeight B (N + 1) t
  have himaj : Integrable maj :=
    (integrable_saddleGaussianWeight hB (N + 1)).const_mul _
  have hnmaj : ∀ᵐ t, 0 ≤ maj t := Eventually.of_forall fun t =>
    mul_nonneg (saddleDerivativeConstant_nonneg hb hM _) (saddleGaussianWeight_nonneg _ _ _)
  have hraw := Analytic.norm_setIntegral_sub_whole_taylor_le
    (measurableSet_saddleLocalDomain b ε) hmeas hjet himaj hnmaj
    (fun t ht e he => contDiffAt_rescaledSaddleIntegrand_real hβp
      ((abs_mul_le_of_mem_uIcc ht he).trans (by linarith [hβ.1])) hA (N + 1 : ℕ))
    (fun t ht e he => by
      simpa only [maj, saddleDerivativeConstant, saddleGaussianWeight, mul_assoc] using
        norm_iteratedDeriv_rescaledSaddleIntegrand_real_le_uniform hb hβ
          (abs_mul_le_of_mem_uIcc ht he) hA hbound (N + 1))
  refine ⟨hraw.1, hraw.2.trans ?_⟩
  have ht (n : ℕ) (hn : n ∈ Finset.range (N + 1)) :=
    saddle_tail_term_le (ε := ε) hb hB hM (N := N)
      (by simpa using Finset.mem_range.mp hn) (hjet n (by simpa using Finset.mem_range.mp hn))
      (fun t => by
        simpa only [saddleDerivativeConstant, saddleGaussianWeight, mul_assoc] using
          norm_iteratedDeriv_rescaledSaddleIntegrand_real_le_uniform hb hβ
            (t := t) (ε := 0) (by simp; positivity) hA hbound n)
  apply (add_le_add (le_refl _) (Finset.sum_le_sum ht)).trans
  apply le_of_eq
  simp only [maj, integral_const_mul, saddleLocalErrorConstant, Finset.sum_mul, add_mul]
  congr 1
  · ring
  · apply Finset.sum_congr rfl
    intro n hn
    ring

/-- The local expansion of the actual BTZ amplitude is uniform throughout a
compact positive energy-ratio interval. The coefficients are whole-line jets;
their explicit Gaussian values are proved in `SaddleJetIntegral`. -/
theorem uniform_localSaddleIntegral_taylor (φ : SmoothKernel) {L U : ℝ}
    (hL : 0 < L) (hLU : L ≤ U) (N : ℕ) :
    ∃ C > 0, ∀ x ∈ Icc L U, ∀ ε : ℝ,
      IntegrableOn
        (fun t : ℝ => rescaledSaddleIntegrand (complexAmplitude φ) (saddleBeta x) t (ε : ℂ))
        (saddleLocalDomain (saddleBeta U) ε) ∧
      ‖(∫ t in saddleLocalDomain (saddleBeta U) ε,
          rescaledSaddleIntegrand (complexAmplitude φ) (saddleBeta x) t (ε : ℂ)) -
        Analytic.integralTaylorPolynomial volume
          (fun e t => rescaledSaddleIntegrand (complexAmplitude φ) (saddleBeta x) t (e : ℂ)) N ε‖ ≤
        C * |ε| ^ (N + 1) := by
  have hU : 0 < U := hL.trans_le hLU
  have hb : 0 < saddleBeta U := saddleBeta_pos hU
  obtain ⟨M, hM, hbound⟩ := complexAmplitude_halfDisk_bounded φ
    (βlo := saddleBeta U) (βhi := saddleBeta L) hb
  let C := saddleLocalErrorConstant (saddleBeta U) (saddleBeta L) M N
  refine ⟨|C| + 1, by positivity, ?_⟩
  intro x hx ε
  have hxp : 0 < x := hL.trans_le hx.1
  have hβ := saddleBeta_mem_Icc hL hx
  have hlocal := norm_localSaddleIntegral_sub_taylor_le hb hβ hM.le N
    (analyticOnNhd_complexAmplitude_halfDisk φ (saddleBeta_pos hxp))
    (hbound (saddleBeta x) hβ)
    (continuous_rescaledSaddleIntegrand_real_coordinate φ (saddleBeta_pos hxp) ε).aestronglyMeasurable
    (fun n hn => integrable_rescaledSaddleIntegrand_real_jet φ hxp n)
  refine ⟨hlocal.1, hlocal.2.trans ?_⟩
  apply mul_le_mul_of_nonneg_right _ (pow_nonneg (abs_nonneg ε) _)
  exact (le_abs_self C).trans (by linarith)

end BTZEntropy
