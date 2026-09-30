import GapFamily.Analytic.Elliptic.RectangleTrace
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Topology.MetricSpace.Cauchy

/-! # Fixed-rectangle point bounds and uniform Cauchy convergence -/

noncomputable section
namespace GapFamily.Analytic.RectangleTrace

open Set MeasureTheory Filter

def energy (F : ℝ × ℝ → ℂ) (a b c d : ℝ) : ℝ :=
  ∫ x in a..b, ∫ y in c..d, ‖F (x,y)‖^2

theorem energy_nonneg (F : ℝ × ℝ → ℂ) {a b c d : ℝ}
    (hab : a ≤ b) (hcd : c ≤ d) : 0 ≤ energy F a b c d :=
  intervalIntegral.integral_nonneg hab (fun _ _ =>
    intervalIntegral.integral_nonneg hcd (fun _ _ => sq_nonneg _))

/-- Actual ordinary energy increases when a compact rectangle is enlarged. -/
theorem energy_mono {F : ℝ × ℝ → ℂ} (hF : Continuous F)
    {a b c d A B C D : ℝ} (hAa : A ≤ a) (hab : a ≤ b) (hbB : b ≤ B)
    (hCc : C ≤ c) (hcd : c ≤ d) (hdD : d ≤ D) :
    energy F a b c d ≤ energy F A B C D := by
  have hCD := hCc.trans (hcd.trans hdD)
  have hs := continuous_integral_right (hF.norm.pow 2) hcd
  have hl := continuous_integral_right (hF.norm.pow 2) hCD
  simp only [Pi.pow_apply] at hs hl
  calc
    energy F a b c d ≤ ∫ x in a..b, ∫ y in C..D, ‖F (x,y)‖^2 := by
      apply intervalIntegral.integral_mono_on (μ := volume) hab
        (hs.intervalIntegrable a b) (hl.intervalIntegrable a b)
      intro x _
      exact intervalIntegral.integral_mono_interval hCc hcd hdD
        (Eventually.of_forall fun _ => sq_nonneg _)
        (((hF.comp (continuous_const.prodMk continuous_id)).norm.pow 2).intervalIntegrable C D)
    _ ≤ energy F A B C D :=
      intervalIntegral.integral_mono_interval hAa hab hbB
        (Eventually.of_forall fun _ =>
          intervalIntegral.integral_nonneg hCD (fun _ _ => sq_nonneg _))
        (hl.intervalIntegrable A B)

def fourEnergy (F : ℝ × ℝ → ℂ) (a b c d : ℝ) : ℝ :=
  energy F a b c d + energy (dx F) a b c d +
    energy (dy F) a b c d + energy (dxy F) a b c d

def pointConstant (h k : ℝ) : ℝ := 4/(h*k) + 4*h/k + 4*k/h + 4*h*k

theorem pointConstant_pos {h k : ℝ} (hh : 0 < h) (hk : 0 < k) :
    0 < pointConstant h k := by unfold pointConstant; positivity

/-- A single fixed ambient rectangle controls every point admitting forward
intervals of fixed positive widths inside it. -/
theorem point_sq_le_fixed_rectangle (F : ℝ × ℝ → ℂ) (hF : ContDiff ℝ 2 F)
    {A B C D h k : ℝ} (hh : 0 < h) (hk : 0 < k) {p : ℝ × ℝ}
    (hp : p ∈ Icc A (B-h) ×ˢ Icc C (D-k)) :
    ‖F p‖^2 ≤ (4/(h*k))*energy F A B C D +
      (4*h/k)*energy (dx F) A B C D +
      (4*k/h)*energy (dy F) A B C D +
      (4*h*k)*energy (dxy F) A B C D := by
  have hh' : p.1 < p.1 + h := by linarith
  have hk' : p.2 < p.2 + k := by linarith
  have hB : p.1 + h ≤ B := by linarith [hp.1.2]
  have hD : p.2 + k ≤ D := by linarith [hp.2.2]
  have hdx : ContDiff ℝ 1 (dx F) :=
    (hF.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  have hdy : Continuous (dy F) :=
    (hF.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hdxy : Continuous (dxy F) :=
    (hdx.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have ht := left_point_sq_le F hF hh' hk'
  simp only [add_sub_cancel_left] at ht
  apply ht.trans
  exact add_le_add
    (add_le_add
      (add_le_add
        (mul_le_mul_of_nonneg_left (energy_mono hF.continuous hp.1.1 hh'.le hB hp.2.1 hk'.le hD)
          (by positivity))
        (mul_le_mul_of_nonneg_left (energy_mono hdx.continuous hp.1.1 hh'.le hB hp.2.1 hk'.le hD)
          (by positivity)))
      (mul_le_mul_of_nonneg_left (energy_mono hdy hp.1.1 hh'.le hB hp.2.1 hk'.le hD)
        (by positivity)))
    (mul_le_mul_of_nonneg_left (energy_mono hdxy hp.1.1 hh'.le hB hp.2.1 hk'.le hD)
      (by positivity))

/-- A convenient single constant multiplying the sum of the four actual
energies, uniform on the fixed inner rectangle. -/
theorem point_sq_le_fourEnergy (F : ℝ × ℝ → ℂ) (hF : ContDiff ℝ 2 F)
    {A B C D h k : ℝ} (hh : 0 < h) (hk : 0 < k) {p : ℝ × ℝ}
    (hp : p ∈ Icc A (B-h) ×ˢ Icc C (D-k)) :
    ‖F p‖^2 ≤ pointConstant h k * fourEnergy F A B C D := by
  have hAB : A ≤ B := by linarith [hp.1.1, hp.1.2]
  have hCD : C ≤ D := by linarith [hp.2.1, hp.2.2]
  have h0 := energy_nonneg F hAB hCD
  have hx := energy_nonneg (dx F) hAB hCD
  have hy := energy_nonneg (dy F) hAB hCD
  have hxy := energy_nonneg (dxy F) hAB hCD
  have h0s : energy F A B C D ≤ fourEnergy F A B C D := by unfold fourEnergy; linarith
  have hxs : energy (dx F) A B C D ≤ fourEnergy F A B C D := by unfold fourEnergy; linarith
  have hys : energy (dy F) A B C D ≤ fourEnergy F A B C D := by unfold fourEnergy; linarith
  have hxys : energy (dxy F) A B C D ≤ fourEnergy F A B C D := by unfold fourEnergy; linarith
  apply (point_sq_le_fixed_rectangle F hF hh hk hp).trans
  calc
    _ ≤ (4/(h*k))*fourEnergy F A B C D + (4*h/k)*fourEnergy F A B C D +
        (4*k/h)*fourEnergy F A B C D + (4*h*k)*fourEnergy F A B C D :=
      add_le_add (add_le_add (add_le_add
        (mul_le_mul_of_nonneg_left h0s (by positivity))
        (mul_le_mul_of_nonneg_left hxs (by positivity)))
        (mul_le_mul_of_nonneg_left hys (by positivity)))
        (mul_le_mul_of_nonneg_left hxys (by positivity))
    _ = _ := by unfold pointConstant; ring

/-- Cauchy convergence of the four ordinary squared energies of actual smooth
differences gives uniform Cauchy convergence on the fixed inner rectangle. -/
theorem uniformCauchySeqOn_of_fourEnergy
    (F : ℕ → ℝ × ℝ → ℂ) (hF : ∀ n, ContDiff ℝ 2 (F n))
    {A B C D h k : ℝ} (hh : 0 < h) (hk : 0 < k)
    (hE : ∀ ε > (0 : ℝ), ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N,
      fourEnergy (F m - F n) A B C D < ε) :
    UniformCauchySeqOn F atTop (Icc A (B-h) ×ˢ Icc C (D-k)) := by
  apply Metric.uniformCauchySeqOn_iff.mpr
  intro ε hε
  have hK := pointConstant_pos hh hk
  obtain ⟨N, hN⟩ := hE (ε^2 / pointConstant h k) (div_pos (sq_pos_of_pos hε) hK)
  refine ⟨N, fun m hm n hn p hp => ?_⟩
  have hpbound := point_sq_le_fourEnergy (F m - F n) ((hF m).sub (hF n)) hh hk hp
  have he := mul_lt_mul_of_pos_left (hN m hm n hn) hK
  have hs : ‖(F m - F n) p‖^2 < ε^2 := hpbound.trans_lt (by
    simpa only [mul_div_cancel₀ _ hK.ne'] using he)
  rw [dist_eq_norm]
  exact (sq_lt_sq₀ (norm_nonneg _) hε.le).mp hs

end GapFamily.Analytic.RectangleTrace
