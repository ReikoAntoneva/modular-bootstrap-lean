import GapFamily.Analytic.Spatial.SpatialDiskTail
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

noncomputable section

namespace GapFamily.Analytic.SpatialPoint

open Set Filter MeasureTheory Metric
open scoped Topology

theorem spatialDiskDensity_nonneg {ζ : ℂ} (hζ : ζ ∈ ball 0 1) (s : ℝ) :
    0 ≤ spatialDiskDensity s ζ := by
  have hζ' : ‖ζ‖ < 1 := by simpa using hζ
  apply Real.rpow_nonneg
  nlinarith [norm_nonneg ζ]

def spatialDiskWeight (s : ℝ) (ζ : ℂ) : ℝ :=
  ((s - 1) / Real.pi) * spatialDiskDensity s ζ

theorem spatialDiskWeight_nonneg {s : ℝ} (hs : 1 < s) {ζ : ℂ}
    (hζ : ζ ∈ ball 0 1) : 0 ≤ spatialDiskWeight s ζ :=
  mul_nonneg (div_nonneg (sub_nonneg.mpr hs.le) Real.pi_pos.le)
    (spatialDiskDensity_nonneg hζ s)

theorem integrableOn_spatialDiskWeight {s : ℝ} (hs : 1 < s) :
    IntegrableOn (spatialDiskWeight s) (ball (0 : ℂ) 1) :=
  (integrableOn_spatialDiskDensity hs).const_mul _

theorem integral_spatialDiskWeight {s : ℝ} (hs : 1 < s) :
    (∫ ζ : ℂ in ball 0 1, spatialDiskWeight s ζ) = 1 := by
  unfold spatialDiskWeight
  rw [integral_const_mul, integral_spatialDiskDensity hs]
  field_simp [Real.pi_ne_zero, ne_of_gt (sub_pos.mpr hs)]

theorem integrableOn_spatialDiskWeight_mul {s : ℝ} (hs : 1 < s) {F : ℂ → ℂ}
    (hF : AEStronglyMeasurable F (volume.restrict (ball 0 1)))
    {M : ℝ} (hM : ∀ ζ ∈ ball (0 : ℂ) 1, ‖F ζ‖ ≤ M) :
    IntegrableOn (fun ζ : ℂ => (spatialDiskWeight s ζ : ℂ) * F ζ) (ball 0 1) := by
  apply (integrableOn_spatialDiskWeight hs).ofReal.mul_bdd hF
  filter_upwards [ae_restrict_mem measurableSet_ball] with ζ hζ using hM ζ hζ

theorem integrableOn_spatialDiskDensity_mul {s : ℝ} (hs : 1 < s) {F : ℂ → ℂ}
    (hF : AEStronglyMeasurable F (volume.restrict (ball 0 1)))
    {M : ℝ} (hM : ∀ ζ ∈ ball (0 : ℂ) 1, ‖F ζ‖ ≤ M) :
    IntegrableOn (fun ζ : ℂ => (spatialDiskDensity s ζ : ℂ) * F ζ) (ball 0 1) := by
  apply (integrableOn_spatialDiskDensity hs).ofReal.mul_bdd hF
  filter_upwards [ae_restrict_mem measurableSet_ball] with ζ hζ using hM ζ hζ

theorem normalized_spatialDiskDensity_integral_eq (s : ℝ) (F : ℂ → ℂ) :
    ((s - 1) / Real.pi : ℝ) •
      (∫ ζ : ℂ in ball 0 1, (spatialDiskDensity s ζ : ℂ) * F ζ) =
    ∫ ζ : ℂ in ball 0 1, (spatialDiskWeight s ζ : ℂ) * F ζ := by
  rw [← integral_smul]
  congr 1
  funext ζ
  simp only [spatialDiskWeight, Complex.ofReal_mul, Complex.real_smul, mul_assoc]

theorem spatialDiskWeight_error_identity {s : ℝ} (hs : 1 < s) {F : ℂ → ℂ}
    (hF : AEStronglyMeasurable F (volume.restrict (ball 0 1)))
    {M : ℝ} (hM : ∀ ζ ∈ ball (0 : ℂ) 1, ‖F ζ‖ ≤ M) :
    (∫ ζ : ℂ in ball 0 1, (spatialDiskWeight s ζ : ℂ) * F ζ) - F 0 =
      ∫ ζ : ℂ in ball 0 1, (spatialDiskWeight s ζ : ℂ) * (F ζ - F 0) := by
  simp_rw [mul_sub]
  have hc : IntegrableOn (fun ζ : ℂ => (spatialDiskWeight s ζ : ℂ) * F 0)
      (ball 0 1) := (integrableOn_spatialDiskWeight hs).ofReal.mul_const (F 0)
  rw [integral_sub (integrableOn_spatialDiskWeight_mul hs hF hM)
    hc, integral_mul_const,
    integral_complex_ofReal, integral_spatialDiskWeight hs, Complex.ofReal_one, one_mul]

theorem norm_spatialDiskWeight_error_le {s r ε M : ℝ} (hs : 1 < s)
    (hr : r ≤ 1) (hε : 0 ≤ ε) {F : ℂ → ℂ}
    (hF : AEStronglyMeasurable F (volume.restrict (ball 0 1)))
    (hM : ∀ ζ ∈ ball (0 : ℂ) 1, ‖F ζ‖ ≤ M)
    (hsmall : ∀ ζ ∈ ball (0 : ℂ) r, ‖F ζ - F 0‖ ≤ ε) :
    ‖(∫ ζ : ℂ in ball 0 1, (spatialDiskWeight s ζ : ℂ) * F ζ) - F 0‖ ≤
      ε + 2 * M * ∫ ζ : ℂ in ball 0 1 \ ball 0 r, spatialDiskWeight s ζ := by
  have hsub : ball (0 : ℂ) r ⊆ ball 0 1 := ball_subset_ball hr
  have hF0 : ‖F 0‖ ≤ M := hM 0 (mem_ball_self zero_lt_one)
  have hdiff : ∀ ζ ∈ ball (0 : ℂ) 1, ‖F ζ - F 0‖ ≤ 2 * M := by
    intro ζ hζ
    exact (norm_sub_le _ _).trans (by linarith [hM ζ hζ])
  have hw := integrableOn_spatialDiskWeight hs
  have hi : IntegrableOn (fun ζ : ℂ => (spatialDiskWeight s ζ : ℂ) * (F ζ - F 0))
      (ball 0 1) :=
    integrableOn_spatialDiskWeight_mul hs (hF.sub aestronglyMeasurable_const) hdiff
  have hn : ∀ ζ ∈ ball (0 : ℂ) 1,
      ‖(spatialDiskWeight s ζ : ℂ) * (F ζ - F 0)‖ =
        spatialDiskWeight s ζ * ‖F ζ - F 0‖ := by
    intro ζ hζ
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (spatialDiskWeight_nonneg hs hζ)]
  have hnear : ‖∫ ζ : ℂ in ball 0 r,
      (spatialDiskWeight s ζ : ℂ) * (F ζ - F 0)‖ ≤ ε := by
    calc
      _ ≤ ∫ ζ : ℂ in ball 0 r, ε * spatialDiskWeight s ζ := by
        apply norm_integral_le_of_norm_le ((hw.mono_set hsub).const_mul ε)
        filter_upwards [ae_restrict_mem measurableSet_ball] with ζ hζ
        rw [hn ζ (hsub hζ), mul_comm ε]
        exact mul_le_mul_of_nonneg_left (hsmall ζ hζ) (spatialDiskWeight_nonneg hs (hsub hζ))
      _ ≤ ∫ ζ : ℂ in ball 0 1, ε * spatialDiskWeight s ζ := by
        apply setIntegral_mono_set (hw.const_mul ε)
        · filter_upwards [ae_restrict_mem measurableSet_ball] with ζ hζ
          exact mul_nonneg hε (spatialDiskWeight_nonneg hs hζ)
        · exact Filter.Eventually.of_forall hsub
      _ = ε := by rw [integral_const_mul, integral_spatialDiskWeight hs, mul_one]
  have hfar : ‖∫ ζ : ℂ in ball 0 1 \ ball 0 r,
      (spatialDiskWeight s ζ : ℂ) * (F ζ - F 0)‖ ≤
      2 * M * ∫ ζ : ℂ in ball 0 1 \ ball 0 r, spatialDiskWeight s ζ := by
    rw [← integral_const_mul]
    apply norm_integral_le_of_norm_le ((hw.mono_set sdiff_subset).const_mul (2 * M))
    filter_upwards [ae_restrict_mem (measurableSet_ball.diff measurableSet_ball)] with ζ hζ
    rw [hn ζ hζ.1, mul_comm (2 * M)]
    exact mul_le_mul_of_nonneg_left (hdiff ζ hζ.1) (spatialDiskWeight_nonneg hs hζ.1)
  rw [spatialDiskWeight_error_identity hs hF hM,
    ← integral_inter_add_sdiff measurableSet_ball hi, inter_eq_right.mpr hsub]
  exact (norm_add_le _ _).trans (add_le_add hnear hfar)

private theorem tendsto_spatialDiskWeight_average_of_tail {F : ℂ → ℂ}
    (hF : AEStronglyMeasurable F (volume.restrict (ball 0 1)))
    (hcont : ContinuousAt F 0)
    (hbound : ∃ M : ℝ, 0 ≤ M ∧ ∀ ζ ∈ ball (0 : ℂ) 1, ‖F ζ‖ ≤ M)
    (htail : ∀ r : ℝ, 0 < r → r < 1 →
      Tendsto (fun s : ℝ => ∫ ζ : ℂ in ball 0 1 \ ball 0 r, spatialDiskWeight s ζ)
        atTop (𝓝 0)) :
    Tendsto (fun s : ℝ => ∫ ζ : ℂ in ball 0 1,
      (spatialDiskWeight s ζ : ℂ) * F ζ) atTop (𝓝 (F 0)) := by
  rcases hbound with ⟨M, hM0, hM⟩
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hhalf : 0 < ε / 2 := half_pos hε
  rcases Metric.continuousAt_iff.mp hcont (ε / 2) hhalf with ⟨δ, hδ, hclose⟩
  let r : ℝ := min (δ / 2) (1 / 2)
  have hr0 : 0 < r := lt_min (half_pos hδ) (by norm_num)
  have hr1 : r < 1 := (min_le_right _ _).trans_lt (by norm_num)
  have hrd : r < δ := (min_le_left _ _).trans_lt (half_lt_self hδ)
  have hsmall : ∀ ζ ∈ ball (0 : ℂ) r, ‖F ζ - F 0‖ ≤ ε / 2 := by
    intro ζ hζ
    simpa only [dist_eq_norm] using (hclose (Metric.mem_ball.mp hζ |>.trans hrd)).le
  have ht : Tendsto (fun s : ℝ =>
      2 * M * ∫ ζ : ℂ in ball 0 1 \ ball 0 r, spatialDiskWeight s ζ) atTop (𝓝 0) := by
    simpa using (htail r hr0 hr1).const_mul (2 * M)
  filter_upwards [eventually_gt_atTop (1 : ℝ), (tendsto_order.mp ht).2 (ε / 2) hhalf]
    with s hs htail_s
  rw [dist_eq_norm]
  exact (norm_spatialDiskWeight_error_le hs hr1.le hhalf.le hF hM hsmall).trans_lt
    (by linarith)

theorem tendsto_spatialDiskTailPower {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    Tendsto (fun s : ℝ => (1 - r ^ 2) ^ (s - 1)) atTop (𝓝 0) := by
  apply (tendsto_rpow_atTop_of_base_lt_one (1 - r ^ 2)
    (by nlinarith) (by nlinarith [sq_pos_of_pos hr])).comp
  simpa only [sub_eq_add_neg, id_eq] using
    tendsto_atTop_add_const_right atTop (-1 : ℝ) tendsto_id

theorem tendsto_spatialDiskWeight_tail {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    Tendsto (fun s : ℝ => ∫ ζ : ℂ in ball 0 1 \ ball 0 r, spatialDiskWeight s ζ)
      atTop (𝓝 0) := by
  apply (tendsto_spatialDiskTailPower hr hr1).congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with s hs
  exact (integral_normalizedSpatialDiskDensity_annulus hs hr hr1).symm

theorem tendsto_normalized_spatialDiskDensity_integral {F : ℂ → ℂ}
    (hF : AEStronglyMeasurable F (volume.restrict (ball 0 1)))
    (hcont : ContinuousAt F 0)
    (hbound : ∃ M : ℝ, 0 ≤ M ∧ ∀ ζ ∈ ball (0 : ℂ) 1, ‖F ζ‖ ≤ M) :
    Tendsto (fun s : ℝ => ((s - 1) / Real.pi : ℝ) •
      (∫ ζ : ℂ in ball 0 1, (spatialDiskDensity s ζ : ℂ) * F ζ))
      atTop (𝓝 (F 0)) := by
  simp_rw [normalized_spatialDiskDensity_integral_eq]
  exact tendsto_spatialDiskWeight_average_of_tail hF hcont hbound
    (fun _ hr hr1 => tendsto_spatialDiskWeight_tail hr hr1)

end GapFamily.Analytic.SpatialPoint
