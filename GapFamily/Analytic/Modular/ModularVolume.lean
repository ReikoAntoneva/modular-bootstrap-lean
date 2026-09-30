import Mathlib.Analysis.Complex.UpperHalfPlane.Measure
import Mathlib.NumberTheory.Modular
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Hyperbolic measure of the modular fundamental domain

The measure is mathlib's actual invariant volume `dx dy / y²`, restricted to
the standard closed modular fundamental domain.
-/

noncomputable section

namespace GapFamily.Analytic

open MeasureTheory Set
open scoped ENNReal NNReal

/-- The measure used by the modular Hilbert space. -/
def modularMeasure : Measure UpperHalfPlane :=
  (volume : Measure UpperHalfPlane).restrict ModularGroup.fd

theorem measurableSet_fd : MeasurableSet ModularGroup.fd :=
  ModularGroup.isClosed_fd.measurableSet

/-- A coarse positive height bound suffices for controlling the cusp integral. -/
theorem one_half_lt_im_of_mem_fd {τ : UpperHalfPlane} (hτ : τ ∈ ModularGroup.fd) :
    (1 : ℝ) / 2 < τ.im := by
  have hs := ModularGroup.three_le_four_mul_im_sq_of_mem_fd hτ
  have hp := τ.im_pos
  nlinarith

/-- The infinite vertical strip used in the cusp estimate. -/
def cuspStrip (h : ℝ) : Set UpperHalfPlane :=
  {τ | |τ.re| ≤ (1 : ℝ) / 2 ∧ h ≤ τ.im}

theorem fd_subset_cuspStrip : ModularGroup.fd ⊆ cuspStrip (1 / 2) := by
  intro τ hτ
  exact ⟨hτ.2, (one_half_lt_im_of_mem_fd hτ).le⟩

/-- The vertical tail of the exact hyperbolic density. -/
theorem vertical_cusp_integral (h : ℝ) (hh : 0 < h) :
    (∫⁻ y : ℝ in Ici h, ((1 / ‖y‖₊) ^ 2 : ℝ≥0)) = ENNReal.ofReal (1 / h) := by
  rw [← restrict_Ioi_eq_restrict_Ici]
  have heq : (∫⁻ y : ℝ in Ioi h, ((1 / ‖y‖₊) ^ 2 : ℝ≥0)) =
      ∫⁻ y : ℝ in Ioi h, ENNReal.ofReal (y ^ (-2 : ℝ)) := by
    apply setLIntegral_congr_fun measurableSet_Ioi
    intro y hy
    have hy0 : 0 ≤ y := (hh.trans hy).le
    dsimp only
    rw [Real.rpow_neg_ofNat, zpow_neg, zpow_ofNat]
    rw [← ENNReal.ofReal_coe_nnreal]
    congr 1
    simp [NNReal.coe_pow, Real.norm_eq_abs, abs_of_nonneg hy0, one_div, inv_pow]
  rw [heq, ← ofReal_integral_eq_lintegral_ofReal
    (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hh)]
  · rw [integral_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hh]
    congr 1
    norm_num [Real.rpow_neg_one, one_div]
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    exact Real.rpow_nonneg (hh.trans hy).le _

/-- Fubini evaluates a cusp strip against the density `dx dy / y²`. -/
theorem complex_cusp_integral (h : ℝ) (hh : 0 < h) :
    (∫⁻ z : ℂ in {z : ℂ | |z.re| ≤ 1 / 2 ∧ h ≤ z.im},
      ((1 / ‖z.im‖₊) ^ 2 : ℝ≥0)) = ENNReal.ofReal (1 / h) := by
  have hset : {z : ℂ | |z.re| ≤ 1 / 2 ∧ h ≤ z.im} =
      Complex.measurableEquivRealProd ⁻¹' (Icc (-1/2 : ℝ) (1/2) ×ˢ Ici h) := by
    ext z
    simp [abs_le, and_assoc, neg_div]
  rw [hset]
  trans (∫⁻ p : ℝ × ℝ in Icc (-1/2 : ℝ) (1/2) ×ˢ Ici h,
    (((1 / ‖p.2‖₊) ^ 2 : ℝ≥0) : ℝ≥0∞))
  · exact Complex.volume_preserving_equiv_real_prod.setLIntegral_comp_preimage_emb
      Complex.measurableEquivRealProd.measurableEmbedding
      (fun p : ℝ × ℝ => (((1 / ‖p.2‖₊) ^ 2 : ℝ≥0) : ℝ≥0∞)) _
  change (∫⁻ p : ℝ × ℝ in Icc (-1/2 : ℝ) (1/2) ×ˢ Ici h,
    (((1 / ‖p.2‖₊) ^ 2 : ℝ≥0) : ℝ≥0∞) ∂(volume.prod volume)) = _
  rw [setLIntegral_prod]
  · simp only [vertical_cusp_integral h hh, lintegral_const, Measure.restrict_apply_univ]
    norm_num [Real.volume_Icc]
  · fun_prop

/-- The full infinite cusp strip has finite hyperbolic volume, with exact tail bound. -/
theorem volume_cuspStrip (h : ℝ) (hh : 0 < h) :
    (volume : Measure UpperHalfPlane) (cuspStrip h) = ENNReal.ofReal (1 / h) := by
  rw [UpperHalfPlane.volume_eq_lintegral]
  have himage : UpperHalfPlane.coe '' cuspStrip h =
      {z : ℂ | |z.re| ≤ 1 / 2 ∧ h ≤ z.im} := by
    ext z
    constructor
    · rintro ⟨τ, hτ, rfl⟩
      exact hτ
    · intro hz
      exact ⟨⟨z, lt_of_lt_of_le hh hz.2⟩, hz, rfl⟩
  rw [himage, complex_cusp_integral h hh]

/-- A concrete finite upper bound for the modular fundamental domain. -/
theorem volume_fd_le_two : (volume : Measure UpperHalfPlane) ModularGroup.fd ≤ 2 := by
  calc
    _ ≤ (volume : Measure UpperHalfPlane) (cuspStrip (1 / 2)) :=
      measure_mono fd_subset_cuspStrip
    _ = 2 := by rw [volume_cuspStrip _ (by norm_num)]; norm_num

theorem volume_fd_lt_top : (volume : Measure UpperHalfPlane) ModularGroup.fd < ⊤ :=
  volume_fd_le_two.trans_lt (by norm_num)

instance instIsFiniteMeasureModularMeasure : IsFiniteMeasure modularMeasure := by
  constructor
  simpa [modularMeasure] using volume_fd_lt_top

/-- The open fundamental domain contains a point above the unit circle. -/
theorem fdo_nonempty : ModularGroup.fdo.Nonempty := by
  refine ⟨⟨⟨0, 2⟩, by norm_num⟩, ?_⟩
  norm_num [ModularGroup.fdo, Complex.normSq]

/-- The actual hyperbolic volume of the modular fundamental domain is positive. -/
theorem volume_fd_pos : 0 < (volume : Measure UpperHalfPlane) ModularGroup.fd := by
  have hopen : IsOpen (UpperHalfPlane.coe '' ModularGroup.fdo) :=
    UpperHalfPlane.isOpenEmbedding_coe.isOpenMap _ ModularGroup.isOpen_fdo
  have hpositive : 0 < (volume : Measure ℂ) (UpperHalfPlane.coe '' ModularGroup.fdo) :=
    hopen.measure_pos (volume : Measure ℂ) (fdo_nonempty.image _)
  have hsupport : UpperHalfPlane.coe '' ModularGroup.fdo ⊆
      Function.support (fun z : ℂ => (↑((1 / ‖z.im‖₊) ^ 2 : NNReal) : ENNReal)) := by
    rintro z ⟨τ, hτ, rfl⟩
    have hp := τ.im_pos
    simp only [Function.mem_support]
    simpa using hp.ne'
  have hvol : 0 < (volume : Measure UpperHalfPlane) ModularGroup.fdo := by
    rw [UpperHalfPlane.volume_eq_lintegral, setLIntegral_pos_iff (by fun_prop),
      inter_eq_right.mpr hsupport]
    exact hpositive
  exact hvol.trans_le (measure_mono ModularGroup.fdo_subset_fd)

theorem modularMeasure_univ_pos : 0 < modularMeasure univ := by
  simpa [modularMeasure] using volume_fd_pos

theorem modularMeasure_real_univ_pos : 0 < modularMeasure.real univ := by
  exact ENNReal.toReal_pos modularMeasure_univ_pos.ne' (measure_ne_top _ _)


open MeasureTheory Set Real
open scoped Interval

theorem arcsin_half : Real.arcsin (1 / 2) = Real.pi / 6 := by
  apply Real.arcsin_eq_of_sin_eq Real.sin_pi_div_six
  constructor <;> linarith [Real.pi_pos]

theorem modular_area_integrand_continuous :
    ContinuousOn (fun x : ℝ => 1 / Real.sqrt (1 - x ^ 2)) (Icc (-1 / 2) (1 / 2)) := by
  apply continuousOn_const.div ((continuousOn_const.sub (continuousOn_id.pow 2)).sqrt)
  intro x hx
  apply ne_of_gt
  apply Real.sqrt_pos.2
  dsimp
  nlinarith [mul_nonneg (sub_nonneg.mpr hx.2) (show 0 ≤ x + 1/2 by linarith [hx.1])]

theorem modular_area_interval_integral :
    (∫ x in (-1 / 2 : ℝ)..(1 / 2), 1 / Real.sqrt (1 - x ^ 2)) = Real.pi / 3 := by
  have hint : IntervalIntegrable (fun x : ℝ => 1 / Real.sqrt (1 - x ^ 2)) volume (-1 / 2) (1 / 2) := by
    apply ContinuousOn.intervalIntegrable
    simpa only [uIcc_of_le (by norm_num : (-1 / 2 : ℝ) ≤ 1 / 2)] using modular_area_integrand_continuous
  have heq := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := Real.arcsin) (f' := fun x : ℝ => 1 / Real.sqrt (1 - x ^ 2))
    (a := (-1 / 2 : ℝ)) (b := (1 / 2 : ℝ)) (fun x hx => by
      rw [uIcc_of_le (by norm_num : (-1 / 2 : ℝ) ≤ 1 / 2)] at hx
      exact Real.hasDerivAt_arcsin (by linarith [hx.1]) (by linarith [hx.2])) hint
  rw [heq]
  have hneg : Real.arcsin (-1 / 2) = -Real.arcsin (1 / 2) := by
    rw [neg_div, Real.arcsin_neg]
  rw [hneg, arcsin_half]
  ring


theorem modular_area_set_integral :
    (∫ x in Icc (-1 / 2 : ℝ) (1 / 2), 1 / Real.sqrt (1 - x ^ 2)) = Real.pi / 3 := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num : (-1 / 2 : ℝ) ≤ 1 / 2)]
  exact modular_area_interval_integral

theorem modular_area_lintegral :
    (∫⁻ x in Icc (-1 / 2 : ℝ) (1 / 2), ENNReal.ofReal (1 / Real.sqrt (1 - x ^ 2))) =
      ENNReal.ofReal (Real.pi / 3) := by
  rw [← ofReal_integral_eq_lintegral_ofReal
    (modular_area_integrand_continuous.integrableOn_Icc)]
  · rw [modular_area_set_integral]
  · exact Filter.Eventually.of_forall fun x => by positivity


open MeasureTheory Set Real
open scoped ENNReal NNReal

theorem modular_lower_height_pos {x : ℝ} (hx : x ∈ Icc (-1 / 2 : ℝ) (1 / 2)) :
    0 < Real.sqrt (1 - x ^ 2) := by
  apply Real.sqrt_pos.2
  nlinarith [mul_nonneg (sub_nonneg.mpr hx.2) (show 0 ≤ x + 1/2 by linarith [hx.1])]

theorem modular_fd_image :
    (UpperHalfPlane.coe '' ModularGroup.fd) =
      {z : ℂ | z.re ∈ Icc (-1 / 2 : ℝ) (1 / 2) ∧ Real.sqrt (1 - z.re ^ 2) ≤ z.im} := by
  ext z
  constructor
  · rintro ⟨τ, hτ, rfl⟩
    have hx : τ.re ∈ Icc (-1 / 2 : ℝ) (1 / 2) := by
      simpa only [Set.mem_Icc, neg_div] using abs_le.mp hτ.2
    refine ⟨hx, Real.sqrt_le_iff.mpr ⟨τ.im_pos.le, ?_⟩⟩
    have hn := hτ.1
    rw [Complex.normSq_apply] at hn
    dsimp at hn ⊢
    nlinarith
  · rintro ⟨hx, hy⟩
    have hpos : 0 < z.im := lt_of_lt_of_le (modular_lower_height_pos hx) hy
    refine ⟨⟨z, hpos⟩, ?_, rfl⟩
    constructor
    · change 1 ≤ Complex.normSq z
      rw [Complex.normSq_apply]
      have hh := (Real.sqrt_le_iff.mp hy).2
      nlinarith
    · change |z.re| ≤ 1 / 2
      exact abs_le.mpr ⟨by simpa only [neg_div] using hx.1, hx.2⟩

theorem modular_fd_preimage :
    Complex.equivRealProd.symm ⁻¹' (UpperHalfPlane.coe '' ModularGroup.fd) =
      {p : ℝ × ℝ | p.1 ∈ Icc (-1 / 2 : ℝ) (1 / 2) ∧ Real.sqrt (1 - p.1 ^ 2) ≤ p.2} := by
  rw [modular_fd_image]
  rfl



theorem modular_area_product_integral :
    (∫⁻ p : ℝ × ℝ in {p : ℝ × ℝ | p.1 ∈ Icc (-1 / 2 : ℝ) (1 / 2) ∧
      Real.sqrt (1 - p.1 ^ 2) ≤ p.2}, (((1 / ‖p.2‖₊) ^ 2 : ℝ≥0) : ℝ≥0∞)) =
      ENNReal.ofReal (Real.pi / 3) := by
  let s : Set (ℝ × ℝ) := {p | p.1 ∈ Icc (-1 / 2 : ℝ) (1 / 2) ∧
    Real.sqrt (1 - p.1 ^ 2) ≤ p.2}
  have hs : MeasurableSet s := by
    exact (measurableSet_Icc.preimage measurable_fst).inter
      (measurableSet_le (by fun_prop) measurable_snd)
  change (∫⁻ p in s, (((1 / ‖p.2‖₊) ^ 2 : ℝ≥0) : ℝ≥0∞)) = _
  rw [← lintegral_indicator hs]
  change (∫⁻ p, s.indicator (fun p : ℝ × ℝ => (((1 / ‖p.2‖₊) ^ 2 : ℝ≥0) : ℝ≥0∞)) p
    ∂(volume.prod volume)) = _
  rw [lintegral_prod]
  · calc
      _ = ∫⁻ x in Icc (-1 / 2 : ℝ) (1 / 2), ENNReal.ofReal (1 / Real.sqrt (1 - x ^ 2)) := by
        rw [← lintegral_indicator measurableSet_Icc]
        apply lintegral_congr
        intro x
        by_cases hx : x ∈ Icc (-1 / 2 : ℝ) (1 / 2)
        · rw [Set.indicator_of_mem hx]
          have heq : (fun y => s.indicator (fun p : ℝ × ℝ =>
              (((1 / ‖p.2‖₊) ^ 2 : ℝ≥0) : ℝ≥0∞)) (x, y)) =
              (Ici (Real.sqrt (1 - x ^ 2))).indicator
                (fun y : ℝ => (((1 / ‖y‖₊) ^ 2 : ℝ≥0) : ℝ≥0∞)) := by
            funext y
            simp only [s, Set.indicator, Set.mem_ofPred_eq, hx, true_and, Set.mem_Ici]
          rw [heq, lintegral_indicator measurableSet_Ici,
            vertical_cusp_integral _ (modular_lower_height_pos hx)]
        · simp only [s, Set.indicator, Set.mem_ofPred_eq, hx, false_and, ite_false, lintegral_zero]
      _ = _ := modular_area_lintegral
  · exact (by fun_prop : Measurable (fun p : ℝ × ℝ =>
      (((1 / ‖p.2‖₊) ^ 2 : ℝ≥0) : ℝ≥0∞))).indicator hs |>.aemeasurable

theorem volume_fd_eq_pi_div_three :
    (volume : Measure UpperHalfPlane) ModularGroup.fd = ENNReal.ofReal (Real.pi / 3) := by
  rw [UpperHalfPlane.volume_eq_lintegral]
  trans (∫⁻ p : ℝ × ℝ in Complex.measurableEquivRealProd.symm ⁻¹'
      (UpperHalfPlane.coe '' ModularGroup.fd),
      (((1 / ‖p.2‖₊) ^ 2 : ℝ≥0) : ℝ≥0∞))
  · exact ((MeasurePreserving.symm Complex.measurableEquivRealProd
      Complex.volume_preserving_equiv_real_prod).setLIntegral_comp_preimage_emb
      Complex.measurableEquivRealProd.symm.measurableEmbedding
      (fun z : ℂ => (((1 / ‖z.im‖₊) ^ 2 : ℝ≥0) : ℝ≥0∞)) _).symm
  change (∫⁻ p : ℝ × ℝ in Complex.equivRealProd.symm ⁻¹'
      (UpperHalfPlane.coe '' ModularGroup.fd),
      (((1 / ‖p.2‖₊) ^ 2 : ℝ≥0) : ℝ≥0∞)) = _
  rw [modular_fd_preimage]
  exact modular_area_product_integral

/-- The total mass of the actual restricted modular measure. -/
theorem modularMeasure_univ : modularMeasure univ = ENNReal.ofReal (Real.pi / 3) := by
  simpa [modularMeasure] using volume_fd_eq_pi_div_three

/-- The real-valued area used to normalize the constant spectral vector. -/
theorem modularMeasure_real_univ : modularMeasure.real univ = Real.pi / 3 := by
  rw [Measure.real, modularMeasure_univ, ENNReal.toReal_ofReal (by positivity)]

/-- The target constant spatial term after normalization by the actual modular area. -/
theorem constant_spectral_normalization :
    (-2 * Real.pi) / modularMeasure.real univ = -6 := by
  rw [modularMeasure_real_univ]
  field_simp
  norm_num


end GapFamily.Analytic
