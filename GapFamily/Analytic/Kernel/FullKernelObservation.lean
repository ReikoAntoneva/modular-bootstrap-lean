import GapFamily.Analytic.Kernel.FullKernelResponse
import GapFamily.Analytic.Kernel.FullKernelBandExtension
import GapFamily.Construction.CellCoordinateIntegral

/-!
# Exterior observation of the actual holomorphic response

On the fixed interval `sqrt 2 < t < sqrt 3`, the physical energy
`|j| + b t²` belongs to the exterior of the input band and to the output
band of width `4 b`. Its exact Jacobian against the physical reference
measure is bounded below by `1/2`, uniformly for `|j| ≤ b`.
-/

noncomputable section

open MeasureTheory Real Set

namespace GapFamily.Analytic

/-- The physical output energy used for the fixed observation interval. -/
def observationEnergy (j : ℤ) (b t : ℝ) : ℝ := |(j : ℝ)| + b * t ^ 2

theorem observationEnergy_mem (j : ℤ) {b t : ℝ} (hb : 0 < b)
    (hj : |(j : ℝ)| ≤ b) (ht : t ∈ Ioo (sqrt 2) (sqrt 3)) :
    b < observationEnergy j b t ∧ observationEnergy j b t ∈ Ioo |(j : ℝ)| (4 * b) := by
  have ht0 : 0 ≤ t := (sqrt_nonneg 2).trans ht.1.le
  have ht2 : (2 : ℝ) < t ^ 2 := by
    nlinarith [sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),
      (sq_lt_sq₀ (sqrt_nonneg 2) ht0).mpr ht.1]
  have ht3 : t ^ 2 < (3 : ℝ) := by
    nlinarith [sq_sqrt (by norm_num : (0 : ℝ) ≤ 3),
      (sq_lt_sq₀ ht0 (sqrt_nonneg 3)).mpr ht.2]
  unfold observationEnergy
  have h2 := mul_lt_mul_of_pos_left ht2 hb
  have h3 := mul_lt_mul_of_pos_left ht3 hb
  have := abs_nonneg (j : ℝ)
  constructor
  · nlinarith
  · constructor <;> nlinarith

theorem observationEnergy_hasDerivAt (j : ℤ) (b t : ℝ) :
    HasDerivAt (observationEnergy j b) (2 * b * t) t := by
  change HasDerivAt (fun x : ℝ => |(j : ℝ)| + b * x ^ 2) (2 * b * t) t
  convert (((hasDerivAt_id t).pow 2).const_mul b).const_add |(j : ℝ)| using 1 <;>
    simp <;> ring

theorem observationEnergy_monotoneOn (j : ℤ) {b : ℝ} (hb : 0 ≤ b) :
    MonotoneOn (observationEnergy j b) (Ioo (sqrt 2) (sqrt 3)) := by
  intro t ht u hu htu
  have ht0 : 0 ≤ t := (sqrt_nonneg 2).trans ht.1.le
  have hu0 : 0 ≤ u := (sqrt_nonneg 2).trans hu.1.le
  exact add_le_add_right (mul_le_mul_of_nonneg_left ((sq_le_sq₀ ht0 hu0).mpr htu) hb) _

/-- The physical Jacobian dominates one half of ordinary coordinate measure. -/
theorem observationEnergy_jacobian_lower (j : ℤ) {b t : ℝ} (hb : 0 < b)
    (hj : |(j : ℝ)| ≤ b) (ht : t ∈ Ioo (sqrt 2) (sqrt 3)) :
    (1 : ℝ) ≤ 2 * ((2 * b * t) * referenceDensity j (observationEnergy j b t)) := by
  have ht1 : 1 ≤ t := by
    have : (1 : ℝ) ≤ sqrt 2 := by
      exact (le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
    exact this.trans ht.1.le
  obtain ⟨_, he⟩ := observationEnergy_mem j hb hj ht
  have he0 : 0 ≤ observationEnergy j b t := (abs_nonneg _).trans he.1.le
  have hrad : 0 < observationEnergy j b t ^ 2 - (j : ℝ) ^ 2 := by
    have hs := (sq_lt_sq₀ (abs_nonneg (j : ℝ)) he0).mpr he.1
    rw [sq_abs] at hs
    linarith
  have hspos : 0 < sqrt (observationEnergy j b t ^ 2 - (j : ℝ) ^ 2) := sqrt_pos.mpr hrad
  have hsle : sqrt (observationEnergy j b t ^ 2 - (j : ℝ) ^ 2) ≤ 4 * b := by
    calc
      _ ≤ sqrt (observationEnergy j b t ^ 2) := sqrt_le_sqrt (by nlinarith [sq_nonneg (j : ℝ)])
      _ = observationEnergy j b t := sqrt_sq he0
      _ ≤ 4 * b := he.2.le
  rw [referenceDensity, mul_one_div, ← mul_div_assoc]
  apply (le_div_iff₀ hspos).mpr
  have hbt : b ≤ b * t := le_mul_of_one_le_right hb.le ht1
  nlinarith

/-- The genuine coordinate integral is bounded by the ordinary physical
integral on the enlarged output band. Both integrability premises are explicit. -/
theorem integral_observation_le_reference_exterior (j : ℤ) {b : ℝ} (hb : 0 < b)
    (hj : |(j : ℝ)| ≤ b) (q : ℝ → ℝ) (hq0 : ∀ e, 0 ≤ q e)
    (hq : IntegrableOn q (Ioo b (4 * b)) (referenceMeasure j))
    (hcomp : IntegrableOn (fun t => q (observationEnergy j b t)) (Ioo (sqrt 2) (sqrt 3))) :
    (∫ t in Ioo (sqrt 2) (sqrt 3), q (observationEnergy j b t)) ≤
      2 * ∫ e in Ioo b (4 * b), q e ∂referenceMeasure j := by
  have hsub : observationEnergy j b '' Ioo (sqrt 2) (sqrt 3) ⊆
      Ioo b (4 * b) := by
    rintro e ⟨t, ht, rfl⟩
    exact ⟨(observationEnergy_mem j hb hj ht).1, (observationEnergy_mem j hb hj ht).2.2⟩
  have hw : IntegrableOn (fun e => referenceDensity j e * q e)
      (Ioo b (4 * b)) :=
    (GapFamily.Construction.integrableOn_referenceMeasure_Ioo_iff j hj q).1 hq
  have hderiv : ∀ t ∈ Ioo (sqrt 2) (sqrt 3), HasDerivWithinAt
      (observationEnergy j b) (2 * b * t) (Ioo (sqrt 2) (sqrt 3)) t :=
    fun t _ => (observationEnergy_hasDerivAt j b t).hasDerivWithinAt
  have hmono := observationEnergy_monotoneOn j hb.le
  have hjac := (integrableOn_image_iff_integrableOn_deriv_smul_of_monotoneOn
    measurableSet_Ioo hderiv hmono (fun e => referenceDensity j e * q e)).1 (hw.mono_set hsub)
  have heq := integral_image_eq_integral_deriv_smul_of_monotoneOn
    measurableSet_Ioo hderiv hmono (fun e => referenceDensity j e * q e)
  simp only [smul_eq_mul] at hjac heq
  calc
    _ ≤ ∫ t in Ioo (sqrt 2) (sqrt 3),
        2 * ((2 * b * t) * (referenceDensity j (observationEnergy j b t) *
          q (observationEnergy j b t))) := by
      apply integral_mono_ae hcomp (hjac.const_mul 2)
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
      have h := mul_le_mul_of_nonneg_right (observationEnergy_jacobian_lower j hb hj ht)
        (hq0 (observationEnergy j b t))
      nlinarith only [h]
    _ = 2 * ∫ e in observationEnergy j b '' Ioo (sqrt 2) (sqrt 3),
        referenceDensity j e * q e := by rw [integral_const_mul, heq]
    _ ≤ 2 * ∫ e in Ioo b (4 * b), referenceDensity j e * q e := by
      apply mul_le_mul_of_nonneg_left ?_ (by norm_num)
      exact setIntegral_mono_set hw
        (Filter.Eventually.of_forall fun e => mul_nonneg (referenceDensity_nonneg j e) (hq0 e))
        (Filter.Eventually.of_forall fun _ he => hsub he)
    _ = _ := by rw [GapFamily.Construction.integral_referenceMeasure_Ioo j hj]

/-- The original input response has a genuine squared-norm integral on the
enlarged output band, as the response of its isometric zero extension. -/
theorem correctedKernelResponse_norm_sq_integrable_enlarged
    {ι : Type*} [Fintype ι] (J : ι → ℤ) {b : ℝ} (hb : 0 < b)
    (f : LowBandHilbert J b) (j : ℤ) :
    IntegrableOn (fun e => ‖correctedKernelResponse J b f j e‖ ^ 2)
      (Ioo |(j : ℝ)| (4 * b)) (referenceMeasure j) := by
  have hbB : b ≤ 4 * b := by linarith
  have hm := correctedKernelResponse_memLp_lowBand J (4 * b) (by positivity)
    (lowBandHilbertExtension J hbB f) j
  have heq : correctedKernelResponse J (4 * b) (lowBandHilbertExtension J hbB f) j =
      correctedKernelResponse J b f j := funext (correctedKernelResponse_extension_eq J hbB f j)
  rw [heq] at hm
  exact hm.integrable_norm_pow (by norm_num)

theorem correctedKernelScaledResponse_observation_intervalIntegrable
    {ι : Type*} [Fintype ι] (J : ι → ℤ) {b : ℝ} (hb : 0 < b)
    (f : LowBandHilbert J b) (j : ℤ) :
    IntervalIntegrable (fun t : ℝ => ‖correctedKernelScaledResponse J b f j t‖ ^ 2)
      volume (sqrt 2) (sqrt 3) :=
  (((differentiable_correctedKernelScaledResponse J b hb f j).continuous.comp
    Complex.continuous_ofReal).norm.pow 2).intervalIntegrable _ _

/-- The fixed-interval holomorphic observation is controlled by the ordinary
physical response on the exterior energy interval. -/
theorem integral_norm_sq_correctedKernelScaledResponse_observation_le
    {ι : Type*} [Fintype ι] (J : ι → ℤ) {b : ℝ} (hb : 0 < b)
    (f : LowBandHilbert J b) (j : ℤ) (hj : |(j : ℝ)| ≤ b) :
    (∫ t in sqrt 2..sqrt 3, ‖correctedKernelScaledResponse J b f j t‖ ^ 2) ≤
      2 * ∫ e in Ioo b (4 * b), ‖correctedKernelResponse J b f j e‖ ^ 2
        ∂referenceMeasure j := by
  have hab : sqrt (2 : ℝ) ≤ sqrt 3 := sqrt_le_sqrt (by norm_num)
  have hi := correctedKernelScaledResponse_observation_intervalIntegrable J hb f j
  have hsub : Ioo b (4 * b) ⊆ Ioo |(j : ℝ)| (4 * b) :=
    fun _ he => ⟨hj.trans_lt he.1, he.2⟩
  have hcomp : IntegrableOn
      (fun t => ‖correctedKernelResponse J b f j (observationEnergy j b t)‖ ^ 2)
      (Ioo (sqrt 2) (sqrt 3)) := by
    apply ((intervalIntegrable_iff_integrableOn_Ioo_of_le hab).1 hi).congr_fun _ measurableSet_Ioo
    intro t ht
    dsimp only
    rw [correctedKernelScaledResponse_ofReal J b hb f j t ((sqrt_nonneg 2).trans ht.1.le)]
    rfl
  rw [intervalIntegral.integral_of_le hab, integral_Ioc_eq_integral_Ioo]
  calc
    _ = ∫ t in Ioo (sqrt 2) (sqrt 3),
        ‖correctedKernelResponse J b f j (observationEnergy j b t)‖ ^ 2 := by
      apply setIntegral_congr_fun measurableSet_Ioo
      intro t ht
      dsimp only
      rw [correctedKernelScaledResponse_ofReal J b hb f j t ((sqrt_nonneg 2).trans ht.1.le)]
      rfl
    _ ≤ _ := integral_observation_le_reference_exterior j hb hj
      (fun e => ‖correctedKernelResponse J b f j e‖ ^ 2) (fun _ => sq_nonneg _)
      ((correctedKernelResponse_norm_sq_integrable_enlarged J hb f j).mono_set hsub) hcomp

theorem correctedKernelScalarNormalizedResponse_observation_intervalIntegrable
    {ι : Type*} [Fintype ι] (J : ι → ℤ) {b : ℝ} (hb : 0 < b)
    (f : LowBandHilbert J b) :
    IntervalIntegrable (fun t : ℝ => ‖correctedKernelScalarNormalizedResponse J b f t‖ ^ 2)
      volume (sqrt 2) (sqrt 3) :=
  (((differentiable_correctedKernelScalarNormalizedResponse J b hb f).continuous.comp
    Complex.continuous_ofReal).norm.pow 2).intervalIntegrable _ _

/-- Division by the nonzero real coordinate only decreases the scalar
observation norm, since the observation interval starts above one. -/
theorem integral_norm_sq_correctedKernelScalarNormalizedResponse_observation_le
    {ι : Type*} [Fintype ι] (J : ι → ℤ) {b : ℝ} (hb : 0 < b)
    (f : LowBandHilbert J b) :
    (∫ t in sqrt 2..sqrt 3, ‖correctedKernelScalarNormalizedResponse J b f t‖ ^ 2) ≤
      2 * ∫ e in Ioo b (4 * b), ‖correctedKernelResponse J b f 0 e‖ ^ 2
        ∂referenceMeasure 0 := by
  refine le_trans ?_ (integral_norm_sq_correctedKernelScaledResponse_observation_le J hb f 0
    (by simpa using hb.le))
  apply intervalIntegral.integral_mono_on (sqrt_le_sqrt (by norm_num))
    (correctedKernelScalarNormalizedResponse_observation_intervalIntegrable J hb f)
    (correctedKernelScaledResponse_observation_intervalIntegrable J hb f 0)
  intro t ht
  have ht1 : 1 ≤ t := by
    have : (1 : ℝ) ≤ sqrt 2 := (le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
    exact this.trans ht.1
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht1
  rw [correctedKernelScalarNormalizedResponse_eq_div J b f t
    (by exact_mod_cast ht0.ne'), norm_div, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos ht0]
  have hd : ‖correctedKernelScaledResponse J b f 0 t‖ / t ≤
      ‖correctedKernelScaledResponse J b f 0 t‖ :=
    div_le_self (norm_nonneg _) ht1
  exact pow_le_pow_left₀ (div_nonneg (norm_nonneg _) ht0.le) hd 2

/-- The actual exterior response is part of the larger-band
identity-plus-kernel image of the extended input. -/
theorem integral_norm_sq_correctedKernelResponse_exterior_le_identityPlus
    {ι : Type*} [Fintype ι] (J : ι → ℤ) {b : ℝ} (hb : 0 < b)
    (f : LowBandHilbert J b) (i : ι) (hi : |(J i : ℝ)| ≤ b) :
    (∫ e in Ioo b (4 * b), ‖correctedKernelResponse J b f (J i) e‖ ^ 2
      ∂referenceMeasure (J i)) ≤
      ‖correctedLowBandIdentityPlus J (4 * b)
        (lowBandHilbertExtension J (by linarith : b ≤ 4 * b) f) i‖ ^ 2 := by
  have hbB : b ≤ 4 * b := by linarith
  let g := correctedLowBandIdentityPlus J (4 * b) (lowBandHilbertExtension J hbB f)
  have hsub : Ioo b (4 * b) ⊆ Ioo |(J i : ℝ)| (4 * b) :=
    fun _ he => ⟨hi.trans_lt he.1, he.2⟩
  have hg : IntegrableOn (fun e => ‖g i e‖ ^ 2) (Ioo |(J i : ℝ)| (4 * b))
      (referenceMeasure (J i)) := (Lp.memLp (g i)).integrable_norm_pow (by norm_num)
  have heq : (fun e => ‖correctedKernelResponse J b f (J i) e‖ ^ 2)
      =ᵐ[(referenceMeasure (J i)).restrict (Ioo b (4 * b))] (fun e => ‖g i e‖ ^ 2) := by
    have hp := (correctedLowBandIdentityPlus_extension_coeFn_exterior J hbB
      (by positivity) f i).filter_mono (ae_mono (Measure.restrict_mono hsub le_rfl))
    filter_upwards [hp, ae_restrict_mem measurableSet_Ioo] with e hpe he
    exact congrArg (fun z : ℂ => ‖z‖ ^ 2) (hpe he.1.le).symm
  calc
    _ = ∫ e in Ioo b (4 * b), ‖g i e‖ ^ 2 ∂referenceMeasure (J i) := integral_congr_ae heq
    _ ≤ ∫ e in Ioo |(J i : ℝ)| (4 * b), ‖g i e‖ ^ 2 ∂referenceMeasure (J i) :=
      setIntegral_mono_set hg (Filter.Eventually.of_forall fun _ => sq_nonneg _)
        (Filter.Eventually.of_forall fun _ he => hsub he)
    _ = ‖g i‖ ^ 2 := (lowBandRow_norm_sq_eq_integral J (4 * b) i (g i)).symm

/-- The nonscalar holomorphic observation is bounded by the actual enlarged
identity-plus-kernel image, without a positivity premise. -/
theorem integral_norm_sq_correctedKernelScaledResponse_le_identityPlus
    {ι : Type*} [Fintype ι] (J : ι → ℤ) {b : ℝ} (hb : 0 < b)
    (f : LowBandHilbert J b) (i : ι) (hi : |(J i : ℝ)| ≤ b) :
    (∫ t in sqrt 2..sqrt 3, ‖correctedKernelScaledResponse J b f (J i) t‖ ^ 2) ≤
      2 * ‖correctedLowBandIdentityPlus J (4 * b)
        (lowBandHilbertExtension J (by linarith : b ≤ 4 * b) f)‖ ^ 2 := by
  refine (integral_norm_sq_correctedKernelScaledResponse_observation_le J hb f (J i) hi).trans ?_
  apply mul_le_mul_of_nonneg_left ?_ (by norm_num)
  refine (integral_norm_sq_correctedKernelResponse_exterior_le_identityPlus J hb f i hi).trans ?_
  exact pow_le_pow_left₀ (norm_nonneg _) (PiLp.norm_apply_le _ i) 2

/-- The scalar removable quotient has the same observation bound by the
actual enlarged identity-plus-kernel image. -/
theorem integral_norm_sq_correctedKernelScalarNormalizedResponse_le_identityPlus
    {ι : Type*} [Fintype ι] (J : ι → ℤ) {b : ℝ} (hb : 0 < b)
    (f : LowBandHilbert J b) (i : ι) (hi : J i = 0) :
    (∫ t in sqrt 2..sqrt 3, ‖correctedKernelScalarNormalizedResponse J b f t‖ ^ 2) ≤
      2 * ‖correctedLowBandIdentityPlus J (4 * b)
        (lowBandHilbertExtension J (by linarith : b ≤ 4 * b) f)‖ ^ 2 := by
  refine (integral_norm_sq_correctedKernelScalarNormalizedResponse_observation_le J hb f).trans ?_
  apply mul_le_mul_of_nonneg_left ?_ (by norm_num)
  have hbound := integral_norm_sq_correctedKernelResponse_exterior_le_identityPlus J hb f i
    (by simpa only [hi, Int.cast_zero, abs_zero] using hb.le)
  have hbound' := hbound.trans (pow_le_pow_left₀ (norm_nonneg _) (PiLp.norm_apply_le _ i) 2)
  simpa only [hi] using hbound'

/-- The actual observation seminorm is at most twice the enlarged image
norm, in the exact form used by quantitative holomorphic propagation. -/
theorem sqrt_integral_norm_sq_correctedKernelScaledResponse_le_identityPlus
    {ι : Type*} [Fintype ι] (J : ι → ℤ) {b : ℝ} (hb : 0 < b)
    (f : LowBandHilbert J b) (i : ι) (hi : |(J i : ℝ)| ≤ b) :
    sqrt (∫ t in sqrt 2..sqrt 3, ‖correctedKernelScaledResponse J b f (J i) t‖ ^ 2) ≤
      2 * ‖correctedLowBandIdentityPlus J (4 * b)
        (lowBandHilbertExtension J (by linarith : b ≤ 4 * b) f)‖ := by
  apply (sqrt_le_left (by positivity)).mpr
  have h := integral_norm_sq_correctedKernelScaledResponse_le_identityPlus J hb f i hi
  nlinarith [sq_nonneg ‖correctedLowBandIdentityPlus J (4 * b)
    (lowBandHilbertExtension J (by linarith : b ≤ 4 * b) f)‖]

theorem sqrt_integral_norm_sq_correctedKernelScalarNormalizedResponse_le_identityPlus
    {ι : Type*} [Fintype ι] (J : ι → ℤ) {b : ℝ} (hb : 0 < b)
    (f : LowBandHilbert J b) (i : ι) (hi : J i = 0) :
    sqrt (∫ t in sqrt 2..sqrt 3, ‖correctedKernelScalarNormalizedResponse J b f t‖ ^ 2) ≤
      2 * ‖correctedLowBandIdentityPlus J (4 * b)
        (lowBandHilbertExtension J (by linarith : b ≤ 4 * b) f)‖ := by
  apply (sqrt_le_left (by positivity)).mpr
  have h := integral_norm_sq_correctedKernelScalarNormalizedResponse_le_identityPlus J hb f i hi
  nlinarith [sq_nonneg ‖correctedLowBandIdentityPlus J (4 * b)
    (lowBandHilbertExtension J (by linarith : b ≤ 4 * b) f)‖]

end GapFamily.Analytic
