import GapFamily.Analytic.Kernel.FullKernelSmoothingSignedMeasure

/-!
# Ordinary integrability of the actual low-band inverse

For an invertible actual identity-plus-kernel operator, its inverse satisfies
`u = f - R_B u`. The proved smoothing of `R_B` therefore makes the inverse
ordinarily integrable whenever its input is. No finite scalar reference mass
and no inverse operator on the whole ordinary measure space is assumed.
-/

noncomputable section

open MeasureTheory Real Set
open scoped BigOperators

namespace GapFamily.Analytic

/-- The actual inverse equation in the Hilbert space. -/
theorem correctedLowBandIdentityPlus_ringInverse_apply
    {ι : Type*} [Fintype ι] (J : ι → ℤ) (B : ℝ)
    (hunit : IsUnit (correctedLowBandIdentityPlus J B)) (f : LowBandHilbert J B) :
    correctedLowBandIdentityPlus J B (Ring.inverse (correctedLowBandIdentityPlus J B) f) = f :=
  congrArg (fun Q : LowBandHilbert J B →L[ℂ] LowBandHilbert J B => Q f)
    (Ring.mul_inverse_cancel _ hunit)

/-- The inverse image is the input minus its genuinely smoothed correction. -/
theorem correctedLowBandInverse_eq_sub
    {ι : Type*} [Fintype ι] (J : ι → ℤ) (B : ℝ)
    (hunit : IsUnit (correctedLowBandIdentityPlus J B)) (f : LowBandHilbert J B) :
    Ring.inverse (correctedLowBandIdentityPlus J B) f =
      f - correctedLowBandOperator J B (Ring.inverse (correctedLowBandIdentityPlus J B) f) := by
  apply eq_sub_of_add_eq
  simpa only [correctedLowBandIdentityPlus_apply] using
    correctedLowBandIdentityPlus_ringInverse_apply J B hunit f

/-- Representative-level inverse equation on every actual physical row. -/
theorem correctedLowBandInverse_coeFn_eq_sub
    {ι : Type*} [Fintype ι] (J : ι → ℤ) (B : ℝ)
    (hunit : IsUnit (correctedLowBandIdentityPlus J B)) (f : LowBandHilbert J B) (i : ι) :
    ⇑(Ring.inverse (correctedLowBandIdentityPlus J B) f i) =ᵐ[
      (referenceMeasure (J i)).restrict (Ioo |(J i : ℝ)| B)]
      (fun e => f i e -
        correctedLowBandOperator J B (Ring.inverse (correctedLowBandIdentityPlus J B) f) i e) := by
  have hrow := congrArg (fun g : LowBandHilbert J B => g i)
    (correctedLowBandInverse_eq_sub J B hunit f)
  rw [PiLp.sub_apply] at hrow
  rw [hrow]
  exact Lp.coeFn_sub _ _

/-- The actual inverse preserves ordinary integrability on `L¹ ∩ H_B`. -/
theorem correctedLowBandInverse_integrable
    {ι : Type*} [Fintype ι] (J : ι → ℤ) (B : ℝ) (hB : 0 ≤ B)
    (hunit : IsUnit (correctedLowBandIdentityPlus J B)) (f : LowBandHilbert J B)
    (hf : ∀ i, Integrable (f i) ((referenceMeasure (J i)).restrict (Ioo |(J i : ℝ)| B)))
    (i : ι) :
    Integrable (Ring.inverse (correctedLowBandIdentityPlus J B) f i)
      ((referenceMeasure (J i)).restrict (Ioo |(J i : ℝ)| B)) :=
  ((hf i).sub (correctedLowBandOperator_integrable J B hB
    (Ring.inverse (correctedLowBandIdentityPlus J B) f) i)).congr
      (correctedLowBandInverse_coeFn_eq_sub J B hunit f i).symm

/-- The ordinary mass of the inverse is controlled before any Hilbert norm estimate. -/
theorem integral_norm_correctedLowBandInverse_le_input_add_response
    {ι : Type*} [Fintype ι] (J : ι → ℤ) (B : ℝ) (hB : 0 ≤ B)
    (hunit : IsUnit (correctedLowBandIdentityPlus J B)) (f : LowBandHilbert J B)
    (hf : ∀ i, Integrable (f i) ((referenceMeasure (J i)).restrict (Ioo |(J i : ℝ)| B)))
    (i : ι) :
    (∫ e, ‖Ring.inverse (correctedLowBandIdentityPlus J B) f i e‖
      ∂(referenceMeasure (J i)).restrict (Ioo |(J i : ℝ)| B)) ≤
      (∫ e, ‖f i e‖ ∂(referenceMeasure (J i)).restrict (Ioo |(J i : ℝ)| B)) +
      ∫ e, ‖correctedLowBandOperator J B
        (Ring.inverse (correctedLowBandIdentityPlus J B) f) i e‖
        ∂(referenceMeasure (J i)).restrict (Ioo |(J i : ℝ)| B) := by
  rw [← integral_add (hf i).norm (correctedLowBandOperator_integrable J B hB
    (Ring.inverse (correctedLowBandIdentityPlus J B) f) i).norm]
  apply integral_mono_ae (correctedLowBandInverse_integrable J B hB hunit f hf i).norm
    ((hf i).norm.add (correctedLowBandOperator_integrable J B hB
      (Ring.inverse (correctedLowBandIdentityPlus J B) f) i).norm)
  filter_upwards [correctedLowBandInverse_coeFn_eq_sub J B hunit f i] with e he
  rw [he]
  exact norm_sub_le _ _

/-- An explicit row mass estimate using the norm of the actual bounded inverse. -/
theorem integral_norm_correctedLowBandInverse_le
    {ι : Type*} [Fintype ι] (J : ι → ℤ) (B : ℝ) (hB : 0 ≤ B)
    (hunit : IsUnit (correctedLowBandIdentityPlus J B)) (f : LowBandHilbert J B)
    (hf : ∀ i, Integrable (f i) ((referenceMeasure (J i)).restrict (Ioo |(J i : ℝ)| B)))
    (i : ι) :
    (∫ e, ‖Ring.inverse (correctedLowBandIdentityPlus J B) f i e‖
      ∂(referenceMeasure (J i)).restrict (Ioo |(J i : ℝ)| B)) ≤
      (∫ e, ‖f i e‖ ∂(referenceMeasure (J i)).restrict (Ioo |(J i : ℝ)| B)) +
        correctedSmoothingBound B * sqrt (Fintype.card ι : ℝ) *
          ‖Ring.inverse (correctedLowBandIdentityPlus J B)‖ * ‖f‖ := by
  apply (integral_norm_correctedLowBandInverse_le_input_add_response J B hB hunit f hf i).trans
  apply add_le_add le_rfl
  calc
    _ = ∫ e, ‖correctedKernelResponse J B
        (Ring.inverse (correctedLowBandIdentityPlus J B) f) (J i) e‖
        ∂(referenceMeasure (J i)).restrict (Ioo |(J i : ℝ)| B) := by
      apply integral_congr_ae
      filter_upwards [correctedLowBandOperator_coeFn J B hB
        (Ring.inverse (correctedLowBandIdentityPlus J B) f) i] with e he
      exact congrArg norm he
    _ ≤ correctedSmoothingBound B * sqrt (Fintype.card ι : ℝ) *
        ‖Ring.inverse (correctedLowBandIdentityPlus J B) f‖ :=
      integral_norm_correctedKernelResponse_lowBand_le J B hB _ (J i)
    _ ≤ correctedSmoothingBound B * sqrt (Fintype.card ι : ℝ) *
        (‖Ring.inverse (correctedLowBandIdentityPlus J B)‖ * ‖f‖) :=
      mul_le_mul_of_nonneg_left ((Ring.inverse (correctedLowBandIdentityPlus J B)).le_opNorm f)
        (mul_nonneg (correctedSmoothingBound_nonneg B hB) (sqrt_nonneg _))
    _ = _ := by ring

theorem sum_integral_norm_correctedLowBandInverse_le
    {ι : Type*} [Fintype ι] (J : ι → ℤ) (B : ℝ) (hB : 0 ≤ B)
    (hunit : IsUnit (correctedLowBandIdentityPlus J B)) (f : LowBandHilbert J B)
    (hf : ∀ i, Integrable (f i) ((referenceMeasure (J i)).restrict (Ioo |(J i : ℝ)| B))) :
    (∑ i, ∫ e, ‖Ring.inverse (correctedLowBandIdentityPlus J B) f i e‖
      ∂(referenceMeasure (J i)).restrict (Ioo |(J i : ℝ)| B)) ≤
      (∑ i, ∫ e, ‖f i e‖ ∂(referenceMeasure (J i)).restrict (Ioo |(J i : ℝ)| B)) +
        (Fintype.card ι : ℝ) * correctedSmoothingBound B * sqrt (Fintype.card ι : ℝ) *
          ‖Ring.inverse (correctedLowBandIdentityPlus J B)‖ * ‖f‖ := by
  calc
    _ ≤ ∑ i, ((∫ e, ‖f i e‖ ∂(referenceMeasure (J i)).restrict (Ioo |(J i : ℝ)| B)) +
        correctedSmoothingBound B * sqrt (Fintype.card ι : ℝ) *
          ‖Ring.inverse (correctedLowBandIdentityPlus J B)‖ * ‖f‖) :=
      Finset.sum_le_sum fun i _ => integral_norm_correctedLowBandInverse_le J B hB hunit f hf i
    _ = _ := by rw [Finset.sum_add_distrib]; simp; ring

/-- The physical spin count gives the `B^(7/2)` correction loss for the inverse. -/
theorem sum_integral_norm_correctedLowBandInverse_le_physical
    {ι : Type*} [Fintype ι] (J : ι → ℤ) (hJ : Function.Injective J)
    (B : ℝ) (hB : 1 ≤ B) (hband : ∀ i, |(J i : ℝ)| < B)
    (hunit : IsUnit (correctedLowBandIdentityPlus J B)) (f : LowBandHilbert J B)
    (hf : ∀ i, Integrable (f i) ((referenceMeasure (J i)).restrict (Ioo |(J i : ℝ)| B))) :
    (∑ i, ∫ e, ‖Ring.inverse (correctedLowBandIdentityPlus J B) f i e‖
      ∂(referenceMeasure (J i)).restrict (Ioo |(J i : ℝ)| B)) ≤
      (∑ i, ∫ e, ‖f i e‖ ∂(referenceMeasure (J i)).restrict (Ioo |(J i : ℝ)| B)) +
        20 * correctedKernelBound * sqrt 5 * B ^ 3 * sqrt B *
          ‖Ring.inverse (correctedLowBandIdentityPlus J B)‖ * ‖f‖ := by
  have hB0 : 0 ≤ B := by linarith
  have hC := correctedKernelBound_pos
  calc
    _ ≤ ∑ i, ((∫ e, ‖f i e‖ ∂(referenceMeasure (J i)).restrict (Ioo |(J i : ℝ)| B)) +
        ∫ e, ‖correctedLowBandOperator J B (Ring.inverse (correctedLowBandIdentityPlus J B) f) i e‖
          ∂(referenceMeasure (J i)).restrict (Ioo |(J i : ℝ)| B)) :=
      Finset.sum_le_sum fun i _ =>
        integral_norm_correctedLowBandInverse_le_input_add_response J B hB0 hunit f hf i
    _ = (∑ i, ∫ e, ‖f i e‖ ∂(referenceMeasure (J i)).restrict (Ioo |(J i : ℝ)| B)) +
        ∑ i, ∫ e, ‖correctedLowBandOperator J B
          (Ring.inverse (correctedLowBandIdentityPlus J B) f) i e‖
          ∂(referenceMeasure (J i)).restrict (Ioo |(J i : ℝ)| B) := Finset.sum_add_distrib
    _ ≤ (∑ i, ∫ e, ‖f i e‖ ∂(referenceMeasure (J i)).restrict (Ioo |(J i : ℝ)| B)) +
        20 * correctedKernelBound * sqrt 5 * B ^ 3 * sqrt B *
          ‖Ring.inverse (correctedLowBandIdentityPlus J B) f‖ :=
      add_le_add le_rfl (sum_integral_norm_correctedLowBandOperator_le_physical J hJ B hB hband _)
    _ ≤ _ := by
      apply add_le_add le_rfl
      calc
        _ ≤ (20 * correctedKernelBound * sqrt 5 * B ^ 3 * sqrt B) *
            (‖Ring.inverse (correctedLowBandIdentityPlus J B)‖ * ‖f‖) :=
          mul_le_mul_of_nonneg_left ((Ring.inverse (correctedLowBandIdentityPlus J B)).le_opNorm f)
            (by positivity)
        _ = _ := by ring

/-- The Hilbert representative of every compact signed seed has ordinary mass. -/
theorem correctedSignedResponseHilbert_integrable
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (ν : ι → SignedMeasure ℝ) (J : ι → ℤ) (j : κ → ℤ) (M B : ℝ)
    (hM : 0 ≤ M) (hB : 0 ≤ B)
    (hs : ∀ i, ∀ᵐ E ∂(ν i).variation, |(J i : ℝ)| ≤ E ∧ E ≤ M) (k : κ) :
    Integrable (correctedSignedResponseHilbert ν J j M B hM hB hs k)
      ((referenceMeasure (j k)).restrict (Ioo |(j k : ℝ)| B)) :=
  (correctedSignedResponse_integrable_lowBand ν J (j k) M B hs).congr
    (correctedSignedResponseLp_coeFn ν J (j k) M B hM hB hs).symm

/-- The actual inverse of a compact signed-seed response is ordinarily integrable. -/
theorem correctedLowBandInverse_signedSeed_integrable
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (ν : ι → SignedMeasure ℝ) (J : ι → ℤ) (j : κ → ℤ) (M B : ℝ)
    (hM : 0 ≤ M) (hB : 0 ≤ B)
    (hs : ∀ i, ∀ᵐ E ∂(ν i).variation, |(J i : ℝ)| ≤ E ∧ E ≤ M)
    (hunit : IsUnit (correctedLowBandIdentityPlus j B)) (k : κ) :
    Integrable (Ring.inverse (correctedLowBandIdentityPlus j B)
      (correctedSignedResponseHilbert ν J j M B hM hB hs) k)
      ((referenceMeasure (j k)).restrict (Ioo |(j k : ℝ)| B)) :=
  correctedLowBandInverse_integrable j B hB hunit _
    (correctedSignedResponseHilbert_integrable ν J j M B hM hB hs) k

/-- The inverse ordinary-mass estimate for actual compact physical signed seeds. -/
theorem sum_integral_norm_correctedLowBandInverse_signedSeed_le_physical
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (ν : ι → SignedMeasure ℝ) (J : ι → ℤ) (j : κ → ℤ)
    (hj : Function.Injective j) (B : ℝ) (hB : 1 ≤ B)
    (hband : ∀ k, |(j k : ℝ)| < B)
    (hs : ∀ i, ∀ᵐ E ∂(ν i).variation, |(J i : ℝ)| ≤ E ∧ E ≤ 3 * B)
    (hunit : IsUnit (correctedLowBandIdentityPlus j B)) :
    (∑ k, ∫ e, ‖Ring.inverse (correctedLowBandIdentityPlus j B)
      (correctedSignedResponseHilbert ν J j (3 * B) B (by linarith) (by linarith) hs) k e‖
      ∂(referenceMeasure (j k)).restrict (Ioo |(j k : ℝ)| B)) ≤
      (45 * correctedKernelBound * B ^ 3 +
        500 * correctedKernelBound ^ 2 * B ^ 6 * ‖Ring.inverse (correctedLowBandIdentityPlus j B)‖) *
          signedSeedMass ν := by
  have hB0 : 0 ≤ B := by linarith
  have hM0 : 0 ≤ 3 * B := by positivity
  have hC := correctedKernelBound_pos
  let r := correctedSignedResponseHilbert ν J j (3 * B) B hM0 hB0 hs
  have hr := correctedSignedResponseHilbert_integrable ν J j (3 * B) B hM0 hB0 hs
  have hmass : (∑ k, ∫ e, ‖r k e‖
      ∂(referenceMeasure (j k)).restrict (Ioo |(j k : ℝ)| B)) ≤
      45 * correctedKernelBound * signedSeedMass ν * B ^ 3 := by
    convert sum_integral_norm_correctedSignedResponse_lowBand_le_physical ν J j hj B hB hband hs using 1
    apply Finset.sum_congr rfl
    intro k hk
    apply integral_congr_ae
    filter_upwards [correctedSignedResponseLp_coeFn ν J (j k) (3 * B) B hM0 hB0 hs] with e he
    exact congrArg norm he
  have hnorm : ‖r‖ ≤ 5 * sqrt 5 * correctedKernelBound * signedSeedMass ν * B ^ 2 * sqrt B :=
    norm_correctedSignedResponseHilbert_le_physical ν J j hj B hB hband hs
  calc
    _ ≤ (∑ k, ∫ e, ‖r k e‖ ∂(referenceMeasure (j k)).restrict (Ioo |(j k : ℝ)| B)) +
        20 * correctedKernelBound * sqrt 5 * B ^ 3 * sqrt B *
          ‖Ring.inverse (correctedLowBandIdentityPlus j B)‖ * ‖r‖ :=
      sum_integral_norm_correctedLowBandInverse_le_physical j hj B hB hband hunit r hr
    _ ≤ 45 * correctedKernelBound * signedSeedMass ν * B ^ 3 +
        20 * correctedKernelBound * sqrt 5 * B ^ 3 * sqrt B *
          ‖Ring.inverse (correctedLowBandIdentityPlus j B)‖ *
            (5 * sqrt 5 * correctedKernelBound * signedSeedMass ν * B ^ 2 * sqrt B) := by
      exact add_le_add hmass (mul_le_mul_of_nonneg_left hnorm (by positivity))
    _ = _ := by
      have hs5 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
      have hsB := Real.sq_sqrt hB0
      ring_nf
      rw [hs5, hsB]
      ring

end GapFamily.Analytic
