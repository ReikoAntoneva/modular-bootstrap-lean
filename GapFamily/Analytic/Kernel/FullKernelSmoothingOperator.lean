import GapFamily.Analytic.Kernel.FullKernelSmoothing

/-!
# The ordinary full-kernel smoothing operator

The linear map below is represented by the actual response integrals. Its
target uses the physical reference measure on the open low band.
-/

noncomputable section

open MeasureTheory Real Set
open scoped BigOperators

namespace GapFamily.Analytic

theorem correctedKernelRowResponse_add (j J : ℤ) (B : ℝ) (hB : 0 ≤ B)
    (f g : LowBandRow J B) (e : ℝ) (he : |(j : ℝ)| ≤ e) :
    correctedKernelRowResponse j J B (f + g) e =
      correctedKernelRowResponse j J B f e + correctedKernelRowResponse j J B g e := by
  unfold correctedKernelRowResponse
  calc
    _ = ∫ E : ℝ, correctedKernel j J e E * f E + correctedKernel j J e E * g E
        ∂(referenceMeasure J).restrict (Ioo |(J : ℝ)| B) := by
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_add f g] with E hE
      rw [hE]
      exact mul_add _ _ _
    _ = _ := integral_add (correctedKernelRowResponse_integrable j J B hB f e he)
      (correctedKernelRowResponse_integrable j J B hB g e he)

theorem correctedKernelRowResponse_smul (j J : ℤ) (B : ℝ)
    (c : ℂ) (f : LowBandRow J B) (e : ℝ) :
    correctedKernelRowResponse j J B (c • f) e = c * correctedKernelRowResponse j J B f e := by
  unfold correctedKernelRowResponse
  calc
    _ = ∫ E : ℝ, c * (correctedKernel j J e E * f E)
        ∂(referenceMeasure J).restrict (Ioo |(J : ℝ)| B) := by
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_smul c f] with E hE
      rw [hE]
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    _ = _ := integral_const_mul _ _

theorem correctedKernelResponse_add {ι : Type*} [Fintype ι]
    (J : ι → ℤ) (B : ℝ) (hB : 0 ≤ B) (f g : LowBandHilbert J B) (j : ℤ) (e : ℝ)
    (he : |(j : ℝ)| ≤ e) :
    correctedKernelResponse J B (f + g) j e =
      correctedKernelResponse J B f j e + correctedKernelResponse J B g j e := by
  simp only [correctedKernelResponse, PiLp.add_apply,
    correctedKernelRowResponse_add _ _ _ hB _ _ _ he, Finset.sum_add_distrib]

theorem correctedKernelResponse_smul {ι : Type*} [Fintype ι]
    (J : ι → ℤ) (B : ℝ) (c : ℂ) (f : LowBandHilbert J B) (j : ℤ) (e : ℝ) :
    correctedKernelResponse J B (c • f) j e = c * correctedKernelResponse J B f j e := by
  simp only [correctedKernelResponse, PiLp.smul_apply,
    correctedKernelRowResponse_smul, Finset.mul_sum]

/-- The ordinary `L¹` target of the smoothing operator on one physical output row. -/
abbrev CorrectedKernelSmoothingRow (j : ℤ) (B : ℝ) :=
  Lp ℂ 1 ((referenceMeasure j).restrict (Ioo |(j : ℝ)| B))

/-- The actual response considered as an equivalence class in ordinary `L¹`. -/
def correctedKernelSmoothingToL1 {ι : Type*} [Fintype ι]
    (J : ι → ℤ) (B : ℝ) (hB : 0 ≤ B) (f : LowBandHilbert J B) (j : ℤ) :
    CorrectedKernelSmoothingRow j B :=
  (correctedKernelResponse_integrable_lowBand J B hB f j).toL1
    (fun e : ℝ => correctedKernelResponse J B f j e)

/-- The chosen `L¹` representative agrees almost everywhere with the ordinary response. -/
theorem coeFn_correctedKernelSmoothingToL1 {ι : Type*} [Fintype ι]
    (J : ι → ℤ) (B : ℝ) (hB : 0 ≤ B) (f : LowBandHilbert J B) (j : ℤ) :
    correctedKernelSmoothingToL1 J B hB f j =ᵐ[
      (referenceMeasure j).restrict (Ioo |(j : ℝ)| B)]
      (fun e : ℝ => correctedKernelResponse J B f j e) :=
  (correctedKernelResponse_integrable_lowBand J B hB f j).coeFn_toL1

theorem correctedKernelSmoothingToL1_add {ι : Type*} [Fintype ι]
    (J : ι → ℤ) (B : ℝ) (hB : 0 ≤ B) (f g : LowBandHilbert J B) (j : ℤ) :
    correctedKernelSmoothingToL1 J B hB (f + g) j =
      correctedKernelSmoothingToL1 J B hB f j + correctedKernelSmoothingToL1 J B hB g j := by
  apply Lp.ext
  filter_upwards [coeFn_correctedKernelSmoothingToL1 J B hB (f + g) j,
    coeFn_correctedKernelSmoothingToL1 J B hB f j,
    coeFn_correctedKernelSmoothingToL1 J B hB g j,
    Lp.coeFn_add (correctedKernelSmoothingToL1 J B hB f j)
      (correctedKernelSmoothingToL1 J B hB g j),
    ae_restrict_mem measurableSet_Ioo] with e hfg hf hg hadd he
  simp only [Pi.add_apply] at hadd
  rw [hfg, hadd, hf, hg]
  exact correctedKernelResponse_add J B hB f g j e he.1.le

theorem correctedKernelSmoothingToL1_smul {ι : Type*} [Fintype ι]
    (J : ι → ℤ) (B : ℝ) (hB : 0 ≤ B) (c : ℂ) (f : LowBandHilbert J B) (j : ℤ) :
    correctedKernelSmoothingToL1 J B hB (c • f) j = c • correctedKernelSmoothingToL1 J B hB f j := by
  apply Lp.ext
  filter_upwards [coeFn_correctedKernelSmoothingToL1 J B hB (c • f) j,
    coeFn_correctedKernelSmoothingToL1 J B hB f j,
    Lp.coeFn_smul c (correctedKernelSmoothingToL1 J B hB f j)] with e hcf hf hsmul
  simp only [Pi.smul_apply, smul_eq_mul] at hsmul
  rw [hcf, hsmul, hf]
  exact correctedKernelResponse_smul J B c f j e

/-- The `L¹` norm is exactly the ordinary absolute response integral. -/
theorem norm_correctedKernelSmoothingToL1_eq_integral {ι : Type*} [Fintype ι]
    (J : ι → ℤ) (B : ℝ) (hB : 0 ≤ B) (f : LowBandHilbert J B) (j : ℤ) :
    ‖correctedKernelSmoothingToL1 J B hB f j‖ =
      ∫ e : ℝ, ‖correctedKernelResponse J B f j e‖
        ∂(referenceMeasure j).restrict (Ioo |(j : ℝ)| B) :=
  L1.norm_of_fun_eq_integral_norm (correctedKernelResponse_integrable_lowBand J B hB f j)

theorem norm_correctedKernelSmoothingToL1_le {ι : Type*} [Fintype ι]
    (J : ι → ℤ) (B : ℝ) (hB : 0 ≤ B) (f : LowBandHilbert J B) (j : ℤ) :
    ‖correctedKernelSmoothingToL1 J B hB f j‖ ≤
      correctedSmoothingBound B * sqrt (Fintype.card ι : ℝ) * ‖f‖ := by
  rw [norm_correctedKernelSmoothingToL1_eq_integral]
  exact integral_norm_correctedKernelResponse_lowBand_le J B hB f j

/-- The linear map induced by the actual response on the quotient spaces. -/
def correctedKernelSmoothingLinear {ι : Type*} [Fintype ι]
    (J : ι → ℤ) (B : ℝ) (hB : 0 ≤ B) (j : ℤ) :
    LowBandHilbert J B →ₗ[ℂ] CorrectedKernelSmoothingRow j B where
  toFun f := correctedKernelSmoothingToL1 J B hB f j
  map_add' f g := correctedKernelSmoothingToL1_add J B hB f g j
  map_smul' c f := correctedKernelSmoothingToL1_smul J B hB c f j

/-- Actual bounded `L² → L¹` smoothing by the full corrected kernel on one output row. -/
def correctedKernelSmoothingOperator {ι : Type*} [Fintype ι]
    (J : ι → ℤ) (B : ℝ) (hB : 0 ≤ B) (j : ℤ) :
    LowBandHilbert J B →L[ℂ] CorrectedKernelSmoothingRow j B :=
  (correctedKernelSmoothingLinear J B hB j).mkContinuous
    (correctedSmoothingBound B * sqrt (Fintype.card ι : ℝ))
    (fun f => norm_correctedKernelSmoothingToL1_le J B hB f j)

@[simp]
theorem correctedKernelSmoothingOperator_apply {ι : Type*} [Fintype ι]
    (J : ι → ℤ) (B : ℝ) (hB : 0 ≤ B) (j : ℤ) (f : LowBandHilbert J B) :
    correctedKernelSmoothingOperator J B hB j f = correctedKernelSmoothingToL1 J B hB f j := rfl

/-- The continuous linear map retains the actual response as its representative. -/
theorem coeFn_correctedKernelSmoothingOperator {ι : Type*} [Fintype ι]
    (J : ι → ℤ) (B : ℝ) (hB : 0 ≤ B) (j : ℤ) (f : LowBandHilbert J B) :
    correctedKernelSmoothingOperator J B hB j f =ᵐ[
      (referenceMeasure j).restrict (Ioo |(j : ℝ)| B)]
      (fun e : ℝ => correctedKernelResponse J B f j e) :=
  coeFn_correctedKernelSmoothingToL1 J B hB f j

/-- The ordinary `L¹` smoothing and the Riesz `L²` compression represent the same function. -/
theorem coeFn_correctedKernelSmoothingOperator_eq_lowBandOperator {ι : Type*} [Fintype ι]
    (J : ι → ℤ) (B : ℝ) (hB : 0 ≤ B) (f : LowBandHilbert J B) (i : ι) :
    correctedKernelSmoothingOperator J B hB (J i) f =ᵐ[
      (referenceMeasure (J i)).restrict (Ioo |(J i : ℝ)| B)]
      correctedLowBandOperator J B f i :=
  (coeFn_correctedKernelSmoothingOperator J B hB (J i) f).trans
    (correctedLowBandOperator_coeFn J B hB f i).symm

/-- The row smoothing norm has the explicit square-root dependence on the number of inputs. -/
theorem norm_correctedKernelSmoothingOperator_le {ι : Type*} [Fintype ι]
    (J : ι → ℤ) (B : ℝ) (hB : 0 ≤ B) (j : ℤ) :
    ‖correctedKernelSmoothingOperator J B hB j‖ ≤
      correctedSmoothingBound B * sqrt (Fintype.card ι : ℝ) := by
  apply ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg (correctedSmoothingBound_nonneg B hB) (sqrt_nonneg _))
  exact fun f => norm_correctedKernelSmoothingToL1_le J B hB f j

/-- The ordinary `L¹` direct sum of finitely many physical output rows. -/
abbrev CorrectedKernelSmoothingSpace {κ : Type*} [Fintype κ] (j : κ → ℤ) (B : ℝ) :=
  PiLp 1 (fun k => CorrectedKernelSmoothingRow (j k) B)

/-- Simultaneous smoothing into the finite sum of ordinary output measures. -/
def correctedKernelFiniteSmoothingOperator {ι κ : Type*} [Fintype ι] [Fintype κ]
    (J : ι → ℤ) (j : κ → ℤ) (B : ℝ) (hB : 0 ≤ B) :
    LowBandHilbert J B →L[ℂ] CorrectedKernelSmoothingSpace j B :=
  (PiLp.continuousLinearEquiv 1 ℂ (fun k => CorrectedKernelSmoothingRow (j k) B)).symm
    |>.toContinuousLinearMap.comp
      (ContinuousLinearMap.pi fun k => correctedKernelSmoothingOperator J B hB (j k))

@[simp]
theorem correctedKernelFiniteSmoothingOperator_apply {ι κ : Type*} [Fintype ι] [Fintype κ]
    (J : ι → ℤ) (j : κ → ℤ) (B : ℝ) (hB : 0 ≤ B)
    (f : LowBandHilbert J B) (k : κ) :
    correctedKernelFiniteSmoothingOperator J j B hB f k =
      correctedKernelSmoothingOperator J B hB (j k) f := rfl

/-- The sum-space norm is the sum of the actual absolute response integrals. -/
theorem norm_correctedKernelFiniteSmoothingOperator_apply_eq_integral {ι κ : Type*}
    [Fintype ι] [Fintype κ] (J : ι → ℤ) (j : κ → ℤ) (B : ℝ) (hB : 0 ≤ B)
    (f : LowBandHilbert J B) :
    ‖correctedKernelFiniteSmoothingOperator J j B hB f‖ =
      ∑ k, ∫ e : ℝ, ‖correctedKernelResponse J B f (j k) e‖
        ∂(referenceMeasure (j k)).restrict (Ioo |(j k : ℝ)| B) := by
  rw [PiLp.norm_eq_of_L1]
  apply Finset.sum_congr rfl
  intro k hk
  exact norm_correctedKernelSmoothingToL1_eq_integral J B hB f (j k)

/-- Explicit smoothing bound for the full finite collection of output rows. -/
theorem norm_correctedKernelFiniteSmoothingOperator_apply_le {ι κ : Type*}
    [Fintype ι] [Fintype κ] (J : ι → ℤ) (j : κ → ℤ) (B : ℝ) (hB : 0 ≤ B)
    (f : LowBandHilbert J B) :
    ‖correctedKernelFiniteSmoothingOperator J j B hB f‖ ≤
      (Fintype.card κ : ℝ) * (correctedSmoothingBound B * sqrt (Fintype.card ι : ℝ)) * ‖f‖ := by
  rw [PiLp.norm_eq_of_L1]
  calc
    _ ≤ ∑ _ : κ, correctedSmoothingBound B * sqrt (Fintype.card ι : ℝ) * ‖f‖ :=
      Finset.sum_le_sum fun k _ => norm_correctedKernelSmoothingToL1_le J B hB f (j k)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

/-- The finite-output smoothing operator is bounded also when either index set is empty. -/
theorem norm_correctedKernelFiniteSmoothingOperator_le {ι κ : Type*}
    [Fintype ι] [Fintype κ] (J : ι → ℤ) (j : κ → ℤ) (B : ℝ) (hB : 0 ≤ B) :
    ‖correctedKernelFiniteSmoothingOperator J j B hB‖ ≤
      (Fintype.card κ : ℝ) * (correctedSmoothingBound B * sqrt (Fintype.card ι : ℝ)) := by
  apply ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg (Nat.cast_nonneg _)
      (mul_nonneg (correctedSmoothingBound_nonneg B hB) (sqrt_nonneg _)))
  exact norm_correctedKernelFiniteSmoothingOperator_apply_le J j B hB

end GapFamily.Analytic
