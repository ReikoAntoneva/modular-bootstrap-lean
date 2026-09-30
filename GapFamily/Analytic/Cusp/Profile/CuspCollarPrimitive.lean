import GapFamily.Analytic.Cusp.Profile.CuspCollarPrimitiveContinuity

/-!
# Bounded integration primitives on logarithmic collars

Every collar `L²` source defines an ordinary continuous partial integral on
any observation collar. Cauchy–Schwarz gives the square-root source-mass bound.
-/

noncomputable section
namespace GapFamily.Analytic

open Set MeasureTheory

/-- Every partial source integral is an ordinary convergent integral. -/
theorem cuspCollarPrimitive_integrable (T t : ℝ)
    (f : Lp ℂ 2 (cuspGreenCollarMeasure 0 T)) :
    IntegrableOn f {u : CuspGreenCollar 0 T | (u : ℝ) ≤ t}
      (cuspGreenCollarMeasure 0 T) :=
  (cuspGreenCollarSource_integrable 0 T f).integrableOn

/-- Uniform Cauchy–Schwarz control of the literal partial integral. -/
theorem norm_cuspCollarPrimitiveIntegral_le (T t : ℝ)
    (f : Lp ℂ 2 (cuspGreenCollarMeasure 0 T)) :
    ‖∫ u : CuspGreenCollar 0 T in {u | (u : ℝ) ≤ t}, f u
      ∂cuspGreenCollarMeasure 0 T‖ ≤
        Real.sqrt ((cuspGreenCollarMeasure 0 T).real univ) * ‖f‖ := by
  let S : Set (CuspGreenCollar 0 T) := {u | (u : ℝ) ≤ t}
  have hS : MeasurableSet S := measurableSet_cuspCollarPrimitiveSlice T t
  have hμS : cuspGreenCollarMeasure 0 T S ≠ ⊤ := measure_ne_top _ _
  let k : Lp ℂ 2 (cuspGreenCollarMeasure 0 T) := indicatorConstLp 2 hS hμS (1 : ℂ)
  have hk : ‖k‖ = Real.sqrt ((cuspGreenCollarMeasure 0 T).real S) := by
    have h := norm_indicatorConstLp (p := 2) (μ := cuspGreenCollarMeasure 0 T)
      (hs := hS) (hμs := hμS) (c := (1 : ℂ)) (by norm_num) (by norm_num)
    simpa only [k, norm_one, one_mul, ENNReal.toReal_ofNat, Real.sqrt_eq_rpow, one_div] using h
  have hknorm : ‖k‖ ≤ Real.sqrt ((cuspGreenCollarMeasure 0 T).real univ) := by
    rw [hk]
    exact Real.sqrt_le_sqrt (measureReal_mono (subset_univ S))
  change ‖∫ u in S, f u ∂cuspGreenCollarMeasure 0 T‖ ≤ _
  rw [← L2.inner_indicatorConstLp_one hS hμS f]
  exact (norm_inner_le_norm k f).trans
    (mul_le_mul_of_nonneg_right hknorm (norm_nonneg f))

/-- The literal partial integral as a continuous function on the observation collar. -/
def cuspCollarPrimitiveValue (L T : ℝ)
    (f : Lp ℂ 2 (cuspGreenCollarMeasure 0 T)) : C(CuspGreenCollar 0 L, ℂ) :=
  ⟨fun t => ∫ u : CuspGreenCollar 0 T in {u | (u : ℝ) ≤ (t : ℝ)}, f u
      ∂cuspGreenCollarMeasure 0 T,
    (continuous_cuspCollarPrimitiveIntegral T f).comp continuous_subtype_val⟩

theorem norm_cuspCollarPrimitiveValue_le (L T : ℝ)
    (f : Lp ℂ 2 (cuspGreenCollarMeasure 0 T)) :
    ‖cuspCollarPrimitiveValue L T f‖ ≤
      Real.sqrt ((cuspGreenCollarMeasure 0 T).real univ) * ‖f‖ := by
  apply (ContinuousMap.norm_le _ (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mpr
  intro t
  exact norm_cuspCollarPrimitiveIntegral_le T t f

/-- The actual source primitive is complex linear. -/
def cuspCollarPrimitiveLinearMap (L T : ℝ) :
    Lp ℂ 2 (cuspGreenCollarMeasure 0 T) →ₗ[ℂ] C(CuspGreenCollar 0 L, ℂ) where
  toFun := cuspCollarPrimitiveValue L T
  map_add' f g := by
    ext t
    change (∫ u : CuspGreenCollar 0 T in {u | (u : ℝ) ≤ (t : ℝ)}, (f + g) u
        ∂cuspGreenCollarMeasure 0 T) = _
    rw [integral_congr_ae (ae_restrict_of_ae (Lp.coeFn_add f g))]
    simp only [Pi.add_apply]
    rw [integral_add (cuspCollarPrimitive_integrable T t f) (cuspCollarPrimitive_integrable T t g)]
    rfl
  map_smul' c f := by
    ext t
    change (∫ u : CuspGreenCollar 0 T in {u | (u : ℝ) ≤ (t : ℝ)}, (c • f) u
        ∂cuspGreenCollarMeasure 0 T) = _
    rw [integral_congr_ae (ae_restrict_of_ae (Lp.coeFn_smul c f))]
    simp only [Pi.smul_apply]
    rw [integral_smul]
    rfl

/-- Bounded partial integration from every actual collar `L²` source to continuous observations. -/
def cuspCollarPrimitive (L T : ℝ) :
    Lp ℂ 2 (cuspGreenCollarMeasure 0 T) →L[ℂ] C(CuspGreenCollar 0 L, ℂ) :=
  (cuspCollarPrimitiveLinearMap L T).mkContinuous
    (Real.sqrt ((cuspGreenCollarMeasure 0 T).real univ))
    (norm_cuspCollarPrimitiveValue_le L T)

theorem cuspCollarPrimitive_apply (L T : ℝ)
    (f : Lp ℂ 2 (cuspGreenCollarMeasure 0 T)) (t : CuspGreenCollar 0 L) :
    cuspCollarPrimitive L T f t =
      ∫ u : CuspGreenCollar 0 T in {u | (u : ℝ) ≤ (t : ℝ)}, f u
        ∂cuspGreenCollarMeasure 0 T := rfl

theorem norm_cuspCollarPrimitive_le_mass (L T : ℝ) :
    ‖cuspCollarPrimitive L T‖ ≤ Real.sqrt ((cuspGreenCollarMeasure 0 T).real univ) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
  exact norm_cuspCollarPrimitiveValue_le L T

/-- The operator bound depends only on the unnormalized source collar length. -/
theorem norm_cuspCollarPrimitive_le (L : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    ‖cuspCollarPrimitive L T‖ ≤ Real.sqrt T := by
  simpa only [cuspGreenCollarMeasure_real_univ 0 T hT, sub_zero] using
    norm_cuspCollarPrimitive_le_mass L T

end GapFamily.Analytic
