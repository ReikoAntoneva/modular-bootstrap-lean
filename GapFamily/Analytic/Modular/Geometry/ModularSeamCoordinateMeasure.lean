import GapFamily.Analytic.Modular.Geometry.ModularCoordinate

/-!
# Hyperbolic and Euclidean measure on an upper-half-plane region

Restricting the actual hyperbolic volume to the preimage of a complex region
and then applying the coordinate embedding gives exactly the local density
`1/y²`. Multiplication by `y²` therefore transfers ordinary integrals and
integrability to Euclidean area, for any measurable region above the real axis.
-/

noncomputable section

namespace GapFamily.Analytic

open Set MeasureTheory
open scoped ENNReal NNReal

/-- Restriction of the full hyperbolic volume, transported to complex coordinates,
is exactly the inverse-square local measure. No fundamental-domain restriction
or omission of seams occurs. -/
theorem map_coe_restrict_upperHalfPlaneVolume {K : Set ℂ}
    (hupper : ∀ z ∈ K, 0 < z.im) :
    Measure.map UpperHalfPlane.coe
      ((volume : Measure UpperHalfPlane).restrict (UpperHalfPlane.coe ⁻¹' K)) =
      Dirichlet.localHyperbolicMeasure K := by
  ext s hs
  rw [Measure.map_apply UpperHalfPlane.measurable_coe hs,
    Measure.restrict_apply (UpperHalfPlane.measurable_coe hs),
    UpperHalfPlane.volume_eq_lintegral]
  have himage : UpperHalfPlane.coe ''
      (UpperHalfPlane.coe ⁻¹' s ∩ UpperHalfPlane.coe ⁻¹' K) = s ∩ K := by
    ext z
    constructor
    · rintro ⟨τ, ⟨hτs, hτK⟩, rfl⟩
      exact ⟨hτs, hτK⟩
    · rintro ⟨hzs, hzK⟩
      exact ⟨⟨z, hupper z hzK⟩, ⟨hzs, hzK⟩, rfl⟩
  rw [himage, Dirichlet.localHyperbolicMeasure,
    withDensity_apply _ hs, Measure.restrict_restrict hs]
  exact lintegral_congr hyperbolicDensity_eq

/-- The exact coordinate change of a restricted hyperbolic volume is measure preserving. -/
theorem measurePreserving_coe_restrict_upperHalfPlaneVolume {K : Set ℂ}
    (hupper : ∀ z ∈ K, 0 < z.im) :
    MeasurePreserving UpperHalfPlane.coe
      ((volume : Measure UpperHalfPlane).restrict (UpperHalfPlane.coe ⁻¹' K))
      (Dirichlet.localHyperbolicMeasure K) :=
  ⟨UpperHalfPlane.measurable_coe, map_coe_restrict_upperHalfPlaneVolume hupper⟩

/-- Multiplication by the square of the height cancels the local hyperbolic density,
for arbitrary real normed-space-valued integrands. -/
theorem Dirichlet.localHyperbolic_integral_im_sq_smul
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K : Set ℂ} (hK : MeasurableSet K) (hupper : ∀ z ∈ K, 0 < z.im) (f : ℂ → E) :
    (∫ z, z.im ^ 2 • f z ∂Dirichlet.localHyperbolicMeasure K) = ∫ z in K, f z := by
  rw [Dirichlet.localHyperbolicMeasure, integral_withDensity_eq_integral_toReal_smul
    (by fun_prop : Measurable (fun z : ℂ => ENNReal.ofReal (1 / z.im ^ 2)))
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem hK] with z hz
  rw [ENNReal.toReal_ofReal (by positivity), smul_smul,
    one_div_mul_cancel (pow_ne_zero 2 (hupper z hz).ne'), one_smul]

/-- The density cancellation preserves actual ordinary integrability. -/
theorem Dirichlet.localHyperbolic_integrable_im_sq_smul_iff
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K : Set ℂ} (hK : MeasurableSet K) (hupper : ∀ z ∈ K, 0 < z.im) (f : ℂ → E) :
    Integrable (fun z => z.im ^ 2 • f z) (Dirichlet.localHyperbolicMeasure K) ↔
      IntegrableOn f K := by
  rw [Dirichlet.localHyperbolicMeasure, integrable_withDensity_iff_integrable_smul'
    (by fun_prop : Measurable (fun z : ℂ => ENNReal.ofReal (1 / z.im ^ 2)))
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  apply integrable_congr
  filter_upwards [ae_restrict_mem hK] with z hz
  rw [ENNReal.toReal_ofReal (by positivity), smul_smul,
    one_div_mul_cancel (pow_ne_zero 2 (hupper z hz).ne'), one_smul]

/-- Euclidean integration equals the height-square weighted ordinary integral
in the actual upper-half-plane hyperbolic volume. -/
theorem setIntegral_eq_upperHalfPlane_im_sq_smul
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K : Set ℂ} (hK : MeasurableSet K) (hupper : ∀ z ∈ K, 0 < z.im) (f : ℂ → E) :
    (∫ z in K, f z) =
      ∫ τ : UpperHalfPlane in UpperHalfPlane.coe ⁻¹' K, τ.im ^ 2 • f τ := by
  rw [← Dirichlet.localHyperbolic_integral_im_sq_smul hK hupper f,
    ← map_coe_restrict_upperHalfPlaneVolume hupper]
  exact UpperHalfPlane.measurableEmbedding_coe.integral_map (fun z => z.im ^ 2 • f z)

/-- The Euclidean integral in the preceding identity is an ordinary integrable
function exactly when the height-square weighted hyperbolic integrand is. -/
theorem integrableOn_upperHalfPlane_im_sq_smul_iff
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K : Set ℂ} (hK : MeasurableSet K) (hupper : ∀ z ∈ K, 0 < z.im) (f : ℂ → E) :
    IntegrableOn (fun τ : UpperHalfPlane => τ.im ^ 2 • f τ)
      (UpperHalfPlane.coe ⁻¹' K) ↔ IntegrableOn f K := by
  rw [← Dirichlet.localHyperbolic_integrable_im_sq_smul_iff hK hupper f,
    ← map_coe_restrict_upperHalfPlaneVolume hupper]
  exact (UpperHalfPlane.measurableEmbedding_coe.integrable_map_iff
    (g := fun z : ℂ => z.im ^ 2 • f z)).symm

/-- Real-valued density cancellation, with the hyperbolic integral on the left. -/
theorem upperHalfPlane_setIntegral_im_sq_mul {K : Set ℂ}
    (hK : MeasurableSet K) (hupper : ∀ z ∈ K, 0 < z.im) (g : ℂ → ℝ) :
    (∫ τ : UpperHalfPlane in UpperHalfPlane.coe ⁻¹' K, τ.im ^ 2 * g τ) =
      ∫ z in K, g z := by
  simpa only [smul_eq_mul] using
    (setIntegral_eq_upperHalfPlane_im_sq_smul hK hupper g).symm

/-- Ordinary integrability under the real-valued density cancellation. -/
theorem upperHalfPlane_integrableOn_im_sq_mul_iff {K : Set ℂ}
    (hK : MeasurableSet K) (hupper : ∀ z ∈ K, 0 < z.im) (g : ℂ → ℝ) :
    IntegrableOn (fun τ : UpperHalfPlane => τ.im ^ 2 * g τ)
      (UpperHalfPlane.coe ⁻¹' K) ↔ IntegrableOn g K := by
  simpa only [smul_eq_mul] using integrableOn_upperHalfPlane_im_sq_smul_iff hK hupper g

end GapFamily.Analytic
