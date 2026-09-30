import GapFamily.Analytic.Foundation.PositiveBCFPower
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import GapFamily.Analytic.Poincare.Fourier.PoincareFourierRemainderBound

/-! Analytic ordinary integrals from a fixed integrable weight and genuine bounded positive powers. -/

noncomputable section
namespace GapFamily.Analytic.PoincareFourierRemainder

open MeasureTheory Set Filter
open scoped Topology BoundedContinuousFunction

theorem integrable_bcf_mul (f : ℝ → ℂ) (hf : Integrable f) (b : ℝ →ᵇ ℂ) :
    Integrable (fun t => b t * f t) :=
  hf.bdd_mul b.continuous.aestronglyMeasurable
    (Eventually.of_forall (fun t => b.norm_coe_le_norm t))

/-- Integration against a fixed actual L1 function, as a complex linear functional on BCF. -/
def bcfWeightedIntegral (f : ℝ → ℂ) (hf : Integrable f) : (ℝ →ᵇ ℂ) →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun b => ∫ t : ℝ, b t * f t
      map_add' := by
        intro b d
        simp only [BoundedContinuousFunction.add_apply, add_mul]
        exact integral_add (integrable_bcf_mul f hf b) (integrable_bcf_mul f hf d)
      map_smul' := by
        intro z b
        simp only [BoundedContinuousFunction.smul_apply, smul_eq_mul, mul_assoc]
        exact integral_const_mul z _ }
    (∫ t : ℝ, ‖f t‖) (by
      intro b
      have hbound : ∀ᵐ t : ℝ, ‖b t * f t‖ ≤ ‖b‖ * ‖f t‖ :=
        Eventually.of_forall fun t => by
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_right (b.norm_coe_le_norm t) (norm_nonneg _)
      have h := norm_integral_le_of_norm_le (hf.norm.const_mul ‖b‖) hbound
      change ‖∫ t : ℝ, b t * f t‖ ≤ (∫ t : ℝ, ‖f t‖) * ‖b‖
      rw [integral_const_mul] at h
      exact h.trans_eq (mul_comm _ _))

@[simp] theorem bcfWeightedIntegral_apply (f : ℝ → ℂ) (hf : Integrable f)
    (b : ℝ →ᵇ ℂ) : bcfWeightedIntegral f hf b = ∫ t : ℝ, b t * f t := rfl

/-- One integrable shifted weight suffices; the positive base may approach zero. -/
theorem analyticAt_integral_positivePower_mul
    (p : ℝ → ℝ) (hp : Continuous p) (hpos : ∀ t, 0 < p t)
    (M : ℝ) (hM : ∀ t, p t ≤ M) (a : ℝ → ℂ) (δ : ℝ)
    (hδ : Integrable (fun t : ℝ => (p t : ℂ) ^ (δ : ℂ) * a t))
    {s : ℂ} (hs : δ < s.re) :
    AnalyticAt ℂ (fun z : ℂ => ∫ t : ℝ, (p t : ℂ) ^ z * a t) s := by
  let f : ℝ → ℂ := fun t => (p t : ℂ) ^ (δ : ℂ) * a t
  let L := bcfWeightedIntegral f hδ
  have hsub : AnalyticAt ℂ (fun z : ℂ => z - (δ : ℂ)) s :=
    analyticAt_id.sub analyticAt_const
  have hshift : AnalyticAt ℂ
      (fun z : ℂ => PositiveBCFPower.positivePower p hp hpos M hM (z - (δ : ℂ))) s :=
    (PositiveBCFPower.positivePower_analyticAt p hp hpos M hM
      (s := s - (δ : ℂ)) (by simp only [Complex.sub_re, Complex.ofReal_re]; linarith)).comp_of_eq
        hsub rfl
  have hL := (L.analyticAt _).comp hshift
  apply hL.congr
  filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs] with z hz
  change L (PositiveBCFPower.positivePower p hp hpos M hM (z - (δ : ℂ))) = _
  rw [bcfWeightedIntegral_apply]
  apply integral_congr_ae
  filter_upwards [] with t
  rw [PositiveBCFPower.positivePower_apply p hp hpos M hM
    (by simp only [Complex.sub_re, Complex.ofReal_re]; linarith)]
  change (p t : ℂ) ^ (z - (δ : ℂ)) * ((p t : ℂ) ^ (δ : ℂ) * a t) = _
  rw [← mul_assoc, ← Complex.cpow_add _ _ (by exact_mod_cast (hpos t).ne'), sub_add_cancel]

theorem continuous_remainderPowerBase {c y : ℝ} (hc : 0 < c) (hy : 0 < y) :
    Continuous (fun t : ℝ => y / (c ^ 2 * (t ^ 2 + y ^ 2))) := by
  apply continuous_const.div (by fun_prop)
  intro t
  positivity

theorem remainderPowerBase_pos {c y : ℝ} (hc : 0 < c) (hy : 0 < y) (t : ℝ) :
    0 < y / (c ^ 2 * (t ^ 2 + y ^ 2)) := by positivity

theorem remainderPowerBase_le {c y : ℝ} (hc : 0 < c) (hy : 0 < y) (t : ℝ) :
    y / (c ^ 2 * (t ^ 2 + y ^ 2)) ≤ 1 / (c ^ 2 * y) := by
  apply (div_le_div_iff₀ (by positivity : 0 < c ^ 2 * (t ^ 2 + y ^ 2))
    (by positivity : 0 < c ^ 2 * y)).mpr
  nlinarith [mul_nonneg (sq_nonneg c) (sq_nonneg t)]

/-- The actual ordinary phase-subtracted Fourier integral is analytic on Re s > 0. -/
theorem analyticAt_integral_fourierRemainderKernel {c y : ℝ}
    (hc : 0 < c) (hy : 0 < y) (j J : ℤ) {s : ℂ} (hs : 0 < s.re) :
    AnalyticAt ℂ (fun z : ℂ => ∫ t : ℝ, fourierRemainderKernel c y j J z t) s := by
  have hδ : 0 < s.re / 2 := half_pos hs
  have hfδ : Integrable (fun t : ℝ =>
      ((y / (c ^ 2 * (t ^ 2 + y ^ 2)) : ℝ) : ℂ) ^ ((s.re / 2 : ℝ) : ℂ) *
        ((cuspFourierMode (-J) (t / (c ^ 2 * (t ^ 2 + y ^ 2))) - 1) *
          cuspFourierMode (-j) t)) := by
    have h0 := integrable_fourierRemainderKernel hc hy j J
      (s := ((s.re / 2 : ℝ) : ℂ)) (by simpa only [Complex.ofReal_re] using hδ)
    change Integrable (fun t : ℝ =>
      fourierRemainderKernel c y j J ((s.re / 2 : ℝ) : ℂ) t) at h0
    simpa only [fourierRemainderKernel, mul_assoc] using
      h0
  have h := analyticAt_integral_positivePower_mul
    (fun t : ℝ => y / (c ^ 2 * (t ^ 2 + y ^ 2)))
    (continuous_remainderPowerBase hc hy) (remainderPowerBase_pos hc hy)
    (1 / (c ^ 2 * y)) (remainderPowerBase_le hc hy)
    (fun t : ℝ => (cuspFourierMode (-J) (t / (c ^ 2 * (t ^ 2 + y ^ 2))) - 1) *
      cuspFourierMode (-j) t) (s.re / 2) hfδ (half_lt_self hs)
  simpa only [fourierRemainderKernel, mul_assoc] using h

end GapFamily.Analytic.PoincareFourierRemainder
