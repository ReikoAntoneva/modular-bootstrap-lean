import GapFamily.Analytic.Modular.Periodization.ModularPeriodizationGradientUnfold
import GapFamily.Analytic.Modular.Geometry.ModularSeamCoordinateMeasure

/-! Ordinary Euclidean gradient unfolding for compact tests crossing modular seams. -/

noncomputable section

namespace GapFamily.Analytic

open Set Filter MeasureTheory UpperHalfPlane ModularGradient
open scoped ContDiff

/-- The ordinary unweighted complex-coordinate mixed derivative density. -/
def modularMixedEuclideanPairing (F ψ : ℂ → ℂ) (z : ℂ) : ℂ :=
  star (fderiv ℝ F z 1) * fderiv ℝ ψ z 1 +
    star (fderiv ℝ F z Complex.I) * fderiv ℝ ψ z Complex.I

/-- Both real frame factors combine into exactly the square of the height. -/
theorem modularMixedFramePairing_eq_im_sq_smul (F ψ : ℂ → ℂ) (τ : UpperHalfPlane) :
    modularMixedFramePairing F ψ τ = τ.im ^ 2 • modularMixedEuclideanPairing F ψ τ := by
  simp only [modularMixedFramePairing, directional, modularMixedEuclideanPairing,
    star_mul, Complex.star_def, Complex.conj_ofReal, Complex.real_smul, Complex.ofReal_pow]
  ring

/-- The seed's derivative vanishes off its topological support. -/
theorem modularMixedEuclideanPairing_eq_zero_of_notMem_tsupport
    (F ψ : ℂ → ℂ) {z : ℂ} (hz : z ∉ tsupport ψ) :
    modularMixedEuclideanPairing F ψ z = 0 := by
  simp only [modularMixedEuclideanPairing, fderiv_of_notMem_tsupport ℝ hz,
    zero_apply, mul_zero, add_zero]

/-- The actual frame density becomes the ordinary Euclidean density, including
every seam; outside the seed's support both derivatives vanish. -/
theorem integral_modularMixedFramePairing_eq_euclideanIntegral
    (F ψ : ℂ → ℂ) (hs : tsupport ψ ⊆ upperHalfPlaneSet) :
    (∫ τ : UpperHalfPlane, modularMixedFramePairing F ψ τ ∂volume) =
      ∫ z : ℂ, modularMixedEuclideanPairing F ψ z := by
  have hupper : ∀ z ∈ tsupport ψ, 0 < z.im := fun z hz => hs hz
  calc
    _ = ∫ τ : UpperHalfPlane in UpperHalfPlane.coe ⁻¹' tsupport ψ,
        modularMixedFramePairing F ψ τ := by
      symm
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro τ hτ
      rw [modularMixedFramePairing_eq_im_sq_smul,
        modularMixedEuclideanPairing_eq_zero_of_notMem_tsupport F ψ hτ, smul_zero]
    _ = ∫ τ : UpperHalfPlane in UpperHalfPlane.coe ⁻¹' tsupport ψ,
        τ.im ^ 2 • modularMixedEuclideanPairing F ψ τ := by
      apply integral_congr_ae
      exact Eventually.of_forall fun τ => modularMixedFramePairing_eq_im_sq_smul F ψ τ
    _ = ∫ z : ℂ in tsupport ψ, modularMixedEuclideanPairing F ψ z :=
      (setIntegral_eq_upperHalfPlane_im_sq_smul (isClosed_tsupport ψ).measurableSet
        hupper (modularMixedEuclideanPairing F ψ)).symm
    _ = _ := setIntegral_eq_integral_of_forall_compl_eq_zero
      fun z hz => modularMixedEuclideanPairing_eq_zero_of_notMem_tsupport F ψ hz

/-- The unweighted Euclidean density is genuinely integrable on the entire
complex plane, even though the core is only smooth on the upper half-plane. -/
theorem modularMixedEuclideanPairing_integrable (F : smoothCore) {ψ : ℂ → ℂ}
    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    (hs : tsupport ψ ⊆ upperHalfPlaneSet) :
    Integrable (modularMixedEuclideanPairing F.val ψ) volume := by
  have hw : IntegrableOn (fun τ : UpperHalfPlane =>
      τ.im ^ 2 • modularMixedEuclideanPairing F.val ψ τ)
      (UpperHalfPlane.coe ⁻¹' tsupport ψ) := by
    apply (modularMixedFramePairing_upper_integrable F hψ hc hs).integrableOn.congr
    exact Eventually.of_forall fun τ => modularMixedFramePairing_eq_im_sq_smul F.val ψ τ
  have he := (integrableOn_upperHalfPlane_im_sq_smul_iff
    (isClosed_tsupport ψ).measurableSet (fun z hz => hs hz)
    (modularMixedEuclideanPairing F.val ψ)).mp hw
  exact he.integrable_of_forall_notMem_eq_zero
    fun z hz => modularMixedEuclideanPairing_eq_zero_of_notMem_tsupport F.val ψ hz

/-- Exact ordinary Euclidean unfolding of the actual core gradient pairing. -/
theorem inner_coreGradient_periodizedUpperCore_eq_euclideanIntegral
    (F : smoothCore) {ψ : ℂ → ℂ} (hψ : ContDiff ℝ ∞ ψ)
    (hc : HasCompactSupport ψ) (hs : tsupport ψ ⊆ upperHalfPlaneSet) :
    inner ℂ (coreGradient F) (coreGradient (periodizedUpperCore ψ hψ hc hs)) =
      ∫ z : ℂ, star (fderiv ℝ F.val z 1) * fderiv ℝ ψ z 1 +
        star (fderiv ℝ F.val z Complex.I) * fderiv ℝ ψ z Complex.I := by
  rw [inner_coreGradient_periodizedUpperCore F hψ hc hs,
    integral_modularMixedFramePairing_eq_euclideanIntegral F.val ψ hs]
  rfl

end GapFamily.Analytic
