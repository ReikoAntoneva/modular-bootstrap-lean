import GapFamily.Analytic.Modular.Periodization.ModularPeriodizationPairing

noncomputable section
namespace GapFamily.Analytic
open Set Filter MeasureTheory UpperHalfPlane ModularGradient
open scoped ContDiff

/-- The literal conjugate-linear/linear pairing of the two hyperbolic frame derivatives. -/
def modularMixedFramePairing (F ψ : ℂ → ℂ) (τ : UpperHalfPlane) : ℂ :=
  star (directional F 1 τ) * directional ψ 1 τ +
    star (directional F Complex.I τ) * directional ψ Complex.I τ

/-- Every real directional derivative of an actual smooth core is continuous on H. -/
theorem continuous_coreDirectional (F : smoothCore) (v : ℂ) :
    Continuous (directional F.val v) := by
  have hD : ContinuousOn (fun z => fderiv ℝ F.val z v) upperHalfPlaneSet :=
    (F.property.1.continuousOn_fderiv_of_isOpen isOpen_upperHalfPlaneSet (by simp)).clm_apply
      continuousOn_const
  exact (Complex.continuous_ofReal.comp UpperHalfPlane.continuous_im).mul
    (hD.comp_continuous UpperHalfPlane.continuous_coe (fun τ => τ.im_pos))

/-- The compact test mixed frame density is ordinarily integrable on the whole upper half-plane. -/
theorem modularMixedFramePairing_upper_integrable (F : smoothCore) {ψ : ℂ → ℂ}
    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    (hs : tsupport ψ ⊆ upperHalfPlaneSet) :
    Integrable (modularMixedFramePairing F.val ψ) volume := by
  have hψD (v : ℂ) : Continuous (directional ψ v) := by
    have hD : Continuous (fun z => fderiv ℝ ψ z v) :=
      (hψ.continuous_fderiv (by simp)).clm_apply continuous_const
    exact (Complex.continuous_ofReal.comp UpperHalfPlane.continuous_im).mul
      (hD.comp UpperHalfPlane.continuous_coe)
  have hg : Continuous (modularMixedFramePairing F.val ψ) :=
    ((continuous_coreDirectional F 1).star.mul (hψD 1)).add
      ((continuous_coreDirectional F Complex.I).star.mul (hψD Complex.I))
  have hK := compact_modular_support_preimage_of_upper_support hc hs
  have hsupport : tsupport (modularMixedFramePairing F.val ψ) ⊆
      UpperHalfPlane.coe ⁻¹' tsupport ψ := by
    apply closure_minimal
    · intro τ hτ
      by_contra hnot
      have hd := fderiv_of_notMem_tsupport ℝ hnot
      apply hτ
      simp [modularMixedFramePairing, directional, hd]
    · exact hK.isClosed
  exact hg.integrable_of_hasCompactSupport
    (hK.of_isClosed_subset (isClosed_tsupport _) hsupport)

/-- The literal directional pairing of actual core representatives is integrable on the modular tile. -/
theorem core_directionalPairing_integrable (F G : smoothCore) (v : ℂ)
    (hmem : ∀ H : smoothCore, MemLp (directional H.val v) 2 modularMeasure) :
    Integrable (fun τ => star (directional F.val v τ) * directional G.val v τ)
      modularMeasure := by
  apply (L2.integrable_inner (𝕜 := ℂ) (component v hmem F) (component v hmem G)).congr
  filter_upwards [component_ae v hmem F, component_ae v hmem G] with τ hF hG
  simp [hF, hG, RCLike.inner_apply, mul_comm]

/-- Both frame components give an ordinary integrable complex density. -/
theorem modularMixedFramePairing_core_integrable (F G : smoothCore) :
    Integrable (modularMixedFramePairing F.val G.val) modularMeasure :=
  (core_directionalPairing_integrable F G 1 (fun H => H.property.2.2.2.1)).add
    (core_directionalPairing_integrable F G Complex.I (fun H => H.property.2.2.2.2))

/-- An actual component Hilbert pairing uses its literal directional representatives. -/
theorem inner_component_eq_integral_directionalPairing (F G : smoothCore) (v : ℂ)
    (hmem : ∀ H : smoothCore, MemLp (directional H.val v) 2 modularMeasure) :
    inner ℂ (component v hmem F) (component v hmem G) =
      ∫ τ, star (directional F.val v τ) * directional G.val v τ ∂modularMeasure := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [component_ae v hmem F, component_ae v hmem G] with τ hF hG
  simp [hF, hG, RCLike.inner_apply, mul_comm]

/-- The actual Hilbert gradient pairing is the ordinary sum of the two frame pairings. -/
theorem inner_coreGradient_eq_integral_mixedFramePairing (F G : smoothCore) :
    inner ℂ (coreGradient F) (coreGradient G) =
      ∫ τ, modularMixedFramePairing F.val G.val τ ∂modularMeasure := by
  rw [WithLp.prod_inner_apply, coreGradient_fst, coreGradient_snd,
    coreGradient_fst, coreGradient_snd]
  change inner ℂ (component 1 (fun H => H.property.2.2.2.1) F)
      (component 1 (fun H => H.property.2.2.2.1) G) +
    inner ℂ (component Complex.I (fun H => H.property.2.2.2.2) F)
      (component Complex.I (fun H => H.property.2.2.2.2) G) = _
  rw [inner_component_eq_integral_directionalPairing,
    inner_component_eq_integral_directionalPairing,
    ← integral_add (core_directionalPairing_integrable F G 1 (fun H => H.property.2.2.2.1))
      (core_directionalPairing_integrable F G Complex.I (fun H => H.property.2.2.2.2))]
  rfl

end GapFamily.Analytic
