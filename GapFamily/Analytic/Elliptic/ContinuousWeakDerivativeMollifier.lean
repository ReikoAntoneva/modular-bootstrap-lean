import GapFamily.Analytic.Elliptic.WeakLaplacianMollifier

noncomputable section
namespace GapFamily.Analytic
open Set Filter MeasureTheory ContinuousLinearMap
open scoped ContDiff Convolution Topology

/-- A literal compact-test weak gradient becomes the actual derivative of a
smooth convolution wherever its reflected kernel is an admissible test. -/
theorem hasFDerivAt_convolution_of_weak_gradient
    {f : ℂ → ℂ} {G : ℂ → (ℂ →L[ℝ] ℂ)}
    (hf : LocallyIntegrable f volume) (hG : LocallyIntegrable G volume)
    {U : Set ℂ}
    (hweak : ∀ ψ : ℂ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ U → ∀ v : ℂ,
      (∫ t : ℂ, fderiv ℝ ψ t v • f t) = -(∫ t : ℂ, ψ t • G t v))
    {η : ℂ → ℝ} (hη : ContDiff ℝ ∞ η) (hc : HasCompactSupport η)
    (y : ℂ) (hs : tsupport (fun t => η (y - t)) ⊆ U) :
    HasFDerivAt (η ⋆[lsmul ℝ ℝ, volume] f)
      ((η ⋆[lsmul ℝ ℝ, volume] G) y) y := by
  let L : ℂ →L[ℝ] ℝ →L[ℝ] ℂ := (lsmul ℝ ℝ).flip
  have hd := hc.hasFDerivAt_convolution_right L hf (hη.of_le (by simp)) y
  have hi : Integrable (fun t : ℂ => η (y - t) • G t) volume :=
    hc.convolutionExists_right (lsmul ℝ ℝ).flip hG hη.continuous y
  have hev (v : ℂ) : ((η ⋆[lsmul ℝ ℝ, volume] G) y) v =
      ∫ t : ℂ, η (y - t) • G t v := by
    rw [← convolution_flip]
    change (∫ t : ℂ, η (y - t) • G t) v = _
    rw [ContinuousLinearMap.integral_apply hi]
    rfl
  have hD : (f ⋆[L.precompR ℂ, volume] fderiv ℝ η) y =
      (η ⋆[lsmul ℝ ℝ, volume] G) y := by
    apply ContinuousLinearMap.ext
    intro v
    rw [convolution_precompR_apply L hf (hc.fderiv ℝ)
      (hη.continuous_fderiv (by simp)), hev]
    have hw := hweak (fun t => η (y - t)) (contDiff_reflected_kernel hη y)
      (hasCompactSupport_reflected_kernel hc y) hs v
    simp_rw [fderiv_reflected_kernel hη, neg_smul] at hw
    rw [integral_neg] at hw
    exact neg_injective hw
  rw [hD] at hd
  simpa only [L, convolution_flip] using hd

end GapFamily.Analytic
