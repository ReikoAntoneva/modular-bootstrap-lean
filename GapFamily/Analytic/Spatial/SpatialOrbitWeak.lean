import GapFamily.Analytic.Spatial.SpatialPointKernelWeak
import GapFamily.Analytic.Spatial.SpatialOrbitCompactIntegral
import GapFamily.Analytic.Spatial.SpatialUpperTest
import GapFamily.Analytic.Spatial.SpatialOrbitContinuity

noncomputable section
namespace GapFamily.Analytic.SpatialPoint
open Set Filter MeasureTheory UpperHalfPlane LaplacianCovariance PoincareWeak
open scoped Topology ContDiff MatrixGroups

private theorem integral_mul_spatialOrbitPartial (s : ℂ) (w : UpperHalfPlane)
    (t : Finset (SL(2, ℤ))) (a : UpperHalfPlane → ℂ)
    (ha : Continuous a) (hc : HasCompactSupport a) :
    (∫ z : UpperHalfPlane, a z * spatialOrbitPartial s w t z) =
      (1 / 2 : ℂ) * ∑ γ ∈ t,
        ∫ z : UpperHalfPlane, a z * pointKernel s z (γ • w : UpperHalfPlane) := by
  have hi (γ : SL(2, ℤ)) : Integrable
      (fun z : UpperHalfPlane => a z * pointKernel s z (γ • w : UpperHalfPlane)) :=
    (ha.mul (continuous_pointKernel_left s (γ • w))).integrable_of_hasCompactSupport
      hc.mul_right
  calc
    _ = ∫ z : UpperHalfPlane, (1 / 2 : ℂ) *
        ∑ γ ∈ t, a z * pointKernel s z (γ • w : UpperHalfPlane) := by
      apply integral_congr_ae
      filter_upwards [] with z
      simp only [spatialOrbitPartial, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro γ hγ
      ring
    _ = _ := by
      rw [integral_const_mul, integral_finsetSum t (fun γ hγ => hi γ)]

/-- All three compact-test terms in the orbit recurrence are genuinely integrable. -/
theorem spatialOrbitKernel_weak_integrable (s : ℂ) (hs : 1 < s.re)
    (w : UpperHalfPlane) (ψ : ℂ → ℂ) (hψ : ContDiff ℝ ∞ ψ)
    (hc : HasCompactSupport ψ) (hupper : tsupport ψ ⊆ upperHalfPlaneSet) :
    Integrable (fun z : UpperHalfPlane => star (ordinaryHyperbolicLaplacian ψ z) *
        spatialOrbitKernel s z w) volume ∧
      Integrable (fun z : UpperHalfPlane => star (ψ z) * spatialOrbitKernel s z w) volume ∧
      Integrable (fun z : UpperHalfPlane => star (ψ z) * spatialOrbitKernel (s + 1) z w) volume := by
  have ha := ((ordinaryHyperbolicLaplacian_continuous hψ).comp continuous_coe).star
  have hb := (hψ.continuous.comp continuous_coe).star
  have hca := (hasCompactSupport_upper_laplacian_test hc hupper).comp_left (star_zero ℂ)
  have hcb := (hasCompactSupport_upper_restrict hc hupper).comp_left (star_zero ℂ)
  have hs' : 1 < (s + 1).re := by simp only [Complex.add_re, Complex.one_re]; linarith
  exact ⟨integrable_mul_spatialOrbitKernel s hs w _ ha hca,
    integrable_mul_spatialOrbitKernel s hs w _ hb hcb,
    integrable_mul_spatialOrbitKernel (s + 1) hs' w _ hb hcb⟩

/-- The literal normalized orbit kernel satisfies the prescribed recurrence in
ordinary compact-test integrals throughout its actual convergence half-plane. -/
theorem integral_spatialOrbitKernel_weak_recurrence (s : ℂ) (hs : 1 < s.re)
    (w : UpperHalfPlane) (ψ : ℂ → ℂ) (hψ : ContDiff ℝ ∞ ψ)
    (hc : HasCompactSupport ψ) (hupper : tsupport ψ ⊆ upperHalfPlaneSet) :
    (∫ z : UpperHalfPlane, star (ordinaryHyperbolicLaplacian ψ z) *
        spatialOrbitKernel s z w) -
      s * (1 - s) * (∫ z : UpperHalfPlane, star (ψ z) * spatialOrbitKernel s z w) =
      s ^ 2 * (∫ z : UpperHalfPlane, star (ψ z) * spatialOrbitKernel (s + 1) z w) := by
  let a : UpperHalfPlane → ℂ := fun z => star (ordinaryHyperbolicLaplacian ψ z)
  let b : UpperHalfPlane → ℂ := fun z => star (ψ z)
  have ha : Continuous a :=
    ((ordinaryHyperbolicLaplacian_continuous hψ).comp continuous_coe).star
  have hb : Continuous b := (hψ.continuous.comp continuous_coe).star
  have hca : HasCompactSupport a :=
    (hasCompactSupport_upper_laplacian_test hc hupper).comp_left (star_zero ℂ)
  have hcb : HasCompactSupport b :=
    (hasCompactSupport_upper_restrict hc hupper).comp_left (star_zero ℂ)
  have hfinite (t : Finset (SL(2, ℤ))) :
      (∫ z : UpperHalfPlane, a z * spatialOrbitPartial s w t z) -
        s * (1 - s) * (∫ z : UpperHalfPlane, b z * spatialOrbitPartial s w t z) =
        s ^ 2 * (∫ z : UpperHalfPlane, b z * spatialOrbitPartial (s + 1) w t z) := by
    rw [integral_mul_spatialOrbitPartial s w t a ha hca,
      integral_mul_spatialOrbitPartial s w t b hb hcb,
      integral_mul_spatialOrbitPartial (s + 1) w t b hb hcb]
    have he : (∑ γ ∈ t,
        ((∫ z : UpperHalfPlane, a z * pointKernel s z (γ • w : UpperHalfPlane)) -
          s * (1 - s) * (∫ z : UpperHalfPlane, b z * pointKernel s z (γ • w : UpperHalfPlane)))) =
        ∑ γ ∈ t, s ^ 2 *
          (∫ z : UpperHalfPlane, b z * pointKernel (s + 1) z (γ • w : UpperHalfPlane)) := by
      apply Finset.sum_congr rfl
      intro γ hγ
      exact integral_pointKernel_weak_recurrence s (γ • w) ψ hψ hc hupper
    simp only [Finset.sum_sub_distrib, ← Finset.mul_sum] at he
    linear_combination (1 / 2 : ℂ) * he
  have hL := (tendsto_integral_mul_spatialOrbitPartial s hs w a ha hca).sub
    ((tendsto_integral_mul_spatialOrbitPartial s hs w b hb hcb).const_mul (s * (1 - s)))
  have hs' : 1 < (s + 1).re := by simp only [Complex.add_re, Complex.one_re]; linarith
  have hR := (tendsto_integral_mul_spatialOrbitPartial (s + 1) hs' w b hb hcb).const_mul (s ^ 2)
  exact tendsto_nhds_unique hL (hR.congr' (Eventually.of_forall (fun t => (hfinite t).symm)))

end GapFamily.Analytic.SpatialPoint
