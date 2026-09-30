import GapFamily.Analytic.Spatial.SpatialOrbitContinuity
import GapFamily.Analytic.Foundation.CompactTestUniformIntegral

/-!
The actual normalized orbit partial sums converge uniformly on every compact
spatial region, and hence converge against arbitrary continuous compact tests in
the whole upper-half-plane hyperbolic volume.
-/

noncomputable section
namespace GapFamily.Analytic.SpatialPoint
open Set Filter UpperHalfPlane MeasureTheory
open scoped Topology Uniformity MatrixGroups

/-- Literal finite matrix-orbit sums with the fixed central-pair normalization. -/
def spatialOrbitPartial (s : ℂ) (w : UpperHalfPlane) (t : Finset (SL(2, ℤ)))
    (z : UpperHalfPlane) : ℂ :=
  (1 / 2 : ℂ) * ∑ γ ∈ t, pointKernel s z (γ • w : UpperHalfPlane)

theorem continuous_spatialOrbitPartial (s : ℂ) (w : UpperHalfPlane)
    (t : Finset (SL(2, ℤ))) : Continuous (spatialOrbitPartial s w t) := by
  apply continuous_const.mul
  exact continuous_finsetSum t (fun γ _ => continuous_pointKernel_left s (γ • w))

/-- The normalized finite sums converge locally uniformly in the first point. -/
theorem tendstoLocallyUniformly_spatialOrbitPartial (s : ℂ) (hs : 1 < s.re)
    (w : UpperHalfPlane) :
    TendstoLocallyUniformly (spatialOrbitPartial s w)
      (fun z => spatialOrbitKernel s z w) atTop := by
  have hraw : TendstoLocallyUniformly
      (fun t : Finset (SL(2, ℤ)) => fun z : UpperHalfPlane =>
        ∑ γ ∈ t, pointKernel s z (γ • w : UpperHalfPlane))
      (fun z => ∑' γ : SL(2, ℤ), pointKernel s z (γ • w : UpperHalfPlane)) atTop := by
    intro V hV z₀
    obtain ⟨U, hU, hconv⟩ := exists_pointKernel_orbit_tendstoUniformlyOn s hs z₀ w
    let g : UpperHalfPlane → ℂ × (UpperHalfPlane × UpperHalfPlane) := fun z => (s, (z, w))
    have hg : Continuous g := continuous_const.prodMk (continuous_id.prodMk continuous_const)
    refine ⟨g ⁻¹' U, hg.continuousAt hU, ?_⟩
    exact (hconv V hV).mono (fun t ht z hz => ht (g z) hz)
  have hc : UniformContinuous (fun x : ℂ => (1 / 2 : ℂ) * x) :=
    ((1 / 2 : ℂ) • (ContinuousLinearMap.id ℂ ℂ)).uniformContinuous
  change TendstoLocallyUniformly
    (fun t : Finset (SL(2, ℤ)) => fun z : UpperHalfPlane =>
      (1 / 2 : ℂ) * ∑ γ ∈ t, pointKernel s z (γ • w : UpperHalfPlane)) _ atTop
  simpa only [Function.comp_def, spatialOrbitKernel_eq_half_tsum_right] using
    hc.comp_tendstoLocallyUniformly hraw

/-- Uniform convergence holds on every actual compact subset of the upper half-plane. -/
theorem tendstoUniformlyOn_spatialOrbitPartial (s : ℂ) (hs : 1 < s.re)
    (w : UpperHalfPlane) {K : Set UpperHalfPlane} (hK : IsCompact K) :
    TendstoUniformlyOn (spatialOrbitPartial s w)
      (fun z => spatialOrbitKernel s z w) atTop K :=
  (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hK).mp
    (tendstoLocallyUniformly_spatialOrbitPartial s hs w).tendstoLocallyUniformlyOn

theorem integrable_mul_spatialOrbitPartial (s : ℂ) (w : UpperHalfPlane)
    (t : Finset (SL(2, ℤ))) (a : UpperHalfPlane → ℂ) (ha : Continuous a)
    (hc : HasCompactSupport a) :
    Integrable (fun z => a z * spatialOrbitPartial s w t z) volume :=
  (ha.mul (continuous_spatialOrbitPartial s w t)).integrable_of_hasCompactSupport hc.mul_right

theorem integrable_mul_spatialOrbitKernel (s : ℂ) (hs : 1 < s.re)
    (w : UpperHalfPlane) (a : UpperHalfPlane → ℂ) (ha : Continuous a)
    (hc : HasCompactSupport a) :
    Integrable (fun z => a z * spatialOrbitKernel s z w) volume := by
  have hg : Continuous (fun z : UpperHalfPlane => (z, w)) :=
    continuous_id.prodMk continuous_const
  have hk := (continuous_spatialOrbitKernel s hs).comp hg
  exact (ha.mul hk).integrable_of_hasCompactSupport hc.mul_right

/-- Every continuous compact test pairs with the actual normalized finite sums
in the limit, using the whole upper-half-plane hyperbolic volume. -/
theorem tendsto_integral_mul_spatialOrbitPartial (s : ℂ) (hs : 1 < s.re)
    (w : UpperHalfPlane) (a : UpperHalfPlane → ℂ) (ha : Continuous a)
    (hc : HasCompactSupport a) :
    Tendsto (fun t : Finset (SL(2, ℤ)) =>
      ∫ z : UpperHalfPlane, a z * spatialOrbitPartial s w t z ∂volume)
      atTop (𝓝 (∫ z : UpperHalfPlane, a z * spatialOrbitKernel s z w ∂volume)) := by
  let : Countable (SL(2, ℤ)) := by
    have : Countable (Matrix (Fin 2) (Fin 2) ℤ) := by
      change Countable (Fin 2 → Fin 2 → ℤ)
      infer_instance
    change Countable {A : Matrix (Fin 2) (Fin 2) ℤ // A.det = 1}
    infer_instance
  have hg : Continuous (fun z : UpperHalfPlane => (z, w)) :=
    continuous_id.prodMk continuous_const
  have hf := (continuous_spatialOrbitKernel s hs).comp hg
  have hunif := tendstoUniformlyOn_spatialOrbitPartial s hs w hc
  exact tendsto_integral_compactTest_of_tendstoUniformlyOn
    (μ := (volume : Measure UpperHalfPlane)) (l := atTop)
    (F := spatialOrbitPartial s w) (f := fun z => spatialOrbitKernel s z w) (a := a)
    (continuous_spatialOrbitPartial s w) hf ha hc hunif

end GapFamily.Analytic.SpatialPoint
