import GapFamily.Analytic.Spatial.SpatialOrbitWeightedSource
import GapFamily.Analytic.Spatial.SpatialOrbitFirstBound
import GapFamily.Analytic.Elliptic.C1ModularForm

noncomputable section
namespace GapFamily.Analytic.SpatialPoint
open Set Filter MeasureTheory UpperHalfPlane ModularGradient
open scoped Topology ContDiff MatrixGroups

/-- The actual unweighted point source, using the proved zero-weight specialization. -/
def spatialOrbitPointSource (s : ℂ) (w : UpperHalfPlane) : ModularHilbert :=
  spatialOrbitWeightedSource 0 (by norm_num) (by norm_num) s w

/-- In the original convergence half-plane the vector has its literal orbit-kernel representative. -/
theorem spatialOrbitPointSource_ae (s : ℂ) (hs : 1 < s.re) (w : UpperHalfPlane) :
    spatialOrbitPointSource s w =ᵐ[modularMeasure]
      (fun z : UpperHalfPlane => spatialOrbitKernel s z w) := by
  simpa only [spatialOrbitPointSource, Real.rpow_zero, Complex.ofReal_one, one_mul] using
    spatialOrbitWeightedSource_ae 0 (by norm_num) (by norm_num) s hs w

/-- The literal complex orbit point source has genuine finite modular L² norm. -/
theorem memLp_spatialOrbitKernel (s : ℂ) (hs : 1 < s.re) (w : UpperHalfPlane) :
    MemLp (fun z : UpperHalfPlane => spatialOrbitKernel s z w) 2 modularMeasure := by
  simpa only [Real.rpow_zero, Complex.ofReal_one, one_mul] using
    memLp_spatialOrbitKernel_weighted 0 (by norm_num) (by norm_num) s hs w

private theorem continuous_spatialOrbitPointFrame (s : ℂ) (hs : 1 < s.re)
    (w : UpperHalfPlane) (v : ℂ) :
    Continuous (directional (fun z : ℂ => spatialOrbitKernel s (ofComplex z) w) v) := by
  have hD := (contDiffOn_spatialOrbitKernel_left s hs w).continuousOn_fderiv_of_isOpen
    isOpen_upperHalfPlaneSet (by simp)
  have hDc : Continuous (fun z : UpperHalfPlane =>
      fderiv ℝ (fun u : ℂ => spatialOrbitKernel s (ofComplex u) w) z) :=
    hD.comp_continuous UpperHalfPlane.continuous_coe (fun z => z.im_pos)
  exact (Complex.continuous_ofReal.comp UpperHalfPlane.continuous_im).mul
    (hDc.clm_apply continuous_const)

/-- Every actual frame direction has finite energy for every complex exponent with real part above one. -/
theorem memLp_spatialOrbitPointFrame (s : ℂ) (hs : 1 < s.re)
    (w : UpperHalfPlane) (v : ℂ) :
    MemLp (directional (fun z : ℂ => spatialOrbitKernel s (ofComplex z) w) v)
      2 modularMeasure := by
  apply ((memLp_spatialOrbitKernel (s.re : ℂ) (by simpa using hs) w).norm.const_mul (‖s‖ * ‖v‖)).mono'
    (continuous_spatialOrbitPointFrame s hs w v).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun z => by
    rw [directional, norm_mul, Complex.norm_of_nonneg z.im_pos.le]
    calc
      _ ≤ z.im * (‖fderiv ℝ (fun u : ℂ => spatialOrbitKernel s (ofComplex u) w) z‖ * ‖v‖) :=
        mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ v) z.im_pos.le
      _ = (z.im * ‖fderiv ℝ (fun u : ℂ => spatialOrbitKernel s (ofComplex u) w) z‖) * ‖v‖ := by ring
      _ ≤ (‖s‖ * ‖spatialOrbitKernel (s.re : ℂ) z w‖) * ‖v‖ :=
        mul_le_mul_of_nonneg_right (spatialOrbitKernel_frame_fderiv_norm_le s hs z w) (norm_nonneg _)
      _ = _ := by ring

/-- The literal complex point source belongs to the original closed-gradient form domain,
with both actual frame derivatives identified. -/
theorem exists_spatialOrbitPointForm (s : ℂ) (hs : 1 < s.re) (w : UpperHalfPlane) :
    ∃ u : FormDomain,
      formEmbedding u = spatialOrbitPointSource s w ∧
      (WithLp.ofLp (formGradient u)).1 =ᵐ[modularMeasure]
        directional (fun z : ℂ => spatialOrbitKernel s (ofComplex z) w) 1 ∧
      (WithLp.ofLp (formGradient u)).2 =ᵐ[modularMeasure]
        directional (fun z : ℂ => spatialOrbitKernel s (ofComplex z) w) Complex.I := by
  have hv : MemLp (fun z : UpperHalfPlane => spatialOrbitKernel s (ofComplex (z : ℂ)) w)
      2 modularMeasure := by
    simpa only [UpperHalfPlane.ofComplex_apply] using memLp_spatialOrbitKernel s hs w
  obtain ⟨u, hu, hx, hy⟩ := C1ModularForm.exists_form_of_C1
    (fun z : ℂ => spatialOrbitKernel s (ofComplex z) w)
    (contDiffOn_spatialOrbitKernel_left s hs w)
    (fun γ z => by simpa only [UpperHalfPlane.ofComplex_apply] using
      spatialOrbitKernel_modular_left s γ z w)
    hv (memLp_spatialOrbitPointFrame s hs w 1) (memLp_spatialOrbitPointFrame s hs w Complex.I)
  refine ⟨u, ?_, ?_, ?_⟩
  · rw [hu]
    apply Lp.ext
    have hraw : hv.toLp (fun z : UpperHalfPlane => spatialOrbitKernel s (ofComplex (z : ℂ)) w) =ᵐ[modularMeasure]
        (fun z : UpperHalfPlane => spatialOrbitKernel s z w) := by
      simpa only [UpperHalfPlane.ofComplex_apply] using hv.coeFn_toLp
    exact hraw.trans (spatialOrbitPointSource_ae s hs w).symm
  · rw [hx]
    exact MemLp.coeFn_toLp _
  · rw [hy]
    exact MemLp.coeFn_toLp _

/-- Domain membership is established for the concrete source vector, without a form-domain premise. -/
theorem spatialOrbitPointSource_mem_closedGradient_domain (s : ℂ) (hs : 1 < s.re)
    (w : UpperHalfPlane) : spatialOrbitPointSource s w ∈ closedGradient.domain := by
  obtain ⟨u, hu, _, _⟩ := exists_spatialOrbitPointForm s hs w
  rw [← hu]
  exact Dirichlet.gradientEmbedding_mem_domain closedGradient u

end GapFamily.Analytic.SpatialPoint
