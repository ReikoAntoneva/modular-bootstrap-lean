import GapFamily.Analytic.Cusp.Green.CuspGreenThreshold
import GapFamily.Analytic.Cusp.Green.CuspGreenSolutionAnalytic
import GapFamily.Analytic.Cusp.Green.CuspGreenTrace

/-!
# Prescribed boundary data for the scalar cusp response

An explicit homogeneous exponential lifts the boundary value of the actual
compact-source Green integral. All differential statements concern the
physical interior; positive real part of the parameter supplies outgoing decay.
-/

noncomputable section

namespace GapFamily.Analytic

open Filter Set
open scoped Topology

/-- The scalar outgoing mode with prescribed value at the boundary. -/
def cuspBoundaryMode (t₀ : ℝ) (κ g : ℂ) (t : ℝ) : ℂ :=
  g * Complex.exp (-κ * ((t - t₀ : ℝ) : ℂ))

/-- The actual Green response with the prescribed boundary value added. -/
def cuspGreenBoundarySolution (t₀ : ℝ) (κ g : ℂ) (f : ℝ → ℂ) (t : ℝ) : ℂ :=
  cuspGreenSolution t₀ κ f t + cuspBoundaryMode t₀ κ g t

@[simp] theorem cuspBoundaryMode_boundary (t₀ : ℝ) (κ g : ℂ) :
    cuspBoundaryMode t₀ κ g t₀ = g := by
  simp [cuspBoundaryMode]

/-- The boundary mode is an actual globally differentiable exponential. -/
theorem hasDerivAt_cuspBoundaryMode (t₀ : ℝ) (κ g : ℂ) (t : ℝ) :
    HasDerivAt (cuspBoundaryMode t₀ κ g) (-κ * cuspBoundaryMode t₀ κ g t) t := by
  have hd := (((Complex.hasDerivAt_exp _).comp (t : ℂ)
    (((hasDerivAt_id (t : ℂ)).sub_const (t₀ : ℂ)).const_mul (-κ))).const_mul g).comp_ofReal
  unfold cuspBoundaryMode
  simp only [Complex.ofReal_sub]
  apply hd.congr_deriv
  dsimp only [id_eq]
  ring

theorem cuspBoundaryMode_continuous (t₀ : ℝ) (κ g : ℂ) :
    Continuous (cuspBoundaryMode t₀ κ g) := by
  unfold cuspBoundaryMode
  fun_prop

@[simp] theorem cuspGreenBoundarySolution_boundary (t₀ : ℝ) (κ g : ℂ) (f : ℝ → ℂ) :
    cuspGreenBoundarySolution t₀ κ g f t₀ = g := by
  simp [cuspGreenBoundarySolution]

/-- The actual lifted solution has a continuous boundary trace. -/
theorem cuspGreenBoundarySolution_continuousWithinAt_boundary {f : ℝ → ℂ}
    (hf : Continuous f) (hfc : HasCompactSupport f) (t₀ : ℝ) (κ g : ℂ) :
    ContinuousWithinAt (cuspGreenBoundarySolution t₀ κ g f) (Ici t₀) t₀ :=
  (cuspGreenSolution_continuousWithinAt_boundary_all hf hfc t₀ κ).add
    (cuspBoundaryMode_continuous t₀ κ g).continuousAt.continuousWithinAt

/-- The prescribed boundary value is the actual right-hand limit. -/
theorem cuspGreenBoundarySolution_tendsto_boundary {f : ℝ → ℂ}
    (hf : Continuous f) (hfc : HasCompactSupport f) (t₀ : ℝ) (κ g : ℂ) :
    Tendsto (cuspGreenBoundarySolution t₀ κ g f) (𝓝[>] t₀) (𝓝 g) := by
  have hc := (cuspGreenBoundarySolution_continuousWithinAt_boundary hf hfc t₀ κ g).mono
    Ioi_subset_Ici_self
  simpa only [ContinuousWithinAt, cuspGreenBoundarySolution_boundary] using hc

/-- The inward boundary derivative is the source trace minus the homogeneous response. -/
theorem hasDerivWithinAt_cuspGreenBoundarySolution_boundary {f : ℝ → ℂ}
    (hf : Continuous f) (hfc : HasCompactSupport f) (t₀ : ℝ) (κ g : ℂ) :
    HasDerivWithinAt (cuspGreenBoundarySolution t₀ κ g f)
      (cuspGreenBoundaryTrace t₀ κ f - κ * g) (Ici t₀) t₀ := by
  apply ((hasDerivWithinAt_cuspGreenSolution_boundary hf hfc t₀ κ).add
    (hasDerivAt_cuspBoundaryMode t₀ κ g t₀).hasDerivWithinAt).congr_deriv
  rw [cuspBoundaryMode_boundary]
  ring

/-- The Dirichlet-to-inward-derivative formula uses the actual within derivative. -/
theorem derivWithin_cuspGreenBoundarySolution_boundary {f : ℝ → ℂ}
    (hf : Continuous f) (hfc : HasCompactSupport f) (t₀ : ℝ) (κ g : ℂ) :
    derivWithin (cuspGreenBoundarySolution t₀ κ g f) (Ici t₀) t₀ =
      cuspGreenBoundaryTrace t₀ κ f - κ * g :=
  (hasDerivWithinAt_cuspGreenBoundarySolution_boundary hf hfc t₀ κ g).derivWithin
    (uniqueDiffWithinAt_Ici t₀)

/-- The first derivative includes the actual homogeneous boundary correction. -/
theorem hasDerivAt_cuspGreenBoundarySolution {f : ℝ → ℂ}
    (hf : Continuous f) (hfc : HasCompactSupport f) (t₀ : ℝ) (κ g : ℂ)
    {t : ℝ} (ht : t₀ < t) :
    HasDerivAt (cuspGreenBoundarySolution t₀ κ g f)
      (deriv (cuspGreenSolution t₀ κ f) t - κ * cuspBoundaryMode t₀ κ g t) t := by
  apply ((cuspGreenSolution_differentiableAt_all hf hfc t₀ κ ht).hasDerivAt.add
    (hasDerivAt_cuspBoundaryMode t₀ κ g t)).congr_deriv
  ring

/-- The second derivative belongs to the actual response with its boundary lift. -/
theorem hasDerivAt_deriv_cuspGreenBoundarySolution {f : ℝ → ℂ}
    (hf : Continuous f) (hfc : HasCompactSupport f) (t₀ : ℝ) (κ g : ℂ)
    {t : ℝ} (ht : t₀ < t) :
    HasDerivAt (deriv (cuspGreenBoundarySolution t₀ κ g f))
      (κ ^ 2 * cuspGreenBoundarySolution t₀ κ g f t - f t) t := by
  have heq : deriv (cuspGreenBoundarySolution t₀ κ g f) =ᶠ[𝓝 t]
      (fun v => deriv (cuspGreenSolution t₀ κ f) v - κ * cuspBoundaryMode t₀ κ g v) := by
    filter_upwards [Ioi_mem_nhds ht] with v hv
    exact (hasDerivAt_cuspGreenBoundarySolution hf hfc t₀ κ g hv).deriv
  have hd := (hasDerivAt_deriv_cuspGreenSolution_all hf hfc t₀ κ ht).sub
    ((hasDerivAt_cuspBoundaryMode t₀ κ g t).const_mul κ)
  apply (hd.congr_of_eventuallyEq heq).congr_deriv
  unfold cuspGreenBoundarySolution
  ring

/-- The lift preserves the actual forced equation for every complex parameter. -/
theorem cuspGreenBoundarySolution_forcedODE {f : ℝ → ℂ}
    (hf : Continuous f) (hfc : HasCompactSupport f) (t₀ : ℝ) (κ g : ℂ)
    {t : ℝ} (ht : t₀ < t) :
    -deriv (deriv (cuspGreenBoundarySolution t₀ κ g f)) t +
      κ ^ 2 * cuspGreenBoundarySolution t₀ κ g f t = f t := by
  rw [(hasDerivAt_deriv_cuspGreenBoundarySolution hf hfc t₀ κ g ht).deriv]
  ring

/-- The boundary lift is outgoing whenever the parameter has positive real part. -/
theorem cuspBoundaryMode_tendsto_zero (t₀ : ℝ) {κ : ℂ} (hκ : 0 < κ.re) (g : ℂ) :
    Tendsto (cuspBoundaryMode t₀ κ g) atTop (𝓝 0) := by
  have h := ((cusp_outgoing_exp_tendsto_zero hκ).mul_const
    (Complex.exp (κ * (t₀ : ℂ)))).const_mul g
  simp only [zero_mul, mul_zero] at h
  apply h.congr
  intro t
  unfold cuspBoundaryMode
  rw [Complex.ofReal_sub, show -κ * ((t : ℂ) - t₀) = -κ * t + κ * t₀ by ring,
    Complex.exp_add]

/-- The actual compact-source response with prescribed data has outgoing decay. -/
theorem cuspGreenBoundarySolution_tendsto_zero {f : ℝ → ℂ} (hfc : HasCompactSupport f)
    (t₀ : ℝ) {κ : ℂ} (hκ : 0 < κ.re) (g : ℂ) :
    Tendsto (cuspGreenBoundarySolution t₀ κ g f) atTop (𝓝 0) := by
  unfold cuspGreenBoundarySolution
  simpa only [add_zero] using
    (cuspGreenSolution_tendsto_zero hfc t₀ hκ).add (cuspBoundaryMode_tendsto_zero t₀ hκ g)

/-- The actual boundary-value response is entire at every physical position. -/
theorem differentiable_cuspGreenBoundarySolution_parameter (t₀ t : ℝ) (ht : t₀ ≤ t)
    (g : ℂ) {f : ℝ → ℂ} (hf : Continuous f) (hfc : HasCompactSupport f) :
    Differentiable ℂ (fun κ => cuspGreenBoundarySolution t₀ κ g f t) := by
  have hm : Differentiable ℂ (fun κ => cuspBoundaryMode t₀ κ g t) := by
    unfold cuspBoundaryMode
    fun_prop
  exact (differentiable_cuspGreenSolution_parameter t₀ t ht hf hfc).add hm

/-- Holomorphy of the prescribed-data response includes the threshold. -/
theorem analyticAt_cuspGreenBoundarySolution_parameter (t₀ t : ℝ) (ht : t₀ ≤ t)
    (g : ℂ) {f : ℝ → ℂ} (hf : Continuous f) (hfc : HasCompactSupport f) (κ : ℂ) :
    AnalyticAt ℂ (fun z => cuspGreenBoundarySolution t₀ z g f t) κ :=
  (differentiable_cuspGreenBoundarySolution_parameter t₀ t ht g hf hfc).analyticAt κ

end GapFamily.Analytic
