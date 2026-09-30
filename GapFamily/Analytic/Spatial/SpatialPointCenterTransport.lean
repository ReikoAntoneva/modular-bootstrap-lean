import GapFamily.Analytic.Spatial.SpatialPointKernelTest

noncomputable section
namespace GapFamily.Analytic.SpatialPoint
open MeasureTheory UpperHalfPlane Matrix
open scoped MatrixGroups BoundedContinuousFunction

/-- Pull back a bounded continuous test by the actual real modular map sending I to z. -/
def pointPullback (z : UpperHalfPlane) (f : UpperHalfPlane →ᵇ ℂ) : UpperHalfPlane →ᵇ ℂ :=
  f.compContinuous ⟨fun w => (z.toSL2R : GL (Fin 2) ℝ) • w, continuous_const_smul _⟩

theorem pointPullback_apply (z w : UpperHalfPlane) (f : UpperHalfPlane →ᵇ ℂ) :
    pointPullback z f w = f ((z.toSL2R : GL (Fin 2) ℝ) • w) := rfl

theorem pointPullback_at_I (z : UpperHalfPlane) (f : UpperHalfPlane →ᵇ ℂ) :
    pointPullback z f UpperHalfPlane.I = f z := by
  have hact : ((z.toSL2R : GL (Fin 2) ℝ) • UpperHalfPlane.I : UpperHalfPlane) =
      z.toSL2R • UpperHalfPlane.I := by
    apply UpperHalfPlane.ext
    rfl
  rw [pointPullback_apply, hact, UpperHalfPlane.toSL2R_smul_I]

/-- Whole-hyperbolic-volume invariance transports the literal tested kernel between centers. -/
theorem integral_pointKernel_test_move (s : ℝ) (z : UpperHalfPlane) (F : UpperHalfPlane → ℂ) :
    (∫ w : UpperHalfPlane, pointKernel (s : ℂ) z w * F w) =
      ∫ w : UpperHalfPlane, pointKernel (s : ℂ) UpperHalfPlane.I w * F ((z.toSL2R : GL (Fin 2) ℝ) • w) := by
  let γ : GL (Fin 2) ℝ := z.toSL2R
  have heq (w : UpperHalfPlane) : pointKernel (s : ℂ) z (γ • w : UpperHalfPlane) =
      pointKernel (s : ℂ) UpperHalfPlane.I w := by
    change pointKernel (s : ℂ) z (z.toSL2R • w : UpperHalfPlane) = _
    simpa only [UpperHalfPlane.toSL2R_smul_I] using
      pointKernel_smul (s : ℂ) z.toSL2R UpperHalfPlane.I w
  have h := integral_smul_eq_self (G := GL (Fin 2) ℝ) (μ := (volume : Measure UpperHalfPlane))
    (g := γ) (fun w : UpperHalfPlane => pointKernel (s : ℂ) z w * F w)
  simpa only [heq] using h.symm

/-- The actual normalized average obeys the same center transport. Ordinary convergence
for s>1 is established by the bounded-test integrability theorem. -/
theorem pointAverage_move (s : ℝ) (z : UpperHalfPlane) (f : UpperHalfPlane →ᵇ ℂ) :
    pointAverage s z f = pointAverage s UpperHalfPlane.I (pointPullback z f) := by
  unfold pointAverage
  rw [integral_pointKernel_test_move]
  rfl

end GapFamily.Analytic.SpatialPoint
