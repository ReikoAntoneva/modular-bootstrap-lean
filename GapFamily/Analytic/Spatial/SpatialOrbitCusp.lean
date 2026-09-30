import GapFamily.Analytic.Spatial.SpatialCuspMatrixEquiv
import GapFamily.Analytic.Spatial.SpatialCuspTranslation
import GapFamily.Analytic.Spatial.SpatialOrbitSummable

noncomputable section
namespace GapFamily.Analytic.SpatialPoint

open scoped MatrixGroups

/-- Full matrices parametrized by a cusp coset, integer translation, and central sign. -/
def signedCuspOrbitEquiv : CuspCoset × (ℤ × Bool) ≃ SL(2, ℤ) :=
  (Equiv.prodCongr (Equiv.refl _) cuspTranslationEquiv).trans cuspMatrixEquiv

theorem signedCuspOrbitEquiv_smul (q : CuspCoset) (n : ℤ) (b : Bool)
    (z : UpperHalfPlane) :
    signedCuspOrbitEquiv (q, n, b) • z = ModularGroup.T ^ n • (q.out • z) := by
  change ((cuspTranslationEquiv (n, b) : SL(2, ℤ)) * q.out) • z = _
  rw [mul_smul, cuspTranslationEquiv_smul]

@[simp] theorem signedCuspOrbitEquiv_smul_apply (p : CuspCoset × (ℤ × Bool))
    (z : UpperHalfPlane) :
    signedCuspOrbitEquiv p • z = ModularGroup.T ^ p.2.1 • (p.1.out • z) := by
  rcases p with ⟨q, n, b⟩
  exact signedCuspOrbitEquiv_smul q n b z

theorem summable_norm_spatialOrbit_left (s : ℂ) (hs : 1 < s.re)
    (z w : UpperHalfPlane) :
    Summable (fun γ : SL(2, ℤ) => ‖pointKernel s (γ • z : UpperHalfPlane) w‖) := by
  exact (summable_norm_spatialOrbit s hs w z).congr
    (fun γ => congrArg norm (pointKernel_symm s w (γ • z : UpperHalfPlane)))

/-- Absolute convergence survives the exact signed cusp reindexing. -/
theorem summable_norm_signedCuspOrbit (s : ℂ) (hs : 1 < s.re)
    (z w : UpperHalfPlane) :
    Summable (fun p : CuspCoset × (ℤ × Bool) =>
      ‖pointKernel s (ModularGroup.T ^ p.2.1 • (p.1.out • z) : UpperHalfPlane) w‖) := by
  have h := signedCuspOrbitEquiv.summable_iff.mpr
    (summable_norm_spatialOrbit_left s hs z w)
  simpa only [Function.comp_def, signedCuspOrbitEquiv_smul_apply] using h

/-- Absolute convergence on the actual unsigned cusp/translation product. -/
theorem summable_norm_cuspOrbit (s : ℂ) (hs : 1 < s.re)
    (z w : UpperHalfPlane) :
    Summable (fun p : CuspCoset × ℤ =>
      ‖pointKernel s (ModularGroup.T ^ p.2 • (p.1.out • z) : UpperHalfPlane) w‖) := by
  let e : CuspCoset × ℤ → CuspCoset × (ℤ × Bool) := fun p => (p.1, p.2, false)
  have he : Function.Injective e := by
    intro p q hpq
    exact Prod.ext (congrArg (fun a : CuspCoset × (ℤ × Bool) => a.1) hpq)
      (congrArg (fun a : CuspCoset × (ℤ × Bool) => a.2.1) hpq)
  have h := (summable_norm_signedCuspOrbit s hs z w).comp_injective he
  change Summable (fun p : CuspCoset × ℤ =>
    ‖pointKernel s (ModularGroup.T ^ (e p).2.1 • ((e p).1.out • z) : UpperHalfPlane) w‖) at h
  exact h

theorem summable_cuspOrbit (s : ℂ) (hs : 1 < s.re) (z w : UpperHalfPlane) :
    Summable (fun p : CuspCoset × ℤ =>
      pointKernel s (ModularGroup.T ^ p.2 • (p.1.out • z) : UpperHalfPlane) w) :=
  (summable_norm_cuspOrbit s hs z w).of_norm

/-- Each cusp's integer periodization is an ordinary absolutely convergent sum. -/
theorem summable_norm_cuspOrbit_translation (s : ℂ) (hs : 1 < s.re)
    (z w : UpperHalfPlane) (q : CuspCoset) :
    Summable (fun n : ℤ =>
      ‖pointKernel s (ModularGroup.T ^ n • (q.out • z) : UpperHalfPlane) w‖) :=
  (summable_norm_cuspOrbit s hs z w).prod_factor q

theorem summable_cuspOrbit_tsum_norm (s : ℂ) (hs : 1 < s.re)
    (z w : UpperHalfPlane) :
    Summable (fun q : CuspCoset => ∑' n : ℤ,
      ‖pointKernel s (ModularGroup.T ^ n • (q.out • z) : UpperHalfPlane) w‖) :=
  (summable_norm_cuspOrbit s hs z w).prod

/-- Absolute convergence also holds after the inner translations are summed. -/
theorem summable_norm_cuspPeriodization (s : ℂ) (hs : 1 < s.re)
    (z w : UpperHalfPlane) :
    Summable (fun q : CuspCoset => ‖∑' n : ℤ,
      pointKernel s (ModularGroup.T ^ n • (q.out • z) : UpperHalfPlane) w‖) := by
  apply (summable_cuspOrbit_tsum_norm s hs z w).of_nonneg_of_le
    (fun _ => norm_nonneg _) (fun q => ?_)
  exact norm_tsum_le_tsum_norm (summable_norm_cuspOrbit_translation s hs z w q)

/-- The half-weighted full matrix orbit equals one periodized point kernel per
actual cusp coset. Its central signs cancel exactly. -/
theorem spatialOrbitKernel_eq_cusp_tsum (s : ℂ) (hs : 1 < s.re)
    (z w : UpperHalfPlane) :
    spatialOrbitKernel s z w = ∑' q : CuspCoset, ∑' n : ℤ,
      pointKernel s (ModularGroup.T ^ n • (q.out • z) : UpperHalfPlane) w := by
  have hsigned := (summable_norm_signedCuspOrbit s hs z w).of_norm
  rw [spatialOrbitKernel_eq_half_tsum_left,
    ← signedCuspOrbitEquiv.tsum_eq
      (fun γ : SL(2, ℤ) => pointKernel s (γ • z : UpperHalfPlane) w)]
  simp only [signedCuspOrbitEquiv_smul_apply]
  rw [hsigned.tsum_prod]
  have hinner (q : CuspCoset) :
      (∑' p : ℤ × Bool,
        pointKernel s (ModularGroup.T ^ p.1 • (q.out • z) : UpperHalfPlane) w) =
      2 * ∑' n : ℤ,
        pointKernel s (ModularGroup.T ^ n • (q.out • z) : UpperHalfPlane) w := by
    rw [(hsigned.prod_factor q).tsum_prod]
    simp only [tsum_fintype, Fintype.sum_bool, ← two_mul, tsum_mul_left]
  simp_rw [hinner]
  rw [tsum_mul_left]
  ring

/-- A convergent-sum certificate for the exact cusp regrouping. -/
theorem hasSum_cuspPeriodization (s : ℂ) (hs : 1 < s.re)
    (z w : UpperHalfPlane) :
    HasSum (fun q : CuspCoset => ∑' n : ℤ,
      pointKernel s (ModularGroup.T ^ n • (q.out • z) : UpperHalfPlane) w)
      (spatialOrbitKernel s z w) := by
  rw [spatialOrbitKernel_eq_cusp_tsum s hs]
  exact (summable_norm_cuspPeriodization s hs z w).of_norm.hasSum

end GapFamily.Analytic.SpatialPoint
