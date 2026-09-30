import GapFamily.Analytic.Elliptic.WeakSobolevOrder
import Mathlib.Analysis.Calculus.ContDiff.Operations

noncomputable section
namespace GapFamily.Analytic.EllipticSobolev
open Set Homogenization
open scoped ContDiff

/-- The real derivative assembled from its finitely many coordinate values. -/
def realGradientField {d : ℕ} (g : Fin d → Vec d → ℝ) (x : Vec d) : Vec d →L[ℝ] ℝ :=
  ∑ i : Fin d, (ContinuousLinearMap.proj i).smulRight (g i x)

@[simp] theorem realGradientField_apply {d : ℕ}
    (g : Fin d → Vec d → ℝ) (x v : Vec d) :
    realGradientField g x v = ∑ i : Fin d, v i * g i x := by
  simp [realGradientField, ContinuousLinearMap.smulRight_apply]

/-- Coordinatewise finite classical regularity gives the same regularity in
continuous-linear-map norm for the actual derivative field. -/
theorem contDiffOn_realGradientField {d : ℕ} {n : ℕ∞ω} {U : Set (Vec d)}
    {g : Fin d → Vec d → ℝ} (hg : ∀ i, ContDiffOn ℝ n (g i) U) :
    ContDiffOn ℝ n (realGradientField g) U := by
  apply ContDiffOn.sum
  intro i _
  exact (((ContinuousLinearMap.smulRightL ℝ (Vec d) ℝ)
    (ContinuousLinearMap.proj i)).contDiff.comp_contDiffOn (hg i))

/-- A genuine derivative with finite-order regular coordinates gives one more
classical derivative order. This is an assembly lemma, not a weak regularity premise. -/
theorem contDiffOn_succ_of_hasFDerivAt_realGradientField {d : ℕ} {n : ℕ}
    {U : Set (Vec d)} (hU : IsOpen U) {f : Vec d → ℝ} {g : Fin d → Vec d → ℝ}
    (hd : ∀ x ∈ U, HasFDerivAt f (realGradientField g x) x)
    (hg : ∀ i, ContDiffOn ℝ (n : ℕ∞ω) (g i) U) :
    ContDiffOn ℝ ((n + 1 : ℕ) : ℕ∞ω) f U := by
  rw [Nat.cast_add, Nat.cast_one, contDiffOn_succ_iff_fderiv_of_isOpen hU]
  refine ⟨fun x hx => (hd x hx).differentiableAt.differentiableWithinAt, ?_, ?_⟩
  · intro h
    norm_cast at h
  · apply (contDiffOn_realGradientField hg).congr
    intro x hx
    exact (hd x hx).fderiv

end GapFamily.Analytic.EllipticSobolev
