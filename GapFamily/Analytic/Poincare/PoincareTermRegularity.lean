import GapFamily.Analytic.Poincare.PoincareTermGradient

/-!
Real spatial regularity of each literal zero-energy Poincare quotient term.
No regularity of an infinite sum is asserted in this module.
-/

noncomputable section
namespace GapFamily.Analytic.PoincareTermRegularity

open Set UpperHalfPlane PoincareSeedGradient
  PoincareActionGradient PoincareTermGradient
open scoped Topology ContDiff MatrixGroups

/-- Every individual raw seed is real smooth at every positive-height point,
for an arbitrary complex exponent. -/
theorem contDiffAt_rawSeed {n : ℕ∞ω} (J : ℤ) (s : ℂ) (τ : UpperHalfPlane) :
    ContDiffAt ℝ n (rawSeed J s) (τ : ℂ) := by
  have hdiff : DifferentiableOn ℂ (fun w : ℂ => w ^ s) Complex.slitPlane :=
    fun w hw => (differentiableAt_id.cpow_const hw).differentiableWithinAt
  have hcp : AnalyticAt ℂ (fun w : ℂ => w ^ s) (τ.im : ℂ) :=
    hdiff.analyticAt (Complex.isOpen_slitPlane.mem_nhds (Or.inl τ.im_pos))
  have hp : ContDiffAt ℝ n (fun z : ℂ => (z.im : ℂ) ^ s) (τ : ℂ) :=
    (hcp.contDiffAt.restrict_scalars ℝ).comp (τ : ℂ)
      ((Complex.ofRealCLM.comp Complex.imCLM).contDiff.contDiffAt)
  have he : ContDiff ℝ n (fun z : ℂ =>
      Complex.exp (((2 * Real.pi * (J : ℝ) * z.re : ℝ) : ℂ) * Complex.I)) := by
    exact ((Complex.ofRealCLM.contDiff.comp
      (contDiff_const.mul Complex.reCLM.contDiff)).mul contDiff_const).cexp
  exact hp.mul he.contDiffAt

/-- The actual ambient modular action is real smooth at positive height. -/
theorem contDiffAt_modularAction {n : ℕ∞ω} (γ : SL(2, ℤ)) (τ : UpperHalfPlane) :
    ContDiffAt ℝ n (modularAction γ) (τ : ℂ) := by
  have hg : 0 < (γ : GL (Fin 2) ℝ).val.det := by
    change 0 < ((γ : Matrix (Fin 2) (Fin 2) ℤ).map (fun x => (x : ℝ))).det
    rw [← Int.cast_det, γ.property]
    norm_num
  simpa only [modularAction] using!
    ((UpperHalfPlane.analyticAt_smul hg τ).contDiffAt (n := n)).restrict_scalars ℝ

/-- An individual transformed seed is real smooth at every upper-half-plane point. -/
theorem contDiffAt_translatedSeed {n : ℕ∞ω} (J : ℤ) (s : ℂ) (γ : SL(2, ℤ))
    (τ : UpperHalfPlane) : ContDiffAt ℝ n (translatedSeed J s γ) (τ : ℂ) := by
  have h : ContDiffAt ℝ n (rawSeed J s) (modularAction γ τ) := by
    simpa only [modularAction_apply] using contDiffAt_rawSeed (n := n) J s (γ • τ)
  exact h.comp (τ : ℂ) (contDiffAt_modularAction γ τ)

/-- Real regularity of the actual quotient term, without an exponent restriction. -/
theorem contDiffAt_term {n : ℕ∞ω} (J : ℤ) (s : ℂ) (q : CuspCoset)
    (τ : UpperHalfPlane) : ContDiffAt ℝ n (term J s q) (τ : ℂ) :=
  contDiffAt_translatedSeed J s q.out τ

/-- Each actual term is real smooth throughout the open upper half-plane. -/
theorem contDiffOn_term {n : ℕ∞ω} (J : ℤ) (s : ℂ) (q : CuspCoset) :
    ContDiffOn ℝ n (term J s q) upperHalfPlaneSet := by
  intro z hz
  exact (contDiffAt_term (n := n) J s q ⟨z, hz⟩).contDiffWithinAt

/-- Continuity in operator norm of the actual real first derivative of each term. -/
theorem continuousOn_fderiv_term (J : ℤ) (s : ℂ) (q : CuspCoset) :
    ContinuousOn (fderiv ℝ (term J s q)) upperHalfPlaneSet :=
  (contDiffOn_term (n := 1) J s q).continuousOn_fderiv_of_isOpen
    isOpen_upperHalfPlaneSet le_rfl

end GapFamily.Analytic.PoincareTermRegularity
