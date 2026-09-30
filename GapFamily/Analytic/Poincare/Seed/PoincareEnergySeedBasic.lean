import GapFamily.Analytic.Poincare.PoincareTermRegularity

/-!
Literal normalization and real spatial regularity of each actual energy-difference
seed and cusp-quotient term. No bound or smoothness of an infinite sum is asserted.
-/

noncomputable section
namespace GapFamily.Analytic.PoincareEnergySeedBasic

open Set UpperHalfPlane PoincareSeedGradient
  PoincareActionGradient PoincareTermRegularity
open scoped Topology ContDiff MatrixGroups

/-- The actual raw zero-energy subtraction with complex input energy. -/
def rawDifferenceSeed (E : ℂ) (J : ℤ) (s : ℂ) (z : ℂ) : ℂ :=
  rawSeed J s z * (Complex.exp ((-2 * (Real.pi : ℂ) * E) * (z.im : ℂ)) - 1)

/-- Exact source normalization of the raw energy-difference seed. -/
theorem rawDifferenceSeed_eq_complexPointSeed (E : ℂ) (J : ℤ) (s : ℂ)
    (τ : UpperHalfPlane) :
    rawDifferenceSeed E J s τ = complexPointSeed E J s τ - complexPointSeed 0 J s τ := by
  rw [complexPointSeed_sub_zero_energy]
  rfl

/-- The exponential subtraction is real smooth on the whole ambient plane. -/
theorem contDiff_energyFactor {n : ℕ∞ω} (E : ℂ) :
    ContDiff ℝ n (fun z : ℂ => Complex.exp ((-2 * (Real.pi : ℂ) * E) * (z.im : ℂ)) - 1) :=
  ((contDiff_const.mul (Complex.ofRealCLM.contDiff.comp Complex.imCLM.contDiff)).cexp).sub
    contDiff_const

/-- Every individual difference seed is real smooth at positive height,
for arbitrary complex energy and exponent. -/
theorem contDiffAt_rawDifferenceSeed {n : ℕ∞ω} (E : ℂ) (J : ℤ) (s : ℂ)
    (τ : UpperHalfPlane) : ContDiffAt ℝ n (rawDifferenceSeed E J s) (τ : ℂ) :=
  (contDiffAt_rawSeed J s τ).mul (contDiff_energyFactor E).contDiffAt

theorem contDiffOn_rawDifferenceSeed {n : ℕ∞ω} (E : ℂ) (J : ℤ) (s : ℂ) :
    ContDiffOn ℝ n (rawDifferenceSeed E J s) upperHalfPlaneSet := by
  intro z hz
  exact (contDiffAt_rawDifferenceSeed (n := n) E J s ⟨z, hz⟩).contDiffWithinAt

/-- The actual cusp term using the existing ambient modular action. -/
def differenceTerm (E : ℂ) (J : ℤ) (s : ℂ) (q : CuspCoset) : ℂ → ℂ :=
  rawDifferenceSeed E J s ∘ modularAction q.out

/-- A literal function identity, including the ambient upper-half-plane extension. -/
theorem differenceTerm_eq_complexPoincareDifferenceTerm_ofComplex
    (E : ℂ) (J : ℤ) (s : ℂ) (q : CuspCoset) :
    differenceTerm E J s q =
      fun z : ℂ => complexPoincareDifferenceTerm E J s (UpperHalfPlane.ofComplex z) q := by
  funext z
  rw [complexPoincareDifferenceTerm, complexPoincareTerm_out, complexPoincareTerm_out]
  exact rawDifferenceSeed_eq_complexPointSeed E J s (q.out • UpperHalfPlane.ofComplex z)

@[simp] theorem differenceTerm_apply (E : ℂ) (J : ℤ) (s : ℂ) (q : CuspCoset)
    (τ : UpperHalfPlane) :
    differenceTerm E J s q τ = complexPoincareDifferenceTerm E J s τ q := by
  simp only [differenceTerm, Function.comp_apply, modularAction_apply,
    rawDifferenceSeed_eq_complexPointSeed, complexPoincareDifferenceTerm, complexPoincareTerm_out]

/-- Real smoothness of each actual transformed difference seed. -/
theorem contDiffAt_differenceTerm {n : ℕ∞ω} (E : ℂ) (J : ℤ) (s : ℂ)
    (q : CuspCoset) (τ : UpperHalfPlane) :
    ContDiffAt ℝ n (differenceTerm E J s q) (τ : ℂ) := by
  have h : ContDiffAt ℝ n (rawDifferenceSeed E J s) (modularAction q.out τ) := by
    simpa only [modularAction_apply] using
      contDiffAt_rawDifferenceSeed (n := n) E J s (q.out • τ)
  exact h.comp (τ : ℂ) (contDiffAt_modularAction q.out τ)

theorem contDiffOn_differenceTerm {n : ℕ∞ω} (E : ℂ) (J : ℤ) (s : ℂ) (q : CuspCoset) :
    ContDiffOn ℝ n (differenceTerm E J s q) upperHalfPlaneSet := by
  intro z hz
  exact (contDiffAt_differenceTerm (n := n) E J s q ⟨z, hz⟩).contDiffWithinAt

/-- The canonical term itself is real smooth, without a representation hypothesis. -/
theorem contDiffAt_complexPoincareDifferenceTerm {n : ℕ∞ω}
    (E : ℂ) (J : ℤ) (s : ℂ) (q : CuspCoset) (τ : UpperHalfPlane) :
    ContDiffAt ℝ n
      (fun z : ℂ => complexPoincareDifferenceTerm E J s (UpperHalfPlane.ofComplex z) q) τ := by
  rw [← differenceTerm_eq_complexPoincareDifferenceTerm_ofComplex]
  exact contDiffAt_differenceTerm E J s q τ

/-- Every canonical term is real smooth throughout the open upper half-plane. -/
theorem contDiffOn_complexPoincareDifferenceTerm {n : ℕ∞ω}
    (E : ℂ) (J : ℤ) (s : ℂ) (q : CuspCoset) :
    ContDiffOn ℝ n
      (fun z : ℂ => complexPoincareDifferenceTerm E J s (UpperHalfPlane.ofComplex z) q)
      upperHalfPlaneSet := by
  rw [← differenceTerm_eq_complexPoincareDifferenceTerm_ofComplex]
  exact contDiffOn_differenceTerm E J s q

end GapFamily.Analytic.PoincareEnergySeedBasic
