import GapFamily.Analytic.Modular.ModularFullProjectedResolvent

/-! Genuine positive-shift resolvents of the actual unbounded modular Laplacian.
The existing completed-form construction supplies both inverse identities. -/

noncomputable section
namespace GapFamily.Analytic.ModularPositiveResolvent
open ModularGradient ModularProjected

/-- The actual bounded inverse at the negative real parameter -r. -/
def shiftedResolvent (r : ℝ) : ModularHilbert →L[ℂ] ModularHilbert :=
  fullResolvent (-(r : ℂ))

theorem shiftedResolvent_mem_domain (r : ℝ) (f : ModularHilbert) :
    shiftedResolvent r f ∈ laplacian.domain := fullResolvent_mem_domain _ _

/-- Positive r discharges the actual physical resolvent conditions. -/
theorem shiftedResolvent_rightInverse (r : ℝ) (hr : 0 < r) (f : ModularHilbert) :
    laplacian ⟨shiftedResolvent r f, shiftedResolvent_mem_domain r f⟩ +
      (r : ℂ) • shiftedResolvent r f = f := by
  have hz : -(r : ℂ) ≠ 0 := neg_ne_zero.mpr (Complex.ofReal_ne_zero.mpr hr.ne')
  have hreg : (-(r : ℂ)).im ≠ 0 ∨ (-(r : ℂ)).re < (1 / 4 : ℝ) := by
    right
    simp only [Complex.neg_re, Complex.ofReal_re]
    linarith
  simpa only [shiftedResolvent, neg_smul, sub_neg_eq_add] using
    fullResolvent_rightInverse hz hreg f

/-- The same map is a left inverse on every vector in the actual operator domain. -/
theorem shiftedResolvent_leftInverse (r : ℝ) (hr : 0 < r) (u : laplacian.domain) :
    shiftedResolvent r (laplacian u + (r : ℂ) • (u : ModularHilbert)) = u := by
  have hz : -(r : ℂ) ≠ 0 := neg_ne_zero.mpr (Complex.ofReal_ne_zero.mpr hr.ne')
  have hreg : (-(r : ℂ)).im ≠ 0 ∨ (-(r : ℂ)).re < (1 / 4 : ℝ) := by
    right
    simp only [Complex.neg_re, Complex.ofReal_re]
    linarith
  simpa only [shiftedResolvent, neg_smul, sub_neg_eq_add] using
    fullResolvent_leftInverse hz hreg u

/-- Symmetry is inherited from the actual densely defined self-adjoint Laplacian. -/
theorem laplacian_inner_symm (u v : laplacian.domain) :
    inner ℂ (laplacian u) (v : ModularHilbert) =
      inner ℂ (u : ModularHilbert) (laplacian v) := by
  have h := LinearPMap.adjoint_isFormalAdjoint laplacian_dense_domain
  rw [LinearPMap.isSelfAdjoint_def.mp laplacian_isSelfAdjoint] at h
  exact h u v

/-- The actual normalized resolvent factor r(A+r)⁻¹. -/
def resolventFactor (r : ℝ) : ModularHilbert →L[ℂ] ModularHilbert :=
  (r : ℂ) • shiftedResolvent r

theorem resolventFactor_mem_domain (r : ℝ) (f : ModularHilbert) :
    resolventFactor r f ∈ laplacian.domain :=
  laplacian.domain.smul_mem (r : ℂ) (shiftedResolvent_mem_domain r f)

/-- Exact cancellation by A+r, with the genuine operator-domain witness. -/
theorem resolventFactor_rightInverse (r : ℝ) (hr : 0 < r) (f : ModularHilbert) :
    laplacian ⟨resolventFactor r f, resolventFactor_mem_domain r f⟩ +
      (r : ℂ) • resolventFactor r f = (r : ℂ) • f := by
  have hsub : (⟨resolventFactor r f, resolventFactor_mem_domain r f⟩ : laplacian.domain) =
      (r : ℂ) • ⟨shiftedResolvent r f, shiftedResolvent_mem_domain r f⟩ :=
    Subtype.ext rfl
  rw [hsub, LinearPMap.map_smul]
  change (r : ℂ) • laplacian ⟨shiftedResolvent r f, shiftedResolvent_mem_domain r f⟩ +
    (r : ℂ) • ((r : ℂ) • shiftedResolvent r f) = _
  rw [← smul_add, shiftedResolvent_rightInverse r hr]

/-- Exact left cancellation on the actual Laplacian domain. -/
theorem resolventFactor_leftInverse (r : ℝ) (hr : 0 < r) (u : laplacian.domain) :
    resolventFactor r (laplacian u + (r : ℂ) • (u : ModularHilbert)) =
      (r : ℂ) • (u : ModularHilbert) := by
  change (r : ℂ) • shiftedResolvent r (laplacian u + (r : ℂ) • (u : ModularHilbert)) = _
  rw [shiftedResolvent_leftInverse r hr]

theorem shiftedResolvent_one : shiftedResolvent 1 = weakResolvent := by
  simpa only [shiftedResolvent, Complex.ofReal_one] using fullResolvent_neg_one

end GapFamily.Analytic.ModularPositiveResolvent
