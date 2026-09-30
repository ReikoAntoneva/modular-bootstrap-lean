import GapFamily.Analytic.Poincare.PoincareAnalytic
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Analysis.SpecialFunctions.Exponential

noncomputable section
namespace GapFamily.Analytic.PoincareConvergentAnalytic
open Set UpperHalfPlane
open scoped Topology MatrixGroups

/-- The actual modular orbit, restricted to a compact-coordinate domain inside H. -/
def compactOrbit (K : Set ℂ) (hKH : K ⊆ upperHalfPlaneSet) (q : CuspCoset) :
    C(K, UpperHalfPlane) :=
  ⟨fun z => q.out • (⟨z.val, hKH z.property⟩ : UpperHalfPlane), by
    have hi : Continuous (fun z : K => (⟨z.val, hKH z.property⟩ : UpperHalfPlane)) :=
      continuous_subtype_val.upperHalfPlaneMk (fun z => hKH z.property)
    exact (show Continuous (fun τ : UpperHalfPlane => q.out • τ) from
      continuous_const_smul (q.out : Matrix.GeneralLinearGroup (Fin 2) ℝ)).comp hi⟩

theorem compactOrbit_apply (K : Set ℂ) (hKH : K ⊆ upperHalfPlaneSet)
    (q : CuspCoset) (z : K) :
    compactOrbit K hKH q z = q.out • UpperHalfPlane.ofComplex z.val := by
  simp only [compactOrbit, ContinuousMap.coe_mk,
    UpperHalfPlane.ofComplex_apply_of_im_pos (hKH z.property)]

/-- The real logarithm of the positive orbit height is an actual continuous field. -/
def compactOrbitLog (K : Set ℂ) (hKH : K ⊆ upperHalfPlaneSet) (q : CuspCoset) :
    C(K, ℂ) :=
  ⟨fun z => (Real.log (compactOrbit K hKH q z).im : ℂ),
    Complex.continuous_ofReal.comp
      ((UpperHalfPlane.continuous_im.comp (compactOrbit K hKH q).continuous).log
        (fun z => (compactOrbit K hKH q z).im_ne_zero))⟩

/-- The original uncompleted Fourier phase has no dependence on the spectral parameter. -/
def compactOrbitPhase (K : Set ℂ) (hKH : K ⊆ upperHalfPlaneSet) (J : ℤ)
    (q : CuspCoset) : C(K, ℂ) :=
  ⟨fun z => Complex.exp
      (((2 * Real.pi * (J : ℝ) * (compactOrbit K hKH q z).re : ℝ) : ℂ) * Complex.I),
    Complex.continuous_exp.comp
      ((Complex.continuous_ofReal.comp
        (continuous_const.mul
          (UpperHalfPlane.continuous_re.comp (compactOrbit K hKH q).continuous))).mul
        continuous_const)⟩

/-- One actual Poincare summand as an element of the spatial uniform-norm Banach algebra. -/
def compactTerm (K : Set ℂ) [CompactSpace K] (hKH : K ⊆ upperHalfPlaneSet)
    (J : ℤ) (s : ℂ) (q : CuspCoset) : C(K, ℂ) :=
  NormedSpace.exp (s • compactOrbitLog K hKH q) * compactOrbitPhase K hKH J q

/-- The Banach-valued construction is literally the existing quotient summand. -/
theorem compactTerm_apply (K : Set ℂ) [CompactSpace K] (hKH : K ⊆ upperHalfPlaneSet)
    (J : ℤ) (s : ℂ) (q : CuspCoset) (z : K) :
    compactTerm K hKH J s q z =
      complexPoincareTerm 0 J s (UpperHalfPlane.ofComplex z.val) q := by
  have he : NormedSpace.exp (s • compactOrbitLog K hKH q) z =
      Complex.exp (s * (Real.log (compactOrbit K hKH q z).im : ℂ)) := by
    simpa only [Complex.exp_eq_exp_ℂ, ContinuousMap.evalAlgHom_apply,
      ContinuousMap.smul_apply, smul_eq_mul, compactOrbitLog, ContinuousMap.coe_mk] using
      NormedSpace.map_exp (ContinuousMap.evalAlgHom ℂ ℂ z)
        (ContinuousMap.evalCLM ℂ z).continuous (s • compactOrbitLog K hKH q)
  have hp : ((compactOrbit K hKH q z).im : ℂ) ^ s =
      Complex.exp (s * (Real.log (compactOrbit K hKH q z).im : ℂ)) := by
    rw [Complex.cpow_def_of_ne_zero
      (Complex.ofReal_ne_zero.mpr (compactOrbit K hKH q z).im_ne_zero),
      ← Complex.ofReal_log (compactOrbit K hKH q z).im_pos.le, mul_comm]
  rw [compactTerm, ContinuousMap.mul_apply, he, ← hp, complexPoincareTerm_out]
  simp only [compactOrbitPhase, ContinuousMap.coe_mk, compactOrbit_apply,
    complexPointSeed, mul_zero, zero_mul, zero_add]

/-- The actual single-term family is differentiable in the spatial uniform norm everywhere. -/
theorem compactTerm_differentiable (K : Set ℂ) [CompactSpace K]
    (hKH : K ⊆ upperHalfPlaneSet) (J : ℤ) (q : CuspCoset) :
    Differentiable ℂ (fun s => compactTerm K hKH J s q) :=
  (differentiable_exp_smul_const ℂ (compactOrbitLog K hKH q)).mul_const _

/-- Every complex parameter is an analytic point of the actual compact single-term family. -/
theorem compactTerm_analyticAt (K : Set ℂ) [CompactSpace K]
    (hKH : K ⊆ upperHalfPlaneSet) (J : ℤ) (q : CuspCoset) (s : ℂ) :
    AnalyticAt ℂ (fun w => compactTerm K hKH J w q) s :=
  (compactTerm_differentiable K hKH J q).analyticAt s

end GapFamily.Analytic.PoincareConvergentAnalytic
