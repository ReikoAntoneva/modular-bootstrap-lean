import GapFamily.Analytic.Poincare.PoincareHighCuspBound
import Mathlib.Analysis.SpecialFunctions.Exponential

/-! Entire dependence of each actual modular-orbit summand in C(K). -/
noncomputable section
namespace GapFamily.Analytic.PoincareHighCuspAnalytic
open Set UpperHalfPlane CuspFourierCutoff PoincareHighCusp
open scoped Topology MatrixGroups

/-- The actual continuous logarithm of the positive orbit height. -/
def orbitLog (K : Set UpperHalfPlane) (γ : SL(2, ℤ)) : C(K, ℂ) :=
  ⟨fun τ => (Real.log (γ • τ.val : UpperHalfPlane).im : ℂ),
    Complex.continuous_ofReal.comp
      ((UpperHalfPlane.continuous_im.comp
        ((show Continuous (fun τ : UpperHalfPlane => γ • τ) from
          continuous_const_smul (γ : Matrix.GeneralLinearGroup (Fin 2) ℝ)).comp continuous_subtype_val)).log
          (fun τ => (γ • τ.val : UpperHalfPlane).im_ne_zero))⟩

/-- The cutoff and Fourier phase of the literal summand are parameter-independent. -/
def orbitAmplitude (K : Set UpperHalfPlane) (J : ℤ) (γ : SL(2, ℤ)) : C(K, ℂ) :=
  ⟨fun τ => (cuspTranslationWeight (γ • τ.val : UpperHalfPlane).re : ℂ) *
      (cutoff (γ • τ.val : UpperHalfPlane).im : ℂ) *
      cuspFourierMode J (γ • τ.val : UpperHalfPlane).re, by
    have hg : Continuous (fun τ : K => (γ • τ.val : UpperHalfPlane)) :=
      (show Continuous (fun τ : UpperHalfPlane => γ • τ) from
          continuous_const_smul (γ : Matrix.GeneralLinearGroup (Fin 2) ℝ)).comp continuous_subtype_val
    exact ((Complex.continuous_ofReal.comp
      (contDiff_cuspTranslationWeight.continuous.comp (UpperHalfPlane.continuous_re.comp hg))).mul
      (Complex.continuous_ofReal.comp
        (contDiff_cutoff.continuous.comp (UpperHalfPlane.continuous_im.comp hg)))).mul
          ((contDiff_cuspFourierMode J).continuous.comp (UpperHalfPlane.continuous_re.comp hg))⟩

/-- The actual positive-height power, expressed in the Banach algebra C(K). -/
def orbitTerm (K : Set UpperHalfPlane) [CompactSpace K] (J : ℤ)
    (γ : SL(2, ℤ)) (s : ℂ) : C(K, ℂ) :=
  orbitAmplitude K J γ * NormedSpace.exp (s • orbitLog K γ)

theorem orbitTerm_apply (K : Set UpperHalfPlane) [CompactSpace K] (J : ℤ)
    (γ : SL(2, ℤ)) (s : ℂ) (τ : K) :
    orbitTerm K J γ s τ =
      cuspFourierProfileSeed J (highProfile s) (γ • τ.val : UpperHalfPlane) := by
  have he : NormedSpace.exp (s • orbitLog K γ) τ =
      Complex.exp (s * (Real.log (γ • τ.val : UpperHalfPlane).im : ℂ)) := by
    simpa only [Complex.exp_eq_exp_ℂ, ContinuousMap.evalAlgHom_apply,
      ContinuousMap.smul_apply, smul_eq_mul, orbitLog, ContinuousMap.coe_mk] using
      NormedSpace.map_exp (ContinuousMap.evalAlgHom ℂ ℂ τ)
        (ContinuousMap.evalCLM ℂ τ).continuous (s • orbitLog K γ)
  have hp : ((γ • τ.val : UpperHalfPlane).im : ℂ) ^ s =
      Complex.exp (s * (Real.log (γ • τ.val : UpperHalfPlane).im : ℂ)) := by
    rw [Complex.cpow_def_of_ne_zero
      (Complex.ofReal_ne_zero.mpr (γ • τ.val : UpperHalfPlane).im_ne_zero),
      ← Complex.ofReal_log (γ • τ.val : UpperHalfPlane).im_pos.le, mul_comm]
  simp only [orbitTerm, ContinuousMap.mul_apply, he, ← hp, orbitAmplitude,
    cuspFourierProfileSeed, cuspProfileSeed, highProfile, ContinuousMap.coe_mk,
    UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
  ring

theorem differentiable_orbitTerm (K : Set UpperHalfPlane) [CompactSpace K]
    (J : ℤ) (γ : SL(2, ℤ)) : Differentiable ℂ (orbitTerm K J γ) :=
  (differentiable_exp_smul_const ℂ (orbitLog K γ)).const_mul _

theorem analyticAt_orbitTerm (K : Set UpperHalfPlane) [CompactSpace K]
    (J : ℤ) (γ : SL(2, ℤ)) (s : ℂ) : AnalyticAt ℂ (orbitTerm K J γ) s :=
  (differentiable_orbitTerm K J γ).analyticAt s

end GapFamily.Analytic.PoincareHighCuspAnalytic
