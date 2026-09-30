import GapFamily.Analytic.Cusp.Fourier.CuspHorizontalPoincare
import GapFamily.Analytic.Modular.ModularGradientCore
import Mathlib.MeasureTheory.Integral.Bochner.Set

noncomputable section
namespace GapFamily.Analytic
open Set MeasureTheory UpperHalfPlane
open scoped ContDiff

theorem cuspPoint_eq (x y : ℝ) : Complex.mk x y = (x : ℂ) + (y : ℂ) * Complex.I := by
  exact Complex.ext (by simp) (by simp)

def cuspHorizontalSlice (F : ℂ → ℂ) (y x : ℝ) : ℂ := F (Complex.mk x y)

def cuspHorizontalAverage (F : ℂ → ℂ) (y : ℝ) : ℂ :=
  ∫ x in (-1/2 : ℝ)..(1/2), cuspHorizontalSlice F y x

def cuspHorizontalResidual (F : ℂ → ℂ) (z : ℂ) : ℂ := F z - cuspHorizontalAverage F z.im

theorem contDiff_cuspHorizontalSlice {F : ℂ → ℂ}
    (hF : ContDiffOn ℝ ∞ F upperHalfPlaneSet) {y : ℝ} (hy : 0 < y) :
    ContDiff ℝ ∞ (cuspHorizontalSlice F y) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  have hpoint := hF.contDiffAt (isOpen_upperHalfPlaneSet.mem_nhds
    (show (Complex.mk x y) ∈ upperHalfPlaneSet from hy))
  apply hpoint.comp x
  simp only [cuspPoint_eq]
  exact Complex.ofRealCLM.contDiff.contDiffAt.add contDiffAt_const

theorem deriv_cuspHorizontalSlice {F : ℂ → ℂ}
    (hF : ContDiffOn ℝ ∞ F upperHalfPlaneSet) {y : ℝ} (hy : 0 < y) (x : ℝ) :
    deriv (cuspHorizontalSlice F y) x = fderiv ℝ F (Complex.mk x y) 1 := by
  have hline : HasDerivAt (fun t : ℝ => Complex.mk t y) 1 x := by
    simpa [cuspPoint_eq] using
      (Complex.ofRealCLM.hasFDerivAt (x := x)).hasDerivAt.add_const ((y : ℂ) * Complex.I)
  have hpoint := (hF.contDiffAt (isOpen_upperHalfPlaneSet.mem_nhds
    (show (Complex.mk x y) ∈ upperHalfPlaneSet from hy))).differentiableAt (by simp)
  exact (hpoint.hasFDerivAt.comp_hasDerivAt x hline).deriv

theorem continuousOn_cuspHorizontalAverage {F : ℂ → ℂ}
    (hF : ContinuousOn F upperHalfPlaneSet) :
    ContinuousOn (cuspHorizontalAverage F) (Ioi 0) := by
  let : LocallyCompactSpace (Ioi (0 : ℝ)) := isOpen_Ioi.locallyCompactSpace
  rw [continuousOn_iff_continuous_domRestrict]
  have hjoint : Continuous (Function.uncurry
      (fun y : Ioi (0 : ℝ) => cuspHorizontalSlice F y)) := by
    change Continuous (fun p : Ioi (0 : ℝ) × ℝ => F (Complex.mk p.2 p.1))
    apply hF.comp_continuous
    · simp only [cuspPoint_eq]
      fun_prop
    · intro p
      exact p.1.property
  have hint := continuous_parametric_integral_of_continuous (μ := volume) hjoint
    (s := Icc (-1/2 : ℝ) (1/2)) isCompact_Icc
  apply hint.congr
  intro y
  dsimp [cuspHorizontalAverage]
  rw [intervalIntegral.integral_of_le (by norm_num : (-1/2 : ℝ) ≤ 1/2),
    ← integral_Icc_eq_integral_Ioc]

theorem continuousOn_cuspHorizontalResidual {F : ℂ → ℂ}
    (hF : ContinuousOn F upperHalfPlaneSet) :
    ContinuousOn (cuspHorizontalResidual F) upperHalfPlaneSet :=
  hF.sub ((continuousOn_cuspHorizontalAverage hF).comp Complex.continuous_im.continuousOn
    (fun _ hz => hz))

theorem modular_horizontal_poincare {F : ℂ → ℂ}
    (hF : ContDiffOn ℝ ∞ F upperHalfPlaneSet) {y : ℝ} (hy : 0 < y) :
    (∫ x in (-1/2 : ℝ)..(1/2), ‖cuspHorizontalResidual F (Complex.mk x y)‖ ^ 2) ≤
      ∫ x in (-1/2 : ℝ)..(1/2), ‖fderiv ℝ F (Complex.mk x y) 1‖ ^ 2 := by
  simpa only [cuspHorizontalResidual, cuspHorizontalAverage, cuspHorizontalSlice,
    deriv_cuspHorizontalSlice hF hy] using
    cusp_horizontal_poincare (cuspHorizontalSlice F y) ((contDiff_cuspHorizontalSlice hF hy).of_le (by simp))

theorem cuspHorizontalSlice_periodic (F : ModularGradient.smoothCore) {y : ℝ} (hy : 0 < y) :
    Function.Periodic (cuspHorizontalSlice F.val y) 1 := by
  intro x
  have hinv := F.property.2.1 ModularGroup.T (⟨Complex.mk x y, hy⟩ : UpperHalfPlane)
  rw [UpperHalfPlane.modular_T_smul, UpperHalfPlane.coe_vadd] at hinv
  simpa [cuspHorizontalSlice, cuspPoint_eq, add_assoc, add_comm, add_left_comm] using hinv

theorem integral_cuspHorizontalResidual_eq_zero {F : ℂ → ℂ}
    (hF : ContDiffOn ℝ ∞ F upperHalfPlaneSet) {y : ℝ} (hy : 0 < y) :
    (∫ x in (-1/2 : ℝ)..(1/2), cuspHorizontalResidual F (Complex.mk x y)) = 0 := by
  have hi := (contDiff_cuspHorizontalSlice hF hy).continuous.intervalIntegrable (μ := volume)
    (-1/2 : ℝ) (1/2)
  change (∫ x in (-1/2 : ℝ)..(1/2), cuspHorizontalSlice F y x - cuspHorizontalAverage F y) = 0
  rw [intervalIntegral.integral_sub hi intervalIntegrable_const]
  norm_num [cuspHorizontalAverage, intervalIntegral.integral_const]

end GapFamily.Analytic
