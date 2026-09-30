import GapFamily.Analytic.Poincare.PoincareAnalytic
import GapFamily.Analytic.Modular.Periodization.ModularPeriodizationAction
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

noncomputable section

namespace GapFamily.Analytic.LaplacianCovariance

open Set Filter UpperHalfPlane
open scoped MatrixGroups Topology ContDiff

/-- The literal ambient zero-energy seed, with the source's uncompleted normalization. -/
def zeroEnergySeed (J : ℤ) (s : ℂ) (z : ℂ) : ℂ :=
  (z.im : ℂ) ^ s *
    Complex.exp ((2 * (Real.pi : ℂ) * Complex.I * (J : ℂ)) * (z.re : ℂ))

theorem contDiffAt_height_cpow (s : ℂ) {z : ℂ} (hz : 0 < z.im) :
    ContDiffAt ℝ ∞ (fun w : ℂ => (w.im : ℂ) ^ s) z := by
  have hlog : ContDiffAt ℝ ∞ (fun w : ℂ => Real.log w.im) z :=
    (Real.contDiffAt_log.mpr hz.ne').comp z Complex.imCLM.contDiff.contDiffAt
  have hlogc : ContDiffAt ℝ ∞ (fun w : ℂ => (Real.log w.im : ℂ)) z :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp z hlog
  have he : ContDiffAt ℝ ∞
      (fun w : ℂ => Complex.exp ((Real.log w.im : ℂ) * s)) z :=
    (hlogc.mul contDiffAt_const).cexp
  apply he.congr_of_eventuallyEq
  filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds hz] with w hw
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt hw)),
    Complex.ofReal_log (le_of_lt hw)]

/-- Every complex exponent gives a real smooth field on the upper half-plane. -/
theorem contDiffAt_zeroEnergySeed (J : ℤ) (s : ℂ) {z : ℂ} (hz : 0 < z.im) :
    ContDiffAt ℝ ∞ (zeroEnergySeed J s) z := by
  apply (contDiffAt_height_cpow s hz).mul
  exact (contDiffAt_const.mul
    (Complex.ofRealCLM.contDiff.contDiffAt.comp z Complex.reCLM.contDiff.contDiffAt)).cexp

theorem contDiffOn_zeroEnergySeed (J : ℤ) (s : ℂ) :
    ContDiffOn ℝ ∞ (zeroEnergySeed J s) upperHalfPlaneSet :=
  fun _z hz => (contDiffAt_zeroEnergySeed J s hz).contDiffWithinAt

theorem contDiffOn_two_zeroEnergySeed (J : ℤ) (s : ℂ) :
    ContDiffOn ℝ 2 (zeroEnergySeed J s) upperHalfPlaneSet :=
  (contDiffOn_zeroEnergySeed J s).of_le (by norm_num)

/-- Exact agreement with the existing complexified point seed. -/
theorem zeroEnergySeed_coe (J : ℤ) (s : ℂ) (τ : UpperHalfPlane) :
    zeroEnergySeed J s τ = complexPointSeed 0 J s τ := by
  unfold zeroEnergySeed complexPointSeed
  simp only [mul_zero, zero_mul, zero_add, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
  congr 2
  push_cast
  ring

theorem zeroEnergySeed_coe_ofReal (J : ℤ) (s : ℝ) (τ : UpperHalfPlane) :
    zeroEnergySeed J (s : ℂ) τ = pointSeed 0 J s τ := by
  rw [zeroEnergySeed_coe]
  simpa using complexPointSeed_ofReal 0 J s τ

/-- An ambient representative for the actual cusp-quotient summand. -/
def zeroEnergyRepresentative (J : ℤ) (s : ℂ) (q : CuspCoset) : ℂ → ℂ :=
  zeroEnergySeed J s ∘ rawModularAction q.out

/-- The chosen ambient representative is the original quotient term at every
upper-half-plane point; the existing quotient proof removes representative dependence. -/
theorem zeroEnergyRepresentative_coe (J : ℤ) (s : ℂ)
    (q : CuspCoset) (τ : UpperHalfPlane) :
    zeroEnergyRepresentative J s q τ = complexPoincareTerm 0 J s τ q := by
  rw [zeroEnergyRepresentative, Function.comp_apply, rawModularAction_coe,
    zeroEnergySeed_coe, complexPoincareTerm_out]

theorem zeroEnergyRepresentative_germ (J : ℤ) (s : ℂ)
    (q : CuspCoset) (τ : UpperHalfPlane) :
    zeroEnergyRepresentative J s q =ᶠ[𝓝 (τ : ℂ)]
      (fun z : ℂ => complexPoincareTerm 0 J s (UpperHalfPlane.ofComplex z) q) := by
  filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds τ.im_pos] with z hz
  simpa only [UpperHalfPlane.ofComplex_apply_of_im_pos hz] using
    zeroEnergyRepresentative_coe J s q (⟨z, hz⟩ : UpperHalfPlane)

/-- The actual coset summand has a real smooth ambient representative locally. -/
theorem contDiffAt_zeroEnergyRepresentative (J : ℤ) (s : ℂ)
    (q : CuspCoset) (τ : UpperHalfPlane) :
    ContDiffAt ℝ ∞ (zeroEnergyRepresentative J s q) τ := by
  have hs : ContDiffAt ℝ ∞ (zeroEnergySeed J s) (rawModularAction q.out τ) := by
    rw [rawModularAction_coe]
    exact contDiffAt_zeroEnergySeed J s (q.out • τ : UpperHalfPlane).im_pos
  exact hs.comp (τ : ℂ)
    ((contDiffOn_rawModularAction q.out).contDiffAt
      (isOpen_upperHalfPlaneSet.mem_nhds τ.im_pos))

end GapFamily.Analytic.LaplacianCovariance
