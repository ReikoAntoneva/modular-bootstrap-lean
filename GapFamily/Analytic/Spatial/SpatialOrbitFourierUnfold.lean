import GapFamily.Analytic.Spatial.SpatialOrbitCusp
import GapFamily.Analytic.Spatial.SpatialPointPeriodization

noncomputable section
namespace GapFamily.Analytic.SpatialPoint

open Set MeasureTheory PoincareFourier UpperHalfPlane
open scoped MatrixGroups

/-- One cusp's periodized point kernel, tested against an integer mode. -/
def cuspOrbitFourierTerm (J : ℤ) (s : ℂ) (z : UpperHalfPlane)
    (y : ℝ) (hy : 0 < y) (q : CuspCoset) (x : ℝ) : ℂ :=
  cuspFourierMode J x * ∑' n : ℤ,
    pointKernel s (rowPoint y hy x) (ModularGroup.T ^ n • (q.out • z) : UpperHalfPlane)

theorem hasSum_cuspOrbitFourierTerm (J : ℤ) (s : ℂ) (hs : 1 < s.re)
    (z : UpperHalfPlane) (y : ℝ) (hy : 0 < y) (x : ℝ) :
    HasSum (fun q => cuspOrbitFourierTerm J s z y hy q x)
      (cuspFourierMode J x * spatialOrbitKernel s z (rowPoint y hy x)) := by
  have h := (hasSum_cuspPeriodization s hs z (rowPoint y hy x)).mul_left
    (cuspFourierMode J x)
  apply h.congr_fun
  intro q
  dsimp [cuspOrbitFourierTerm]
  congr 1
  exact tsum_congr fun n => pointKernel_symm s (rowPoint y hy x)
    (ModularGroup.T ^ n • (q.out • z) : UpperHalfPlane)

/-- Absolute convergence of the integer orbit with the horizontal argument first. -/
theorem summable_norm_cuspOrbit_horizontal (s : ℂ) (hs : 1 < s.re)
    (z : UpperHalfPlane) (y : ℝ) (hy : 0 < y) (q : CuspCoset) (x : ℝ) :
    Summable (fun n : ℤ =>
      ‖pointKernel s (rowPoint y hy x) (ModularGroup.T ^ n • (q.out • z) : UpperHalfPlane)‖) :=
  (summable_norm_cuspOrbit_translation s hs z (rowPoint y hy x) q).congr
    (fun n => congrArg norm (pointKernel_symm s
      (ModularGroup.T ^ n • (q.out • z) : UpperHalfPlane) (rowPoint y hy x)))

theorem cuspOrbit_horizontal_norm_le (s : ℂ) (hs : 1 < s.re)
    (z : UpperHalfPlane) (y : ℝ) (hy : 0 < y) (q : CuspCoset) (n : ℤ)
    (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
    ‖pointKernel s (rowPoint y hy x) (ModularGroup.T ^ n • (q.out • z) : UpperHalfPlane)‖ ≤
      (2 + 2 / y ^ 2) ^ s.re *
        ‖pointKernel s (rowPoint y hy 0) (ModularGroup.T ^ n • (q.out • z) : UpperHalfPlane)‖ := by
  have h := pointKernel_horizontal_shift_norm_le s (by linarith) y hy
    (ModularGroup.T ^ n • (q.out • z)) 1 x 0 (by
      rw [abs_of_nonneg hx.1]
      exact hx.2)
  simpa using h

theorem continuousOn_cuspOrbitFourierTerm (J : ℤ) (s : ℂ) (hs : 1 < s.re)
    (z : UpperHalfPlane) (y : ℝ) (hy : 0 < y) (q : CuspCoset) :
    ContinuousOn (cuspOrbitFourierTerm J s z y hy q) (Icc (0 : ℝ) 1) := by
  apply (contDiff_cuspFourierMode J).continuous.continuousOn.mul
  apply continuousOn_tsum
    (fun n => ((continuous_pointKernel_left s
      (ModularGroup.T ^ n • (q.out • z))).comp (continuous_rowPoint y hy)).continuousOn)
    ((summable_norm_cuspOrbit_horizontal s hs z y hy q 0).mul_left
      ((2 + 2 / y ^ 2) ^ s.re))
  exact fun n x hx => cuspOrbit_horizontal_norm_le s hs z y hy q n x hx

theorem exists_cuspOrbitFourierTerm_majorant (J : ℤ) (s : ℂ) (hs : 1 < s.re)
    (z : UpperHalfPlane) (y : ℝ) (hy : 0 < y) :
    ∃ u : CuspCoset → ℝ, Summable u ∧ (∀ q, 0 ≤ u q) ∧
      ∀ q x, x ∈ Icc (0 : ℝ) 1 → ‖cuspOrbitFourierTerm J s z y hy q x‖ ≤ u q := by
  let C : ℝ := (2 + 2 / y ^ 2) ^ s.re
  let u : CuspCoset → ℝ := fun q => C * ∑' n : ℤ,
    ‖pointKernel s (rowPoint y hy 0) (ModularGroup.T ^ n • (q.out • z) : UpperHalfPlane)‖
  have hsum : Summable (fun q : CuspCoset => ∑' n : ℤ,
      ‖pointKernel s (rowPoint y hy 0) (ModularGroup.T ^ n • (q.out • z) : UpperHalfPlane)‖) := by
    apply (summable_cuspOrbit_tsum_norm s hs z (rowPoint y hy 0)).congr
    intro q
    exact tsum_congr fun n => congrArg norm (pointKernel_symm s
      (ModularGroup.T ^ n • (q.out • z) : UpperHalfPlane) (rowPoint y hy 0))
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨u, hsum.mul_left C, fun q => mul_nonneg hC (tsum_nonneg (fun _ => norm_nonneg _)), ?_⟩
  intro q x hx
  rw [cuspOrbitFourierTerm, norm_mul, norm_cuspFourierMode, one_mul]
  calc
    _ ≤ ∑' n : ℤ,
        ‖pointKernel s (rowPoint y hy x) (ModularGroup.T ^ n • (q.out • z) : UpperHalfPlane)‖ :=
      norm_tsum_le_tsum_norm (summable_norm_cuspOrbit_horizontal s hs z y hy q x)
    _ ≤ ∑' n : ℤ, C *
        ‖pointKernel s (rowPoint y hy 0) (ModularGroup.T ^ n • (q.out • z) : UpperHalfPlane)‖ :=
      (summable_norm_cuspOrbit_horizontal s hs z y hy q x).tsum_le_tsum
        (fun n => cuspOrbit_horizontal_norm_le s hs z y hy q n x hx)
        ((summable_norm_cuspOrbit_horizontal s hs z y hy q 0).mul_left C)
    _ = u q := tsum_mul_left

theorem summable_integral_norm_cuspOrbitFourierTerm (J : ℤ) (s : ℂ) (hs : 1 < s.re)
    (z : UpperHalfPlane) (y : ℝ) (hy : 0 < y) :
    Summable (fun q : CuspCoset =>
      ∫ x in (0 : ℝ)..1, ‖cuspOrbitFourierTerm J s z y hy q x‖) := by
  obtain ⟨u, hu, hu0, hbound⟩ := exists_cuspOrbitFourierTerm_majorant J s hs z y hy
  apply hu.of_nonneg_of_le
  · intro q
    exact intervalIntegral.integral_nonneg_of_forall zero_le_one (fun x => norm_nonneg _)
  · intro q
    have hfi : IntervalIntegrable (cuspOrbitFourierTerm J s z y hy q) volume 0 1 :=
      (continuousOn_cuspOrbitFourierTerm J s hs z y hy q).intervalIntegrable_of_Icc
        zero_le_one
    have h := intervalIntegral.integral_mono_on zero_le_one
      hfi.norm (intervalIntegrable_const (c := u q)) (hbound q)
    simpa using h

theorem hasSum_integral_cuspOrbitFourierTerm (J : ℤ) (s : ℂ) (hs : 1 < s.re)
    (z : UpperHalfPlane) (y : ℝ) (hy : 0 < y) :
    HasSum (fun q : CuspCoset => ∫ x in (0 : ℝ)..1, cuspOrbitFourierTerm J s z y hy q x)
      (∫ x in (0 : ℝ)..1, cuspFourierMode J x * spatialOrbitKernel s z (rowPoint y hy x)) := by
  let : Countable CuspCoset := cuspBottomRow_injective.countable
  have hint : ∀ q, Integrable (cuspOrbitFourierTerm J s z y hy q)
      (volume.restrict (Ioc (0 : ℝ) 1)) := fun q =>
    ((continuousOn_cuspOrbitFourierTerm J s hs z y hy q).intervalIntegrable_of_Icc
      zero_le_one).1
  have hsum : Summable (fun q : CuspCoset =>
      ∫ x in Ioc (0 : ℝ) 1, ‖cuspOrbitFourierTerm J s z y hy q x‖) := by
    simpa only [intervalIntegral.integral_of_le zero_le_one] using
      summable_integral_norm_cuspOrbitFourierTerm J s hs z y hy
  have h := MeasureTheory.hasSum_integral_of_summable_integral_norm hint hsum
  have heq : (fun x => ∑' q, cuspOrbitFourierTerm J s z y hy q x) =
      (fun x => cuspFourierMode J x * spatialOrbitKernel s z (rowPoint y hy x)) :=
    funext fun x => (hasSum_cuspOrbitFourierTerm J s hs z y hy x).tsum_eq
  simpa only [intervalIntegral.integral_of_le zero_le_one, heq] using h

theorem integral_cuspOrbitFourierTerm_eq_unfold (J : ℤ) (s : ℂ) (hs : 1 < s.re)
    (z : UpperHalfPlane) (y : ℝ) (hy : 0 < y) (q : CuspCoset) :
    (∫ x in (0 : ℝ)..1, cuspOrbitFourierTerm J s z y hy q x) =
      ∫ x : ℝ, cuspFourierMode J x * pointKernel s (rowPoint y hy x) (q.out • z : UpperHalfPlane) := by
  calc
    _ = ∫ x in (0 : ℝ)..1, cuspFourierMode J x * ∑' n : ℤ,
        pointKernel s (ModularGroup.T ^ n • (q.out • z) : UpperHalfPlane) (rowPoint y hy x) := by
      apply intervalIntegral.integral_congr
      intro x _
      unfold cuspOrbitFourierTerm
      congr 1
      exact tsum_congr fun n => pointKernel_symm s (rowPoint y hy x)
        (ModularGroup.T ^ n • (q.out • z) : UpperHalfPlane)
    _ = _ := pointKernel_translation_source_fourier_integral s hs (q.out • z) y hy J

/-- The actual orbit Fourier coefficient unfolds into the cusp sum of ordinary
real-line point-kernel Fourier transforms. Both interchanges use proved absolute convergence. -/
theorem spatialOrbitKernel_fourier_unfold (J : ℤ) (s : ℂ) (hs : 1 < s.re)
    (z : UpperHalfPlane) (y : ℝ) (hy : 0 < y) :
    (∫ x in (0 : ℝ)..1, cuspFourierMode J x * spatialOrbitKernel s z (rowPoint y hy x)) =
      ∑' q : CuspCoset, ∫ x : ℝ,
        cuspFourierMode J x * pointKernel s (rowPoint y hy x) (q.out • z : UpperHalfPlane) := by
  rw [← (hasSum_integral_cuspOrbitFourierTerm J s hs z y hy).tsum_eq]
  exact tsum_congr fun q => integral_cuspOrbitFourierTerm_eq_unfold J s hs z y hy q

end GapFamily.Analytic.SpatialPoint
