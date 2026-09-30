import GapFamily.Analytic.Poincare.PoincareAnalytic
import GapFamily.Analytic.Cusp.Fourier.CuspFourierProfileCore
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Ordinary horizontal Fourier integrals of the actual convergent Poincaré series. -/

noncomputable section
namespace GapFamily.Analytic.PoincareFourier

open Set MeasureTheory UpperHalfPlane
open scoped Topology MatrixGroups

def rowPoint (y : ℝ) (hy : 0 < y) (x : ℝ) : UpperHalfPlane :=
  ⟨Complex.mk x y, hy⟩

def fourierTerm (j J : ℤ) (s : ℂ) (y : ℝ) (hy : 0 < y)
    (q : CuspCoset) (x : ℝ) : ℂ :=
  cuspFourierMode (-j) x * complexPoincareTerm 0 J s (rowPoint y hy x) q

def fourierSeries (j J : ℤ) (s : ℂ) (y : ℝ) (hy : 0 < y) (x : ℝ) : ℂ :=
  cuspFourierMode (-j) x * complexPoincareSeries 0 J s (rowPoint y hy x)

theorem continuous_rowPoint (y : ℝ) (hy : 0 < y) : Continuous (rowPoint y hy) := by
  apply UpperHalfPlane.isEmbedding_coe.continuous_iff.mpr
  change Continuous (fun x : ℝ => Complex.mk x y)
  convert Complex.continuous_ofReal.add
    (continuous_const (y := (y : ℂ) * Complex.I)) using 1
  funext x
  apply Complex.ext <;> simp

private theorem continuous_zeroEnergySeed (J : ℤ) (s : ℂ) :
    Continuous (complexPointSeed 0 J s) := by
  have hi : Continuous (fun τ : UpperHalfPlane => (τ.im : ℂ)) :=
    Complex.continuous_ofReal.comp UpperHalfPlane.continuous_im
  have hp : Continuous (fun τ : UpperHalfPlane => (τ.im : ℂ) ^ s) :=
    hi.cpow continuous_const (fun τ => Or.inl τ.im_pos)
  have hphase : Continuous (fun τ : UpperHalfPlane =>
      Complex.exp (((2 * Real.pi * (J : ℝ) * τ.re : ℝ) : ℂ) * Complex.I)) := by
    fun_prop
  convert hp.mul hphase using 1
  ext τ
  simp [complexPointSeed]

theorem continuous_fourierTerm (j J : ℤ) (s : ℂ) (y : ℝ) (hy : 0 < y)
    (q : CuspCoset) : Continuous (fourierTerm j J s y hy q) := by
  have hact : Continuous (fun τ : UpperHalfPlane => q.out • τ) := by
    change Continuous (fun τ : UpperHalfPlane => Matrix.SpecialLinearGroup.mapGL ℝ q.out • τ)
    exact continuous_const_smul _
  change Continuous (fun x => cuspFourierMode (-j) x *
    complexPoincareTerm 0 J s (rowPoint y hy x) q)
  simp only [complexPoincareTerm_out]
  exact (contDiff_cuspFourierMode (-j)).continuous.mul
    ((continuous_zeroEnergySeed J s).comp (hact.comp (continuous_rowPoint y hy)))

theorem norm_fourierTerm (j J : ℤ) (s : ℂ) (y : ℝ) (hy : 0 < y)
    (q : CuspCoset) (x : ℝ) :
    ‖fourierTerm j J s y hy q x‖ = (q.out • rowPoint y hy x).im ^ s.re := by
  simp [fourierTerm, norm_cuspFourierMode, complexPoincareTerm_out,
    norm_complexPointSeed]

theorem exists_fourierTerm_majorant (j J : ℤ) {s : ℂ} (hs : 1 < s.re)
    (y : ℝ) (hy : 0 < y) :
    ∃ u : CuspCoset → ℝ, Summable u ∧ (∀ q, 0 ≤ u q) ∧
      ∀ q x, x ∈ Icc (0 : ℝ) 1 → ‖fourierTerm j J s y hy q x‖ ≤ u q := by
  have hK : IsCompact (rowPoint y hy '' Icc (0 : ℝ) 1) :=
    isCompact_Icc.image (continuous_rowPoint y hy)
  obtain ⟨M, hM, u, hu, hu0, hbound⟩ := exists_cusp_height_compact_majorant hK hs
  refine ⟨u, hu, hu0, ?_⟩
  intro q x hx
  rw [norm_fourierTerm]
  exact (hbound q (rowPoint y hy x) ⟨x, hx, rfl⟩).2

theorem hasSum_fourierTerm (j J : ℤ) {s : ℂ} (hs : 1 < s.re)
    (y : ℝ) (hy : 0 < y) (x : ℝ) :
    HasSum (fun q => fourierTerm j J s y hy q x) (fourierSeries j J s y hy x) :=
  (hasSum_complexPoincareTerm 0 J hs (rowPoint y hy x)).mul_left (cuspFourierMode (-j) x)

theorem intervalIntegrable_fourierTerm (j J : ℤ) (s : ℂ) (y : ℝ) (hy : 0 < y)
    (q : CuspCoset) : IntervalIntegrable (fourierTerm j J s y hy q) volume 0 1 :=
  (continuous_fourierTerm j J s y hy q).intervalIntegrable 0 1

theorem intervalIntegrable_fourierSeries (j J : ℤ) {s : ℂ} (hs : 1 < s.re)
    (y : ℝ) (hy : 0 < y) :
    IntervalIntegrable (fourierSeries j J s y hy) volume 0 1 := by
  obtain ⟨u, hu, hu0, hbound⟩ := exists_fourierTerm_majorant j J hs y hy
  have hc : ContinuousOn (fun x => ∑' q, fourierTerm j J s y hy q x) (Icc 0 1) :=
    continuousOn_tsum (fun q => (continuous_fourierTerm j J s y hy q).continuousOn) hu hbound
  have heq : (fun x => ∑' q, fourierTerm j J s y hy q x) = fourierSeries j J s y hy :=
    funext fun x => (hasSum_fourierTerm j J hs y hy x).tsum_eq
  rw [heq] at hc
  exact hc.intervalIntegrable_of_Icc zero_le_one

theorem summable_integral_norm_fourierTerm (j J : ℤ) {s : ℂ} (hs : 1 < s.re)
    (y : ℝ) (hy : 0 < y) :
    Summable (fun q : CuspCoset => ∫ x in (0 : ℝ)..1, ‖fourierTerm j J s y hy q x‖) := by
  obtain ⟨u, hu, hu0, hbound⟩ := exists_fourierTerm_majorant j J hs y hy
  apply hu.of_nonneg_of_le
  · intro q
    exact intervalIntegral.integral_nonneg_of_forall zero_le_one (fun x => norm_nonneg _)
  · intro q
    have h := intervalIntegral.integral_mono_on zero_le_one
      (intervalIntegrable_fourierTerm j J s y hy q).norm
      (intervalIntegrable_const (c := u q)) (hbound q)
    simpa using h

theorem hasSum_integral_fourierTerm (j J : ℤ) {s : ℂ} (hs : 1 < s.re)
    (y : ℝ) (hy : 0 < y) :
    HasSum (fun q : CuspCoset => ∫ x in (0 : ℝ)..1, fourierTerm j J s y hy q x)
      (∫ x in (0 : ℝ)..1, fourierSeries j J s y hy x) := by
  let : Countable CuspCoset := cuspBottomRow_injective.countable
  have hint : ∀ q, Integrable (fourierTerm j J s y hy q)
      (volume.restrict (Ioc (0 : ℝ) 1)) :=
    fun q => (intervalIntegrable_fourierTerm j J s y hy q).1
  have hsum : Summable (fun q : CuspCoset =>
      ∫ x in Ioc (0 : ℝ) 1, ‖fourierTerm j J s y hy q x‖) := by
    simpa only [intervalIntegral.integral_of_le zero_le_one] using
      summable_integral_norm_fourierTerm j J hs y hy
  have h := MeasureTheory.hasSum_integral_of_summable_integral_norm hint hsum
  have heq : (fun x => ∑' q, fourierTerm j J s y hy q x) = fourierSeries j J s y hy :=
    funext fun x => (hasSum_fourierTerm j J hs y hy x).tsum_eq
  simpa only [intervalIntegral.integral_of_le zero_le_one, heq] using h

theorem integral_fourierSeries_eq_tsum (j J : ℤ) {s : ℂ} (hs : 1 < s.re)
    (y : ℝ) (hy : 0 < y) :
    (∫ x in (0 : ℝ)..1, fourierSeries j J s y hy x) =
      ∑' q : CuspCoset, ∫ x in (0 : ℝ)..1, fourierTerm j J s y hy q x :=
  (hasSum_integral_fourierTerm j J hs y hy).tsum_eq.symm

end GapFamily.Analytic.PoincareFourier
