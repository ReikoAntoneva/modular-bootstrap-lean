import GapFamily.Analytic.Poincare.Threshold.PoincareThresholdH1
import GapFamily.Analytic.Poincare.Seed.PoincareSeriesSmooth
import GapFamily.Analytic.Poincare.Threshold.PoincareThresholdSourceCutoff

/-!
The actual Euclidean source of the canonical threshold equation has a genuine
local H1 witness. Only the already constructed H1 value of the threshold seed
is used; the inverse-height multiplier and shifted-series source are constructed
from ordinary smooth compact functions.
-/

noncomputable section
namespace GapFamily.Analytic.PoincareThresholdSourceH1

open Set Filter MeasureTheory UpperHalfPlane Homogenization
  PoincareCanonical PoincareThresholdSourceCutoff
open scoped ContDiff Topology

/-- The genuine shifted zero-energy Poincaré series in the threshold equation. -/
def shiftedThresholdSource (J : ℤ) (w : ℂ) : ℂ :=
  (2 * (Real.pi : ℂ) * (J : ℂ)) ^ 2 *
    complexPoincareSeries 0 J (5 / 2 : ℂ) (ofComplex w)

/-- The literal ordinary source, including its inverse-height coefficient. -/
def thresholdSource (J : ℤ) (w : ℂ) : ℂ :=
  ((1 / 4 : ℂ) * thresholdSeed J (ofComplex w) + shiftedThresholdSource J w) /
    (w.im : ℂ) ^ 2

theorem contDiffOn_shiftedThresholdSource (J : ℤ) :
    ContDiffOn ℝ ∞ (shiftedThresholdSource J) upperHalfPlaneSet :=
  contDiffOn_const.mul
    (PoincareSeriesSmooth.contDiffOn_complexPoincareSeries J (by norm_num))

/-- All coefficients are real, so any real-linear projection has the same scalar source. -/
theorem thresholdSource_projection (J : ℤ) (L : ℂ →L[ℝ] ℝ) (w : ℂ) :
    L (thresholdSource J w) =
      (1 / 4 : ℝ) * ((1 / w.im ^ 2) * L (thresholdSeed J (ofComplex w))) +
        (1 / w.im ^ 2) * L (shiftedThresholdSource J w) := by
  have he : thresholdSource J w =
      (1 / w.im ^ 2 : ℝ) •
        ((1 / 4 : ℝ) • thresholdSeed J (ofComplex w) + shiftedThresholdSource J w) := by
    unfold thresholdSource
    simp only [Complex.real_smul, Complex.ofReal_div, Complex.ofReal_one,
      Complex.ofReal_pow, Complex.ofReal_ofNat]
    ring
  rw [he, map_smul, map_add, map_smul]
  simp only [smul_eq_mul]
  ring

/-- The shifted forcing localized by the actual real inverse-height multiplier. -/
def localizedShiftedSource (J : ℤ) (L : ℂ →L[ℝ] ℝ) (m : ℂ → ℝ) (w : ℂ) : ℝ :=
  m w * L (shiftedThresholdSource J w)

theorem contDiff_localizedShiftedSource (J : ℤ) (L : ℂ →L[ℝ] ℝ)
    (m : ℂ → ℝ) (hm : ContDiff ℝ ∞ m) (hs : tsupport m ⊆ upperHalfPlaneSet) :
    ContDiff ℝ ∞ (localizedShiftedSource J L m) := by
  rw [contDiff_iff_contDiffAt]
  intro w
  by_cases hw : w ∈ upperHalfPlaneSet
  · exact hm.contDiffAt.mul (L.contDiff.contDiffAt.comp w
      ((contDiffOn_shiftedThresholdSource J).contDiffAt
        (isOpen_upperHalfPlaneSet.mem_nhds hw)))
  · have hwm : w ∉ tsupport m := fun h => hw (hs h)
    have hzero : localizedShiftedSource J L m =ᶠ[𝓝 w] (fun _ => 0) := by
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hwm] with x hx
      simp only [localizedShiftedSource, hx, zero_mul, Pi.zero_apply]
    exact contDiffAt_const.congr_of_eventuallyEq hzero

theorem hasCompactSupport_localizedShiftedSource (J : ℤ) (L : ℂ →L[ℝ] ℝ)
    (m : ℂ → ℝ) (hm : HasCompactSupport m) :
    HasCompactSupport (localizedShiftedSource J L m) := hm.mul_right

/-- The ordinary smooth shifted forcing gives an actual H1 chart function. -/
def shiftedSourceChartH1 (J : ℤ) (L : ℂ →L[ℝ] ℝ)
    (m : ℂ → ℝ) (hm : ContDiff ℝ ∞ m) (hc : HasCompactSupport m)
    (hs : tsupport m ⊆ upperHalfPlaneSet) (z : ℂ)
    (S : Set (Fin 2 → ℝ)) (hS : IsOpen S) : H1Function S :=
  H1Function.ofContDiff hS
    (((contDiff_localizedShiftedSource J L m hm hs).comp
      (ellipticChart_contDiff z)).of_le (by simp))
    ((hasCompactSupport_localizedShiftedSource J L m hc).comp_homeomorph (ellipticChart z))

/-- The actual H1 source uses the exact H1 multiplier construction and its
Leibniz weak gradient, together with the genuine smooth shifted forcing. -/
def thresholdSourceChartH1 (J : ℤ) (L : ℂ →L[ℝ] ℝ)
    (m : ℂ → ℝ) (hm : ContDiff ℝ ∞ m) (hc : HasCompactSupport m)
    (hs : tsupport m ⊆ upperHalfPlaneSet) (z : ℂ)
    (S : Set (Fin 2 → ℝ)) (hS : IsOpen S) (u : H1Function S) : H1Function S :=
  (1 / 4 : ℝ) • u.mulContDiffHasCompactSupport
    (hm.comp (ellipticChart_contDiff z)) (hc.comp_homeomorph (ellipticChart z)) +
    shiftedSourceChartH1 J L m hm hc hs z S hS

theorem thresholdSourceChartH1_value_ae (J : ℤ) (L : ℂ →L[ℝ] ℝ)
    (m : ℂ → ℝ) (hm : ContDiff ℝ ∞ m) (hc : HasCompactSupport m)
    (hs : tsupport m ⊆ upperHalfPlaneSet) (z : ℂ)
    (S : Set (Fin 2 → ℝ)) (hS : IsOpen S) (u : H1Function S)
    (hu : u.toFun =ᵐ[volume.restrict S]
      (fun v => L (thresholdSeed J (ofComplex (ellipticChart z v)))))
    (hEq : EqOn m (fun w => 1 / w.im ^ 2) (ellipticChart z '' S)) :
    (thresholdSourceChartH1 J L m hm hc hs z S hS u).toFun =ᵐ[volume.restrict S]
      (fun v => L (thresholdSource J (ellipticChart z v))) := by
  filter_upwards [hu, ae_restrict_mem hS.measurableSet] with v hv hvS
  change (1 / 4 : ℝ) * (m (ellipticChart z v) * u.toFun v) +
    m (ellipticChart z v) * L (shiftedThresholdSource J (ellipticChart z v)) = _
  rw [hv, hEq (mem_image_of_mem _ hvS), thresholdSource_projection]

/-- On every relatively compact positive-height chart domain, an actual H1
representative of the threshold value produces an actual H1 representative of
its prescribed source. The multiplier and shifted forcing are constructed here. -/
theorem exists_thresholdSource_chartH1 (J : ℤ) (L : ℂ →L[ℝ] ℝ)
    (z : ℂ) (S : Set (Fin 2 → ℝ)) (hS : IsOpen S)
    (hSc : IsCompact (closure S))
    (hSH : ellipticChart z '' closure S ⊆ upperHalfPlaneSet)
    (u : H1Function S)
    (hu : u.toFun =ᵐ[volume.restrict S]
      (fun v => L (thresholdSeed J (ofComplex (ellipticChart z v))))) :
    ∃ g : H1Function S, g.toFun =ᵐ[volume.restrict S]
      (fun v => L (thresholdSource J (ellipticChart z v))) := by
  obtain ⟨m, hm, hc, hs, he⟩ :=
    exists_inverseHeightCutoff (hSc.image (ellipticChart z).continuous) hSH
  refine ⟨thresholdSourceChartH1 J L m hm hc hs z S hS u, ?_⟩
  apply thresholdSourceChartH1_value_ae J L m hm hc hs z S hS u hu
  exact he.mono (image_mono subset_closure)

end GapFamily.Analytic.PoincareThresholdSourceH1
